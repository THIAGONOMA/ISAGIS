import io
import os
import re
from google.cloud import vision
from google.cloud.vision import types
from unicodedata import normalize
from pdf2image import convert_from_path, convert_from_bytes
from PIL import Image as IMage
import json
import time
import hashlib
os.environ["GOOGLE_APPLICATION_CREDENTIALS"]="<path from your key>"

#global variables
mensageDict, tokenWords={}, []

states={'ACRE':'AC', 'ALAGOAS':'AL','AMAPÁ':'AP','AMAZONAS':'AM','BAHIA':'BA','CEARÁ':'CE','DISTRITO FEDERAL':'DF','ESPÍRITO SANTO':'ES','GOIÁS':'GO',
        'MARANHÃO':'MA','MATO GROSSO DO SUL':'MS','MATO GROSSO':'MT','MINAS GERAIS':'MG','PARÁ':'PA','PARAÍBA':'PB','PARANÁ':'PR','PERNAMBUCO':'PE','PIAUÍ':'PI',
        'RIO DE JANEIRO':'RJ','RIO GRANDE DO SUL':'RS','RIO GRANDE DO NORTE':'RN','RONDÔNIA':'RO','RORAIMA':'RR','SANTA CATARINA':'SC','SÃO PAULO':'SP','SERGIPE':'SE','TOCANTINS':'TO'}

states2={'AC':'AC(I|R|E)E', 'AL':'ALA(G|O)OAS', 'AP':'AMAP(Á|A)', 'AM':'AMAZONAS', 'BA':'BAHIA', 'CE':'CEA(R|I)(Á|A)', 'DF':'DISTRITO FEDERAL', 'ES':'ESP(Í|I)(R|I)ITO SANTO', 'GO':'GOI(Á|A)S',
         'MA':'MARANH(Ã|A)O', 'MS':'MATO GROSSO DO SUL', 'MT':'MATO GROSSO', 'MG':'MINAS GERAIS', 'PA':'PA(R|I)(Á|A)', 'PB':'PARA(Í|I)BA', 'PR':'PARAN(Á|A)', 'PE':'PERNAMBUCO', 'PI':'PIAU(Í|I)',
         'RJ':'RIO DE JANEIRO', 'RS':'RIO GRANDE DO SUL', 'RN':'RIO GRANDE DO NORTE', 'RO':'RONDÔNIA', 'RR':'RORAIMA', 'SC':'SANTA CATARINA', 'SP':'S(Ã|A)O PAULO', 'SE':'SERGIPE', 'TO':'TOCANTINS'}

MONTH={'JANEIRO':'01','FEVEREIRO':'02','MARÇO':'03','ABRIL':'04','MAIO':'05','JUNHO':'06',
       'JULHO':'07','AGOSTO':'08','SETEMBRO':'09','OUTUBRO':'10','NOVEMBRO':'11','DEZEMBRO':'12'}

patterns={'POLCIV':'(((D|d)elegado|DELEGADO) (de|DE) ((P|p)olícia|POLICIA)|POL(I|Í)CIA (|JUDICI(Á|A)RIA)|CIV(Í|I)L)|((P|p)olic(i|í)a (|(J|j)udici(a|á)ria)|(C|c)iv(i|í)l)',
          'POLDE':'(POL(I|Í)CIA)(| CIV(Í|I)L)( DO ESTADO| D(E|O|OS|A)) .+?(\,|\.|\r|\;|\n)',
          'POLSUB':'(.+|)(POL(I|Í)CIA)(( CIV(Í|I)L)|)( DO ESTADO (DE|DO)| D(E|A|O))',
          'COMMON':'(\,|\r|\.|\;|\n)', 'NAME':'([A-Z])([A-Z]+|[a-z]+) ([A-Z])([A-Z]+|[a-z]+)( |)(([A-Z])([A-Z]+|[a-z]+)|)',
          'UFFULL':'([A-Z])([A-Z]|[a-z])+?(/|-)([A-Z][A-Z])( |\.|\;|\r)','COMAUX':'(\-| \-|\/| \/)( |)([A-Z][A-Z]|[a-z][a-z])( |\.|\n|\;)',
          'DOFY':'([0-9][0-9]) (de) (([A-Z]|[a-z])(([A-Z]|[a-z])+)) (de) ([0-9][0-9][0-9][0-9])', 'PODJUD':'(P|p)oder Judici(á|a)rio|PODER JUDICI(Á|A)RIO',
          'DATECOM':r'(([A-Z]|[a-z])(([A-Z]|[a-z])+)(|.+)(| )(|\-|\/|\,)(| )(|[A-Z][A-Z]))(|\,) ([0-9][0-9]) (|de) (([A-Z]|[a-z])(([A-Z]|[a-z])+)) (|de) ([0-9][0-9][0-9][0-9])'}

adress={'ALAMEDA':'(ALAMEDA|(A|a)lameda|(A|a)(L|l)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'AVENIDA':'(AVENIDA|(A|a)venida|(A|a)(V|v)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])',
        'BECO':'(BECO|(B|b)eco|(B|b)(E|e|)(|\.)) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'BOULEVARD':'(BOULEVARD|(B|b)oulevard|(B|b)(O|o)(\.|L|l)(|\.)) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])',
        'ESTRADA':'(ESTRADA|(E|e)strada|(E|e)(STR|str)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'FAZENDA':'(FAZENDA|(F|f)azenda|(F|f)(AZ|az)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])',
        'LADEIRA':'(LADEIRA|(L|l)adeira|(L|l)(AD|ad)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'LARGO':'(LARGO|(L|l)argo|(L|l)(\.|GO|go)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])',
        'LOTEAMENTO':'(LOTEAMENTO|(L|l)oteamento|(L|l)(OTE|ote)|(L|l)(OT|ot)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])',
        'PRAIA':'(PRAIA|(P|p)raia|(P|p)(R|r)(\.|a\.|A\.)) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'PRAÇA':'(PRA(Ç|C)A|(P|p)ra(ç|c)a|((P|p)(RÇ|rç|RC|rc)(\.|))) .+?(\/|\-)(| )([A-Z][A-Z])',
        'RODOVIA':'(RODOVIA|(R|r)odovia|(R|r)(OD|od)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'RUA':'(RUA|(R|r)ua|(R|r)\.) ([A-Z]|[a-z]).+?(\/|\-|\-|\/)(| )([A-Z][A-Z])',
        'TRAVESSA':'(TRAVESSA|(T|t)ravessa|(T|t)(RA|ra)\.) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])',
        'VIA':'(VIA|(V|v)ia) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])', 'VIELA':'(VIELA|(V|v)iela|((V|v)LA|la)) ([A-Z]|[a-z]).+?(\/|\-)(| )([A-Z][A-Z])'}

fullSearAdress={'AVENIDA':'(AVENIDA|(A|a)venida|(A|a)(V|v)\.).+', 'RUA':'(RUA|(R|r)ua|(R|r)\.).+', 'ESTRADA':'(ESTRADA|(E|e)strada|(E|e)(STR|str)\.).+', 'RODOVIA':'(RODOVIA|(R|r)odovia|(R|r)(OD|od)\.).+'}

typesSear={'OFI':'(((O|o)f(i|í)c(io|ie|e))|(OF(I|Í)C(IO|E))|(OF\.|Of\.|of\.)).+', 'PROC':'(PROCESSO|PROCEDIMENT(O|OS)|(P|p)rocediment(o|os)|(p|P)rocesso|(P|p)roc\.|PROC\.).+',
           'INQ':'(((I|i)nqu(é|e)rito)|INQU(É|E)RITO|(IP|(I|i)(nq|NQ))( |\.)).+',
           'BO':'((B|b)(|\.)(O|o)( |\.|\:|\-)|REDS|(R|r)eds|(B|b)oletim de (O|o)corr(ê|e)ncia|noticia(s|) crim(inais|e)|NOTICI(A|AS) CRIM(INAIS|E)|BOLETIM DE OCORR(Ê|E)NCIA|RDO|(R|r)(DO|do)( |\.|\:|\-)|Procedimento( |\.|\:|\-)).+',
           'DEPTPOL':'(([0-9][0-9][0-9]|[0-9][0-9]|[0-9]|)(.+|)( |)(((S|s)uper|)((G|g)er|intend)(ê|e)ncia|(D|d)iretoria|(D|d)ivis(ã|a)o|(S|s)ub(\-|)divis(ã|a)o|(D|d)epartamento|(D|d)pto\.)( |)((D|d)(E|e|O|o|A|a)|)( |)((I|i)ntelig(ê|e)ncia|)( |)((P|p)ol(í|i)ci(amento|al|a)|)(((D|d)(E|e|O|o|A|a)|)( |)((R|r)epress(ã|a)o|(P|p)rote(ç|c)(ã|a)o)|)( |)(ao|(D|d)(E|e|O|o|A|a)|)(.+))|(([0-9][0-9][0-9]|[0-9][0-9]|[0-9]|)(.+|)( |)(((S|S)UPER|)((G|G)ER|INTEND)(Ê|E)NCIA|(D|D)IRETORIA|(D|D)IVIS(Ã|A)O|(S|S)UB(\-|)DIVIS(Ã|A)O|(D|D)EPARTAMENTO|(D|D)PTO\.)( |)((D|D)(E|E|O|O|A|A)|)( |)((I|I)NTELIG(Ê|E)NCIA|)( |)((P|P)OL(Í|I)CI(AMENTO|AL|A)|)(((D|D)(E|E|O|O|A|A)|)( |)((R|R)EPRESS(Ã|A)O|(P|P)ROTE(Ç|C)(Ã|A)O)|)( |)(AO|(D|D)(E|E|O|O|A|A)|)(.+))',
           'DELTIP':'([0-9][0-9]|[0-9]|[0-9](\ª|a|\º|o|)|[0-9][0-9](\ª|a|\º|o|)|([A-Z]+)|([a-z]+)|)(\.|)(| |)(DELEGACIA|(D|d)elegacia|DISTRITO|(D|d)iatrito|(D|d)(|\.)(P|p))(|\.).+',
           'PRAZO':'(((P|p)razo)( |)(|.+)((\:|\-)|((D|d)e))( |)(\:|\-|)( |)(([0-9][0-9][0-9]|[0-9][0-9]|[0-9]|([a-z]+) e ([a-z]+) e ([a-z]+)|([a-z]+) e ([a-z]+)|([a-z]+))( |)(\(([A-Z]|[a-z]).+\)|)|([A-Z].+))( |)((D|d)ia(s|m|)|(H|h)oras|(M|m)es(es|)|(H|h)|(hrs|Hrs|HRS)|(A|a)no(s|))|(((P|P)RAZO)( |)(|.+)((\:|\-)|((D|D)E))( |)(\:|\-|)( |)(([0-9][0-9][0-9]|[0-9][0-9]|[0-9]|([A-Z]+) E ([A-Z]+) E ([A-Z]+)|([A-Z]+) E ([A-Z]+)|([A-Z]+))( |)(\(([A-Z]|[A-Z]).+\)|)|([A-Z].+))( |)((D|D)IA(S|M|)|(H|H)ORAS|(M|M)ES(ES)|(A|A)NO(S|))))',
           'DESCR':'(((N|n)ão) ((A|a)tendimento|(C|c)umprimento|(F|f)ornecimento)|((D|d)escumprimento)|(R|r)ecusa|(O|o)miss(ã|a)o|(atendimento do que ora|(R|r)e(tin|nit)(ê|e)ncia|(M|m)orisidade|(D|d)e(mora|longa))).+|(((N|N)ÃO) ((A|A)TENDIMENTO|(C|C)UMPRIMENTO|(F|F)ORNECIMENTO)|(ATENDIMENTO DO QUE ORA REQUISITA|(D|D)ESCUMPRIMENTO)|(R|R)ECUSA|(O|O)MISS(Ã|A)O|((R|R)E(TIN|NIT)(Ê|E)NCIA|(M|M)ORISIDADE|(D|D)E(MORA|LONGA))).+'}

typesSub={'OFI':'(((O|o)f(i|í)c(io|ie|e))|(OF(I|Í)C(IO|E))|(OF\.|Of\.|of\.)).+?([0-9]).+', 'PROC':'(PROCESS(O|OS)|PROCEDIMENT(O|OS)|(P|p)rocediment(o|os)|(P|p)rocess(o|os)|(P|p)roc\.|PROC\.).+?([0-9]).+',
           'INQ':'(((I|i)nqu(é|e)rito)|INQU(É|E)RITO|(IP|(I|i)(nq|NQ))( |\.)).+?([0-9]).+',
           'BO':'((B|b)(|\.)(O|o)( |\.|\:|\-)|REDS|(R|r)eds|(B|b)oletim de (O|o)corr(ê|e)ncia|noticia(s|) crim(inais|e)|NOTICI(A|AS) CRIM(INAIS|E)|BOLETIM DE OCORR(Ê|E)NCIA|RDO|(R|r)(DO|do)( |\.|\:|\-)|Procedimento( |\.|\:|\-)).+?([0-9]).+',
           'PRAZO':'((([0-9][0-9][0-9]|[0-9][0-9]|[0-9]|([a-z]+) e ([a-z]+) e ([a-z]+)|([a-z]+) e ([a-z]+)|([a-z]+))( |)(\(([A-Z]|[a-z]).+\)|)|([A-Z]+))( |)((D|d)ia(s|m)|(H|h)oras|(H|h)|(hrs|Hrs|HRS)|(M|m)ese(s|)|(A|a)no(s|)))|((([0-9][0-9][0-9]|[0-9][0-9]|[0-9]|([A-Z]+) E ([A-Z]+) E ([A-Z]+)|([A-Z]+) E ([A-Z]+)|([A-Z]+))( |)(\(([A-Z]|[A-Z]).+\)|)|([A-Z]+))( |)((D|D)IA(S|)|(H|H)ORAS|(M|M)ES(ES|)|(A|A)NO(S|)))'}

pattClass={'REITERACAO':'((R|r)eiter(o|a|á|e)(vamos|sseis|ssemos|ssem|ramos|ssemos|remos|ríamos|ríeis|riam|reis|rmos|rdes|sses|veis|stes|rias|vam|sse|ste|mos|vas|ram|r(ã|a)o|r(a|á)s|rem|res|rei|ria|r(a|á)|va|is|i|m|v|u|r|s|))|((REITER(O|A|Á|E)(VAMOS|SSEIS|SSEMOS|SSEM|RAMOS|SSEMOS|REMOS|RÍAMOS|RÍEIS|RIAM|REIS|RMOS|RDES|SSES|VEIS|STES|RIAS|VAM|SSE|STE|MOS|VAS|RAM|R(Ã|A)O|R(A|Á)S|REM|RES|REI|RIA|R(A|Á)|VA|IS|I|M|V|U|R|S|)))',
           'RETIFICACAO':'((R|r)etifi(c(o|a|á|e)|que)(vamos|sseis|ssemos|ssem|ramos|ssemos|remos|ríamos|ríeis|riam|reis|rmos|rdes|sses|veis|stes|rias|vam|sse|ste|mos|vas|ram|r(ã|a)o|r(a|á)s|rem|res|rei|ria|r(a|á)|va|is|i|m|v|u|r|s|))|((R|R)ETIFI(C(O|A|Á|E)|QUE)(VAMOS|SSEIS|SSEMOS|SSEM|RAMOS|SSEMOS|REMOS|RÍAMOS|RÍEIS|RIAM|REIS|RMOS|RDES|SSES|VEIS|STES|RIAS|VAM|SSE|STE|MOS|VAS|RAM|R(Ã|A)O|R(A|Á)S|REM|RES|REI|RIA|R(A|Á)|VA|IS|I|M|V|U|R|S|))'}

pattSubs={'DELEGADO':'((D|d)(e|o)l(e|o)(g|c)a(d(o|a))(\(a\)|)( |)((d|D)e|)( |)(Pokcia|Pajčia|(P|p)ol(i|í)ci(al|a)|)((T|t)itular|\n|)( |)(.+|))|((D|D)(E|O)L(O|E)(G|C)A(D(O|A))(\(A\)|)( |)((D|D)E|)( |)((P|P)OL(I|Í)CI(AL|A)|)((T|T)ITULAR|)( |)(.|..|...|))'}

pattLaw={'(A|a)rt(\.|igo|)|(A|A)RT(\.|IGO|)##(21)(.+)((L|l)ei|)( |)(12(\.|)850)(\/|\-|\.|)(13)':'Art. 21 Lei 12850/13 - 6 (seis) meses a 2 (dois) anos e multa',
        '((D|d)esobedi(ê|e)ncia)|((D|D)ESOBEDI(Ê|E)NCIA)':'DESOBEDIÊNCIA - detenção, de 15 dias a 6 meses, e multa',
         '((C|c)rime|CRIME)( |)((D|d)(E|e))':'CRIME - '}


def getPrazo(dictFull,key=1,types='PRAZO'):
    global typesSear, typesSub
    try:
        arrayStr=dictFull[key].split('\n')
        final, eletiv=[], []
        for Str in arrayStr:
            for x in cr(typesSear[types],Str): eletiv.append(x.group(0))
        for Str in eletiv:
            for x in re.finditer(typesSub[types],Str): final.append(x.group(0))
        if len(final)==0: return 'NOTF'
        if len(final)==1: return final[0]
        else: return final 
    except Exception as e: return f'Exception - {str(e)}'
                
def deepPena(array, arrayStr):
    try:
        nt=[array, [x+1 for x in array] ,[x-1 for x in array] ,[x+2 for x in array], [x-2 for x in array]]
        for n in nt:
            for con in n:
                for i, Str in enumerate(arrayStr):
                    if i==con:
                        print(f'DEEPPENA##{Str}##')
                        for k, v in pattLaw.items(): 
                            art=str(re.split(r'##',k)).strip()[0] if re.search(r'##',v) else k
                            if re.search(art,Str):
                                if re.search(r'CRIME',v): return f'{v}{Str}'
                                else: return v
        return 'NOTF'
    except Exception as e: return f'Exception - {str(e)}'
            
def getPena(dictFull,key=1,types='DESCR'):
    global typesSear
    control=[]
    try:
        arrayStr=dictFull[key].split('\n')
        for i, Str in enumerate(arrayStr):
            for x in re.finditer(typesSear[types],Str):
                control.append(i)
        if len(control)>0:
            for x in control:
                ret=deepPena(control,arrayStr)
                if ret!='NOTF': return ret    
        return 'NOTF'
    except Exception as e: return f'Exception - {str(e)}'

def getOPIBO(dictFull,key,types='OFI'):
    global typesSear, typesSub
    try:
        arrayStr=dictFull[key].split('\n')
        eletiv=[]
        for Str in arrayStr:
            for x in re.finditer(typesSear[types],Str): eletiv.append(x.group(0))
        if len(eletiv)>0: 
            eletiv=[mat for mat in eletiv if re.search(typesSub[types],mat) and not re.search(r'((P|p)enal|PENAL|(A|a)rtigo|ARTIGO)',mat)]
            eMore= [e for e in eletiv if re.search(r'([0-9]+) (E|e)',e)]
            if len(eMore)>0:
                for i, Str in enumerate(arrayStr):
                    if re.search(eMore[0], Str):
                        for k, Str in enumerate(arrayStr): 
                            if i+1==k: eletiv[0]=f'{eletiv[0]} {Str}'
            return eletiv[0] if len(eletiv)>0 else 'NOTIF'  
        else: return 'NOTIF'      
    except Exception as e: return f'Exception - {str(e)}'

def castUA(array):
    try:
        if len(array)==0: return 'NOTF'
        unique=list(set(array))
        unique=[x for x in array if not re.search(r'CLARO |(c|C)LARO |(S|s)r\.',x)]
        return 'NOTF' if len(unique)==0 else str(unique).replace('[','').replace(']','').replace("'","")
    except Exception as e: return f'Exception - {str(e)}'

def getDPOL(dictFull,key,types='DEPTPOL',controller=0):
    global typesSear, typesSub, patterns
    eletiv,ret=[],[]
    try:
        arrayStr=dictFull[key].split('\n')
        for Str in arrayStr:
            for x in re.finditer(typesSear[types],Str): eletiv.append(x.group(0))
        print(f'###{eletiv}####')
        if len(eletiv)>0:
            if types!='DEPTPOL':
                for mat in eletiv:
                    if not re.search(patterns['COMMON'],mat) and not re.search(r'\@|(N|n|)est(a|á) |(n|N)(o|a) ',mat): ret.append(mat)
                    elif not re.search(r'\@|\,|((N|n|)est(a|á)|(n|N)(o|a))( |\n|\.)',mat): ret.append(re.sub(r'(\;|\-).+','',mat))
                    elif re.search(r'(DP|dp).+',mat):
                        x='DP'+re.sub(r'.+?(DP|dp)','',re.sub(r'(\;|\-|\@).+','',mat).upper())
                        if len(x)>3: ret.append(x)
                return castUA(ret)  
            else: 
                ret=castUA(eletiv)
                return ret if ret!= 'NOTF' else getDPOL(dictFull,key,'DELTIP',controller+1)
        else:
            if controller == 0: return getDPOL(dictFull,key,'DELTIP',controller+1)
            else: return 'NOTF'
    except Exception as e: return f'Exception - {str(e)}'
    
def getClassi(dictFull,key=1):
    global pattClass
    try:
        arrayStr=dictFull[key].split('\n')
        for Str in arrayStr:
            for k, v in pattClass.items():
                if re.search(v,Str): return k
        return 'NOTF'
    except Exception as e: return f'Exception - {str(e)}'
    
def getSubscri(dictFull,key=1,types='DELEGADO'):
    global pattSubs, patterns
    eletiv=[]
    try:
        arrayStr=dictFull[key].split('\n')
        for i, Str in enumerate(arrayStr):
            if re.search(pattSubs[types],Str) and not re.search(r'(P|p)elo',Str):
                arrayStr2=dictFull[key].split('\n')
                for i2, ST in enumerate(arrayStr2):
                    if i-1==i2:
                        if re.search(r'MASP',ST):
                            arrayStr3=dictFull[key].split('\n')
                            for i3, ST in enumerate(arrayStr3):
                                if i2-1==i3: eletiv.append(ST)
                        else: eletiv.append(ST)
        print(eletiv)
        eletiv=[e for e in eletiv if re.search(patterns['NAME'],e) and not re.search(r'CLARO',e)]           
        return types+'(A)'+' '+str(re.sub(patterns['COMMON'],'',re.sub(r'([0-9]+)','',eletiv[len(eletiv)-1]))) if len(eletiv)>0 else 'NOTF' 
    except Exception as e: return f'Exception - {str(e)}'
        
def getMaxWordArr(array):
    maybe={}
    try:
        for elem in array:
            if len(maybe) == 0: maybe[elem]=1
            maybe[elem]=maybe[elem]=+1 if elem in maybe else 1
        return max(maybe, key=lambda x: maybe[x])
    except Exception as e: return f'Exception - {str(e)}'

def deepSAD(key,estado):
    global states
    mati={}
    try:
        splitText=mensageDict[key].split('\n')
        for i, splt in enumerate(splitText):
            for k, v in fullSearAdress.items():
                if re.search(v,splt):
                    mati[i]=[mat.group(0) for mat in re.finditer(v,splt)][0]
                    pass     
        if len(mati)>0:
            for k, v in mati.items():
                if re.search(f'(\/|\-)(| ){states[estado]}',v): return v
                kmais=k+1
                kmenos=k-1 if k>0 else 0
                for i, splt in enumerate(splitText):
                    if kmenos==i:
                        if re.search(f'(\/|\-)(| ){states[estado]}',splt): return v
                    if kmais==i:
                        if re.search(f'(\/|\-)(| ){states[estado]}',splt): return v
            return [y for k,y in mati.items()][0]        
        return 'NOTF'                      
    except Exception as e: return f'Exception - {str(e)}'
    
def getAdress(keyFrom, values, estado):
    global adress
    adressBase, lat={}, []
    try:
        for key, value in adress.items():
            base=[mat.group(0) for mat in re.finditer(value, values)]
            if len(base)>0: 
                adressBase[key]=base
                lat.append(key)
        if len(lat)==0: return deepSAD(keyFrom,estado)
        else: 
            for key in lat:
                for it in adressBase[key]:
                    if re.search(f'(\/|\-)(| ){states[estado]}',it): return str(it).replace("'","")
        return adressBase[lat[0]][0]     
    except Exception as e: return f'Exception - {str(e)}'

def getEstado(sta, value):
    global states, states2
    try:
        if sta!='NOTF':
            start=sta
            if re.search(r'(\/|\-)',start):
                x=re.split(r'(\/|\-)',start)
                for k,v in states.items():
                    if v==x[len(x)-1]: return k
                    if k==x[len(x)-1].upper(): return k
        for k, v in states.items():
            if re.search(k, value.upper()): return k
        for k, v in states.items():
            if re.search(f'(\/|\/|-|-)( |){v}( |\.|\;|\n)', value.upper()): return k
        for k, v in states2.items():
            if re.search(v, value.upper()): return getMaxWordArr([x for x,y in states.items() if y==k])
        return 'NOTF' 
    except Exception as e: return f'Exception - {str(e)}'
        
def getDatAndComaux(value,estado):
    global patterns
    comarc=None
    try:
        for mat in re.finditer(patterns['DATECOM'],value):
            data=mat.group(11)+'/'+MONTH[mat.group(13).upper()]+'/'+mat.group(18)
            if re.search(patterns['COMAUX'],mat.group(1)): comarc=mat.group(1).replace(',','') 
            comaux=re.sub(patterns['COMAUX'], '',mat.group(1))
            print(comarc)
            return data, re.sub(f'({states[estado]})( |\.|\;|)','',comaux.replace(',','')), comarc 
        ret=[]
        for x in re.finditer(patterns['DOFY'],value):
            tmp=re.split('de',x.group(0))
            print(f'{tmp}|{x.group(0)}')
            tmp=tmp[0].strip()+'/'+MONTH[tmp[1].strip().upper()]+'/'+tmp[2].strip()
            ret.append(tmp)
        ret=list(set(ret))[0] if len(ret)>0 else None
        return ret, None, comarc 
    except Exception as e: return f'Exception - {str(e)}'
        
def getComarca(array,value,comarc,estado, comaux):
    global states, patterns
    try:
        if comarc is None:
            value=normalize('NFKD', value).encode('ASCII', 'ignore').decode('ASCII')
            UFARR=f'(/|-)(| ){states[estado]}'
            UFTEXT=f'((([A-Z]|[a-z]| )+)|(([A-Z]|[a-z])+?))((| / |/|-| - )({states[estado]}))(\n|\,|\r|\.|\;)'
            comarca = [it for it in array if re.search(UFARR,it)]
            if len(comarca)==0: 
                comarca=[re.sub(patterns['COMMON'],'',matE.group(0).strip().upper()) for matE in re.finditer(UFTEXT,value)]
                comarca=[re.sub(patterns['COMMON'],'',matE.group(0).strip().upper()) for matE in re.finditer(patterns['UFFULL'],value)] if len(comarca)==0 else comarca
                comarca=comaux if len(comarca)==0 else comarca
                comarca=['NOTF'] if len(comarca)==0 else comarca
            else: comarca
            comarca=getMaxWordArr(comarca) if len(comarca) > 1 else comarca[0]
        else: comarca=comarc
        return comarca
    except Exception as e: return f'Exception - {str(e)}'

def getVisionFile(file,img=False):
    try:
        #open file
        if img: content=file
        else: 
            with io.open(file, 'rb') as image_file: 
                content = image_file.read()
        #get Client Vision
        client = vision.ImageAnnotatorClient()
        image = vision.types.Image(content=content)
        response = client.document_text_detection(image=image)
        labels = response.text_annotations
        return labels
    except Exception as e: return f'Exception - {str(e)}'

def image_to_byte_array(image:IMage):
    imgByteArr = io.BytesIO()
    image.save(imgByteArr, format='JPEG')
    imgByteArr = imgByteArr.getvalue()
    return imgByteArr

def normalizationType(path,msgPoint=1):
    ext=path.split('.')
    ext=ext[len(ext)-1]
    _hash=hashlib.md5(str(time.time()).encode('utf-8')).hexdigest()
    try:
        if ext in ['pdf','Pdf','PDF']:
            pages=convert_from_path(path)
            if len(pages)>1:
                for page in pages:
                    if not getMsgsAndBounds(getVisionFile(image_to_byte_array(page),True),_hash,msgPoint): break
                    msgPoint+=1
            else: getMsgsAndBounds(getVisionFile(image_to_byte_array(pages[0]),True),_hash,msgPoint) 
        else: getMsgsAndBounds(getVisionFile(path),_hash,msgPoint)
        return _hash
    except Exception as e: return f'Exception - {str(e)}'

def getMsgsAndBounds(labels,_hash,msgPoint=1):
    global mensageDict, tokenWords
    ret,contWord=True,0
    try:
        for i, text in enumerate(labels): 
            if i == 0: mensageDict[str(_hash)+'|'+str(msgPoint)]=text.description
            else: 
                vertices = (['({},{})'.format(vertex.x, vertex.y) for vertex in text.bounding_poly.vertices])
                tokenWords.append((str(_hash), msgPoint, contWord, text.description, vertices))     
                contWord+=1
        return ret
    except Exception as e: 
        print(str(e))
        return False
       
def testNone(key, types, result):
    global mensageDict
    try:
        if key>1:
            if result[types] is None: return True
            elif result[types]=='NOTF': return True
            else: return False
        return True
    except Exception as e: return f'Exception - {str(e)}'

def builderPOLCIV(key,value):
    global patterns
    result, cit, estado, comarc, comaux={}, 'CIDADE', {}, None, None
    _key=key.split('|')
    _key=int(_key[1].strip())
    if _key > 1 and re.search(patterns['PODJUD'],value): return "Ops, ainda estamos em desenvolvimento"
    result['ORGAO'], result['ESFERA'], result['OFICIO_TIPO'], result['VARA']='POLICIA CIVIL', 'CRIMINAL', 'EXTRA', 'NA'
    prestates=[str(re.sub(patterns['POLSUB'],'',re.sub(patterns['COMMON'],'',one2.group(0)))).strip() for one2 in re.finditer(patterns['POLDE'],value.upper())] 
    subTy=['OFICIO_CLASSI','ESTADO', 'DATAEXP','COMARCA','ENDEREÇO','OFICIO','PROCESSO','INQUERITO','BO','SUBORGAO_1','SUBORGAO_2','SUBSCRITOR','PRAZO','PENA']
    for i, it in enumerate(subTy):
        if testNone(_key,it,result):
            if i==0: result[it]=getClassi(mensageDict,key)
            elif i==1: 
                result[it]=getEstado(getMaxWordArr(prestates),value)
                estado=result[it]
            elif i==2 and _key==1: 
                result[it], result['CIDADE'], comarc=getDatAndComaux(value,estado)
            elif i==3: 
                result[it]=getComarca(prestates,value,comarc,estado, comaux)
                if _key==1:
                    if result[cit]=='NOTF' or result[cit] is None or len(result[cit])<3: result[cit]=result[it]
                    if result[it]=='NOTF' and result[cit]!='NOTF': result[it]=result[cit]
            elif i==4: result[it]=getAdress(key, value,estado)
            elif i==5: result[it]=getOPIBO(mensageDict,key)
            elif i==6: result[it]=getOPIBO(mensageDict,key,'PROC')
            elif i==7: result[it]=getOPIBO(mensageDict,key,'INQ')
            elif i==8: result[it]=getOPIBO(mensageDict,key,'BO')
            elif i==9: result[it]=getDPOL(mensageDict,key)
            elif i==10: result[it]=getDPOL(mensageDict,key,'DELTIP',1)
            elif i==11: result[it]=getSubscri(mensageDict,key)
            elif i==12: result[it]=getPrazo(mensageDict,key)
            elif i==13: result[it]=getPena(mensageDict,key)
    return result 

def motorOrgan(_hash):
    global mensageDict, patterns
    ret,result=True,{}
    try:
        for key, value in mensageDict.items():
            if re.search(patterns['POLCIV'], value):
                result=builderPOLCIV(key, value)
            else: result={f'{_hash}':'Ops, ainda estamos em desenvolvimento'}
    except Exception as e:
        print(e)
        ret=False
    print(json.dumps(result,ensure_ascii=False))
    return ret       


'''to execute:
x=normalizationType('<path from your photo>')
if not re.search(r'Exception',x): motorOrgan(x)
else: x
'''
'''to view metrics:
tokenWords
'''
