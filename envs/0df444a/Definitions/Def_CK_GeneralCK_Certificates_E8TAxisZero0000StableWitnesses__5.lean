-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000StableWitnesses__5
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0000StableWitnesses__5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:48:02.355808+00:00
-- url     : https://prove2.me/theorems/1fcb97a8-cb79-499f-afcb-dce3eaa2648a
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0000StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0001StableWitnesses, GeneralCK.Certificates.E8TAxisZero00…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0000StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0001StableWitnesses, GeneralCK.Certificates.E8TAxisZero0002StableWitnesses, GeneralCK.Certificates.E8TAxisZero0003StableWitnesses, GeneralCK.Certificates.E8TAxisZero0004StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0000StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0001StableWitnesses, GeneralCK.Certificates.E8TAxisZero0002StableWitnesses, GeneralCK.Certificates.E8TAxisZero0003StableWitnesses, GeneralCK.Certificates.E8TAxisZero0004StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0000StableWitnesses (+4 modules: GeneralCK.Certificates.E8TAxisZero0001StableWitnesses, GeneralCK.Certificates.E8TAxisZero0002StableWitnesses, GeneralCK.Certificates.E8TAxisZero0003StableWitnesses, GeneralCK.Certificates.E8TAxisZero0004StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0000StableWitnesses (+4 modules: GeneralCK/Certificates/E8TAxisZero0001StableWitnesses, GeneralCK/Certificates/E8TAxisZero0002StableWitnesses, GeneralCK/Certificates/E8TAxisZero0003StableWitnesses, GeneralCK/Certificates/E8TAxisZero0004StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0000StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0000StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨18520713486944908849589682846130841202756280060, 18520713486944908849589682846130841202756280061⟩
def centerDExp : DyadicInterval precision := ⟨1424925672993232823669539261288255236086664390075, 1424925672993232823669539261288255238285687645628⟩
def centerDLog : DyadicInterval precision := ⟨994632373490912888449452118447742043824684057942, 994632373490912888449452118447742046023707313495⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1424925672993232823669539261288255236636420203963, scale precision, 1424925672993232823669539261288255237735931831740, scale precision,
    0, 128, 0, 128, ⟨-37041426973889817699179365692261682969380929891, -37041426973889817699179365692261682969378832738⟩, ⟨-37041426973889817699179365692261681841646287505, -37041426973889817699179365692261681841644190352⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨19787261415618956269193137821462137643299660144, 19787261415618956269193137821462137643299660145⟩
def centerCExp : DyadicInterval precision := ⟨1422458110153910514512537297173309437352704550462, 1422458110153910514512537297173309439551727806015⟩
def centerCLog : DyadicInterval precision := ⟨993382423595496802456179790205135829228690482622, 993382423595496802456179790205135831427713738175⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1422458110153910514512537297173309437902460364350, scale precision, 1422458110153910514512537297173309439001971992127, scale precision,
    0, 128, 0, 128, ⟨-39574522831237912538386275642924275851445840514, -39574522831237912538386275642924275851443743361⟩, ⟨-39574522831237912538386275642924274721754897217, -39574522831237912538386275642924274721752800064⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨38315625879059651361002779648504240877812961677, 38315625879059651361002779648504240877812961678⟩
def centerBExp : DyadicInterval precision := ⟨1386844740094340195616466637239585533175353614045, 1386844740094340195616466637239585535374376869598⟩
def centerBLog : DyadicInterval precision := ⟨975222308904945787429848329856119060048479601589, 975222308904945787429848329856119062247502857142⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1386844740094340195616466637239585533725109427933, scale precision, 1386844740094340195616466637239585534824621055710, scale precision,
    0, 128, 0, 128, ⟨-76631251758119302722005559297008482334977348295, -76631251758119302722005559297008482334975251142⟩, ⟨-76631251758119302722005559297008481176276595570, -76631251758119302722005559297008481176274498417⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨18045766478403223402692576908062521137160327707, 18995665047735116218618892934888584156033732658⟩
def wholeDExp : DyadicInterval precision := ⟨1423999843327116683343282796578766319521637719281, 1425852095715601701956974364377367525255168591536⟩
def wholeDLog : DyadicInterval precision := ⟨994163517538761546318115582447098111973928863644, 995101379269639710001049868967429117197932794939⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1423999843327116683343282796578766320071393533169, scale precision, 1425852095715601701956974364377367524705412777648, scale precision,
    0, 128, 0, 128, ⟨-37991330095470232437237785869777168876302439825, -37991330095470232437237785869777168876300342672⟩, ⟨-36091532956806446805385153816125041710820745831, -36091532956806446805385153816125041710818648678⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨18045766478403223402692576908062521137160327707, 21528821741448843534916460983893935247377312626⟩
def wholeCExp : DyadicInterval precision := ⟨1419072076386451827323355281724057475125424745425, 1425852095715601701956974364377367525255168591536⟩
def wholeCLog : DyadicInterval precision := ⟨991665478244185565170265217796583833220263420595, 995101379269639710001049868967429117197932794939⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1419072076386451827323355281724057475675180559313, scale precision, 1425852095715601701956974364377367524705412777648, scale precision,
    0, 128, 0, 128, ⟨-43057643482897687069832921967787871060948917639, -43057643482897687069832921967787871060946820486⟩, ⟨-36091532956806446805385153816125041710820745831, -36091532956806446805385153816125041710818648678⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨36097938246870058546958457136650379086153782135, 40533518663166560848124822041176720320630938596⟩
def wholeBExp : DyadicInterval precision := ⟨1382641925933778624162051348417793950459834536220, 1391059939013504036843525882064723713679662965519⟩
def wholeBLog : DyadicInterval precision := ⟨973064230117935785593232025639809023515288350551, 977383551042037225952002295716720301818895510063⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1382641925933778624162051348417793951009590350108, scale precision, 1391059939013504036843525882064723713129907151631, scale precision,
    0, 128, 0, 128, ⟨-81067037326333121696249644082353441222374352421, -81067037326333121696249644082353441222372255268⟩, ⟨-72195876493740117093916914273300757594713787782, -72195876493740117093916914273300757594711690629⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0000StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0001StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0001StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨17570823905353200298253796885578914283159635363, 17570823905353200298253796885578914283159635364⟩
def centerDExp : DyadicInterval precision := ⟨1426779112096221605837879292607267577758400287595, 1426779112096221605837879292607267579957423543148⟩
def centerDLog : DyadicInterval precision := ⟨995570534987112542562287311753608945074363304183, 995570534987112542562287311753608947273386559736⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1426779112096221605837879292607267578308156101483, scale precision, 1426779112096221605837879292607267579407667729260, scale precision,
    0, 128, 0, 128, ⟨-35141647810706400596507593771157829129455155887, -35141647810706400596507593771157829129453058734⟩, ⟨-35141647810706400596507593771157828003185482721, -35141647810706400596507593771157828003183385568⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨18837347347792335890441586986672273956520483180, 18837347347792335890441586986672273956520483181⟩
def centerCExp : DyadicInterval precision := ⟨1424308387357809551060822779449006367915237000413, 1424308387357809551060822779449006370114260255966⟩
def centerCLog : DyadicInterval precision := ⟨994319786215667360595982839376915120674104652161, 994319786215667360595982839376915122873127907714⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1424308387357809551060822779449006368464992814301, scale precision, 1424308387357809551060822779449006369564504442078, scale precision,
    0, 128, 0, 128, ⟨-37674694695584671780883173973344548477153712419, -37674694695584671780883173973344548477151615266⟩, ⟨-37674694695584671780883173973344547348930317455, -37674694695584671780883173973344547348928220302⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨36414738655787567372767384943771663269163032974, 36414738655787567372767384943771663269163032975⟩
def centerBExp : DyadicInterval precision := ⟨1390457007296089150201247600492916033760023101622, 1390457007296089150201247600492916035959046357175⟩
def centerBLog : DyadicInterval precision := ⟨977074608077038208556184078185131913450555306680, 977074608077038208556184078185131915649578562233⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1390457007296089150201247600492916034309778915510, scale precision, 1390457007296089150201247600492916035409290543287, scale precision,
    0, 128, 0, 128, ⟨-72829477311575134745534769887543327116172396986, -72829477311575134745534769887543327116170299833⟩, ⟨-72829477311575134745534769887543325960481832064, -72829477311575134745534769887543325960479734911⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨17095885651040514825842973106213884464633028208, 18045766478403223402692576908062521137160327708⟩
def wholeDExp : DyadicInterval precision := ⟨1425852095715601701956974364377367523056145335983, 1427706722737910795912950268245206061292909357824⟩
def wholeDLog : DyadicInterval precision := ⟨995101379269639710001049868967429114998909539386, 996039840755618551298709894112357435963326953459⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1425852095715601701956974364377367523605901149871, scale precision, 1427706722737910795912950268245206060743153543936, scale precision,
    0, 128, 0, 128, ⟨-36091532956806446805385153816125042837822662151, -36091532956806446805385153816125042837820564998⟩, ⟨-34191771302081029651685946212427768366498148783, -34191771302081029651685946212427768366496051630⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨17095885651040514825842973106213884464633028208, 20578871293540181087774692060534010761932455779⟩
def wholeCExp : DyadicInterval precision := ⟨1420918019911383254566844357126927029598135402497, 1427706722737910795912950268245206061292909357824⟩
def wholeCLog : DyadicInterval precision := ⟨992601745007901601457433275450218201286829393502, 996039840755618551298709894112357435963326953459⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1420918019911383254566844357126927030147891216385, scale precision, 1427706722737910795912950268245206060743153543936, scale precision,
    0, 128, 0, 128, ⟨-41157742587080362175549384121068022089323650775, -41157742587080362175549384121068022089321553622⟩, ⟨-34191771302081029651685946212427768366498148783, -34191771302081029651685946212427768366496051630⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨34197217411116296057608686704873335075949402705, 38632454867883059004928015843439109440062491347⟩
def wholeBExp : DyadicInterval precision := ⟨1386243581168110757962356618682828762093889765683, 1394682867839290040449494560757779836865701202074⟩
def wholeBLog : DyadicInterval precision := ⟨974913818515194634191299090803398235106428622793, 979238570356633093565442356204073681058797827565⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1386243581168110757962356618682828762643645579571, scale precision, 1394682867839290040449494560757779836315945388186, scale precision,
    0, 128, 0, 128, ⟨-77264909735766118009856031686878219459727648940, -77264909735766118009856031686878219459725551787⟩, ⟨-68394434822232592115217373409746669575805430906, -68394434822232592115217373409746669575803333753⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0001StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0002StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0002StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨16620951598713310515991793134470960105966667927, 16620951598713310515991793134470960105966667928⟩
def centerDExp : DyadicInterval precision := ⟨1428634928244308711378823712010396600887434155037, 1428634928244308711378823712010396603086457410590⟩
def centerDLog : DyadicInterval precision := ⟨996509296687561598184276445757911818881532200755, 996509296687561598184276445757911821080555456308⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1428634928244308711378823712010396601437189968925, scale precision, 1428634928244308711378823712010396602536701596702, scale precision,
    0, 128, 0, 128, ⟨-33241903197426621031983586268941920774337701223, -33241903197426621031983586268941920774335604070⟩, ⟨-33241903197426621031983586268941919649531067638, -33241903197426621031983586268941919649528970485⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨17887451800319839290372054347300106957639710412, 17887451800319839290372054347300106957639710413⟩
def centerCExp : DyadicInterval precision := ⟨1426161035184028525298037043722834741256924120264, 1426161035184028525298037043722834743455947375817⟩
def centerCLog : DyadicInterval precision := ⟨995257747843394008246053613269947662197904331132, 995257747843394008246053613269947664396927586685⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1426161035184028525298037043722834741806679934152, scale precision, 1426161035184028525298037043722834742906191561929, scale precision,
    0, 128, 0, 128, ⟨-35774903600639678580744108694600214478659360220, -35774903600639678580744108694600214478657263067⟩, ⟨-35774903600639678580744108694600213351901578583, -35774903600639678580744108694600213351899481430⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨34513994673849056249355123398713418481189360346, 34513994673849056249355123398713418481189360347⟩
def centerBExp : DyadicInterval precision := ⟨1394078409980602946896329831479021586411470776403, 1394078409980602946896329831479021588610494031956⟩
def centerBLog : DyadicInterval precision := ⟨978929238224557456986699259969584039246976828266, 978929238224557456986699259969584041446000083819⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1394078409980602946896329831479021586961226590291, scale precision, 1394078409980602946896329831479021588060738218068, scale precision,
    0, 128, 0, 128, ⟨-69027989347698112498710246797426837538723980884, -69027989347698112498710246797426837538721883731⟩, ⟨-69027989347698112498710246797426836386035557654, -69027989347698112498710246797426836386033460501⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨16146021631622132505602154469507921559441792473, 17095885651040514825842973106213884464633028209⟩
def wholeDExp : DyadicInterval precision := ⟨1427706722737910795912950268245206059093886102271, 1429563729219877177794428923148060136729147575503⟩
def wholeDLog : DyadicInterval precision := ⟨996039840755618551298709894112357433764303697906, 996978902895462305330196666434672379232603104095⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1427706722737910795912950268245206059643641916159, scale precision, 1429563729219877177794428923148060136179391761615, scale precision,
    0, 128, 0, 128, ⟨-34191771302081029651685946212427769492036061204, -34191771302081029651685946212427769492033964051⟩, ⟨-32292043263244265011204308939015842556846715446, -32292043263244265011204308939015842556844618293⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨16146021631622132505602154469507921559441792473, 19628941078537730196812941240615820545473948722⟩
def wholeCExp : DyadicInterval precision := ⟨1422766325265285935775877612508304620426744726032, 1429563729219877177794428923148060136729147575503⟩
def wholeCLog : DyadicInterval precision := ⟨993538609139131549366545609183574417798866669948, 996978902895462305330196666434672379232603104095⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1422766325265285935775877612508304620976500539920, scale precision, 1429563729219877177794428923148060136179391761615, scale precision,
    0, 128, 0, 128, ⟨-39257882157075460393625882481231641655672054699, -39257882157075460393625882481231641655669957546⟩, ⟨-32292043263244265011204308939015842556846715446, -32292043263244265011204308939015842556844618293⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨32296631088779800838933709755643288761184366277, 36731543043628067898155960956801315285829304374⟩
def wholeBExp : DyadicInterval precision := ⟨1389854329341637920452395630847774504872918950707, 1398314974961442163854890103597640425462105602732⟩
def wholeBLog : DyadicInterval precision := ⟨976765729861290771806028354487818354829744711949, 981095928713060143440614067544145824500769419918⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1389854329341637920452395630847774505422674764595, scale precision, 1398314974961442163854890103597640424912349788844, scale precision,
    0, 128, 0, 128, ⟨-73463086087256135796311921913602631149755508930, -73463086087256135796311921913602631149753411777⟩, ⟨-64593262177559601677867419511286576947771756711, -64593262177559601677867419511286576947769659558⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0002StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0003StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0003StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨15671095633019860897215209866369230294530182688, 15671095633019860897215209866369230294530182689⟩
def centerDExp : DyadicInterval precision := ⟨1430493126269901616989962472786282227563085586833, 1430493126269901616989962472786282229762108842386⟩
def centerDLog : DyadicInterval precision := ⟨997448659491958118410211053001204308338128746073, 997448659491958118410211053001204310537152001626⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1430493126269901616989962472786282228112841400721, scale precision, 1430493126269901616989962472786282229212353028498, scale precision,
    0, 128, 0, 128, ⟨-31342191266039721794430419732738461150734173770, -31342191266039721794430419732738461150732076617⟩, ⟨-31342191266039721794430419732738460027388654137, -31342191266039721794430419732738460027386556984⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨16937573839142958325485834377227148560267537173, 16937573839142958325485834377227148560267537174⟩
def centerCExp : DyadicInterval precision := ⟨1428016058447464986913713547260113933228851511629, 1428016058447464986913713547260113935427874767182⟩
def centerCLog : DyadicInterval precision := ⟨996196309375885725170924381614964827977213047958, 996196309375885725170924381614964830176236303511⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1428016058447464986913713547260113933778607325517, scale precision, 1428016058447464986913713547260113934878118953294, scale precision,
    0, 128, 0, 128, ⟨-33875147678285916650971668754454297683183172569, -33875147678285916650971668754454297683181075416⟩, ⟨-33875147678285916650971668754454296557889073280, -33875147678285916650971668754454296557886976127⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨32613386452068186512645484902019899271106700537, 32613386452068186512645484902019899271106700538⟩
def centerBExp : DyadicInterval precision := ⟨1397708984828652127800670294526114219544144078877, 1397708984828652127800670294526114221743167334430⟩
def centerBLog : DyadicInterval precision := ⟨980786206259123103316407863840628217789319410175, 980786206259123103316407863840628219988342665728⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1397708984828652127800670294526114220093899892765, scale precision, 1397708984828652127800670294526114221193411520542, scale precision,
    0, 128, 0, 128, ⟨-65226772904136373025290969804039799117061596556, -65226772904136373025290969804039799117059499403⟩, ⟨-65226772904136373025290969804039797967367302749, -65226772904136373025290969804039797967365205596⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨15196173486161644112312625263859972843392477663, 16146021631622132505602154469507921559441792474⟩
def wholeDExp : DyadicInterval precision := ⟨1429563729219877177794428923148060134530124319950, 1431423120000492259122295500270501609338356151294⟩
def wholeDLog : DyadicInterval precision := ⟨996978902895462305330196666434672377033579848542, 997918566589803370182164072894784146467964879609⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1429563729219877177794428923148060135079880133838, scale precision, 1431423120000492259122295500270501608788600337406, scale precision,
    0, 128, 0, 128, ⟨-32292043263244265011204308939015843680922551602, -32292043263244265011204308939015843680920454449⟩, ⟨-30392346972323288224625250527719945125478162145, -30392346972323288224625250527719945125476064992⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨15196173486161644112312625263859972843392477663, 18679030162303741504086552505207128636420699063⟩
def wholeCExp : DyadicInterval precision := ⟨1424616997239092963457576464131988991327542522851, 1431423120000492259122295500270501609338356151294⟩
def wholeCLog : DyadicInterval precision := ⟨994476071531667759156497176411557096946142239221, 997918566589803370182164072894784146467964879609⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1424616997239092963457576464131988991877298336739, scale precision, 1431423120000492259122295500270501608788600337406, scale precision,
    0, 128, 0, 128, ⟨-37358060324607483008173105010414257836831942606, -37358060324607483008173105010414257836829845453⟩, ⟨-30392346972323288224625250527719945125478162145, -30392346972323288224625250527719945125476064992⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨30396171800123412460251093542107771996415104709, 34830775707694518323356855819802492385993843110⟩
def wholeBExp : DyadicInterval precision := ⟨1393474206903787201785230037422771619329955308483, 1401956297293647672601908456314651955587398897934⟩
def wholeBLog : DyadicInterval precision := ⟨978619971033722696354607064598753113312271289775, 982955633057142006343070852505364093763236165501⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1393474206903787201785230037422771619879711122371, scale precision, 1401956297293647672601908456314651955037643084046, scale precision,
    0, 128, 0, 128, ⟨-69661551415389036646713711639604985348582846224, -69661551415389036646713711639604985348580749071⟩, ⟨-60792343600246824920502187084215543419725645729, -60792343600246824920502187084215543419723548576⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0003StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0004StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0004StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨24537142255194453123116932212186507937933422250, 24537142255194453123116932212186507937933422251⟩
def centerDExp : DyadicInterval precision := ⟨1413242115861781282406286337262575277488632337182, 1413242115861781282406286337262575279687655592735⟩
def centerDLog : DyadicInterval precision := ⟨988704564336070341914220112468827111579893378896, 988704564336070341914220112468827113778916634449⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1413242115861781282406286337262575278038388151070, scale precision, 1413242115861781282406286337262575279137899778847, scale precision,
    0, 128, 0, 128, ⟨-49074284510388906246233864424373016444396818951, -49074284510388906246233864424373016444394721798⟩, ⟨-49074284510388906246233864424373015307338967204, -49074284510388906246233864424373015307336870051⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨25803874188220294174958011373635178398750026047, 25803874188220294174958011373635178398750026048⟩
def centerCExp : DyadicInterval precision := ⟨1410794430353970155378151434557014702381339587854, 1410794430353970155378151434557014704580362843407⟩
def centerCLog : DyadicInterval precision := ⟨987459646359117521932777793286535584300247077863, 987459646359117521932777793286535586499270333416⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1410794430353970155378151434557014702931095401742, scale precision, 1410794430353970155378151434557014704030607029519, scale precision,
    0, 128, 0, 128, ⟨-51607748376440588349916022747270357367016406973, -51607748376440588349916022747270357367014309820⟩, ⟨-51607748376440588349916022747270356227985794371, -51607748376440588349916022747270356227983697218⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨50358387464788094565508226754163990527967612749, 50358387464788094565508226754163990527967612750⟩
def centerBExp : DyadicInterval precision := ⟨1364176857568604256874790178069699266527439465291, 1364176857568604256874790178069699268726462720844⟩
def centerBLog : DyadicInterval precision := ⟨963544769795384609901545553993877875672062457030, 963544769795384609901545553993877877871085712583⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1364176857568604256874790178069699267077195279179, scale precision, 1364176857568604256874790178069699268176706906956, scale precision,
    0, 128, 0, 128, ⟨-100716774929576189131016453508327981644913442008, -100716774929576189131016453508327981644911344855⟩, ⟨-100716774929576189131016453508327980466959106142, -100716774929576189131016453508327980466957008989⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨23745456717760790936231587082098894243338759235, 25328844546563792145364175869944518712165973940⟩
def wholeDExp : DyadicInterval precision := ⟨1411711825212582109366700862001636146388582104418, 1414774032904110256356769903186423883637657967959⟩
def wholeDLog : DyadicInterval precision := ⟨987926367053698422343402489929183441562734658937, 989483173884649444583154341512750141457828864394⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1411711825212582109366700862001636146938337918306, scale precision, 1414774032904110256356769903186423883087902154071, scale precision,
    0, 128, 0, 128, ⟨-50657689093127584290728351739889037993478205684, -50657689093127584290728351739889037993476108531⟩, ⟨-47490913435521581872463174164197787918765244181, -47490913435521581872463174164197787918763147028⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨23745456717760790936231587082098894243338759235, 27862410764083842283213187030105662664219775912⟩
def wholeCExp : DyadicInterval precision := ⟨1406825792685543838526339659362356364657647097115, 1414774032904110256356769903186423883637657967959⟩
def wholeCLog : DyadicInterval precision := ⟨985438900223535865014739601324176536564063382345, 989483173884649444583154341512750141457828864394⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1406825792685543838526339659362356365207402911003, scale precision, 1414774032904110256356769903186423883087902154071, scale precision,
    0, 128, 0, 128, ⟨-55724821528167684566426374060211325899562502135, -55724821528167684566426374060211325899560404982⟩, ⟨-47490913435521581872463174164197787918765244181, -47490913435521581872463174164197787918763147028⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨47505507071657740518735821235696738414842784502, 53211713690413505970693577539315862056912531908⟩
def wholeBExp : DyadicInterval precision := ⟨1358860610121550734019776036940863162167768100353, 1369513068138043369445864397783340233586296146697⟩
def wholeBLog : DyadicInterval precision := ⟨960792502499039239104543795401092339883353345369, 966302169753818284714270219284031316517556753438⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1358860610121550734019776036940863162717523914241, scale precision, 1369513068138043369445864397783340233036540332809, scale precision,
    0, 128, 0, 128, ⟨-106423427380827011941387155078631724705107525766, -106423427380827011941387155078631724705105428613⟩, ⟨-95011014143315481037471642471393476243004357424, -95011014143315481037471642471393476243002260271⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0004StableWitnesses

end


