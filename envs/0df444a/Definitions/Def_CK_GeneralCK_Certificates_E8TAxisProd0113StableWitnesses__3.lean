-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0113StableWitnesses__3
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0113StableWitnesses__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:54:57.823111+00:00
-- url     : https://prove2.me/theorems/83f41646-1454-44ed-a0e1-4d220ae42a00
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0113StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0114StableWitnesses, GeneralCK.Certificates.E8TAxisProd01…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0113StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0114StableWitnesses, GeneralCK.Certificates.E8TAxisProd0115StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0113StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0114StableWitnesses, GeneralCK.Certificates.E8TAxisProd0115StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0113StableWitnesses (+2 modules: GeneralCK.Certificates.E8TAxisProd0114StableWitnesses, GeneralCK.Certificates.E8TAxisProd0115StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0113StableWitnesses (+2 modules: GeneralCK/Certificates/E8TAxisProd0114StableWitnesses, GeneralCK/Certificates/E8TAxisProd0115StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0113StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0113StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 4748624479255801076876082777124010865681651339⟩
def centerAExp : DyadicInterval precision := ⟨1452035179538035812075122148102075716455422985340, 1452035179538035812075122148102075718654446240893⟩
def centerALog : DyadicInterval precision := ⟨1008294829281404787796718047455216463185937117999, 1008294829281404787796718047455216465384960373552⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452035179538035812075122148102075717005178799228, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-9497248958511602153752165554248022284704265776, -9497248958511602153752165554248022284702168623⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨433150018597706032584967812015361721770461165013, 433150018597706032584967812015361721770461165014⟩
def centerDExp : DyadicInterval precision := ⟨807928177963092639274651197161192176096781955567, 807928177963092639274651197161192178295805211120⟩
def centerDLog : DyadicInterval precision := ⟨643154536224866812603613452556143370937466856601, 643154536224866812603613452556143373136490112154⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨807928177963092639274651197161192176646537769455, scale precision, 807928177963092639274651197161192177746049397232, scale precision,
    0, 128, 0, 128, ⟨-866300037195412065169935624030723444535404130786, -866300037195412065169935624030723444535402033633⟩, ⟨-866300037195412065169935624030723442546442626421, -866300037195412065169935624030723442546440529268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨438375091290137518069549625298519207305398096048, 438375091290137518069549625298519207305398096049⟩
def centerCExp : DyadicInterval precision := ⟨802171869702486908680439586971471387947897096213, 802171869702486908680439586971471390146920351766⟩
def centerCLog : DyadicInterval precision := ⟨639442792692217392939268161531245037605464399489, 639442792692217392939268161531245039804487655042⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨802171869702486908680439586971471388497652910101, scale precision, 802171869702486908680439586971471389597164537878, scale precision,
    0, 128, 0, 128, ⟨-876750182580275036139099250597038415612414291181, -876750182580275036139099250597038415612412194028⟩, ⟨-876750182580275036139099250597038413609180190169, -876750182580275036139099250597038413609178093016⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨959794308250057769945379052537513464788642101243, 959794308250057769945379052537513464788642101244⟩
def centerBExp : DyadicInterval precision := ⟨392989885370642300422552441799005197186169916888, 392989885370642300422552441799005199385193172441⟩
def centerBLog : DyadicInterval precision := ⟨348050945554550776846158975373340592281301789954, 348050945554550776846158975373340594480325045507⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨392989885370642300422552441799005197735925730776, scale precision, 392989885370642300422552441799005198835437358553, scale precision,
    1, 128, 1, 128, ⟨-1919588616500115539890758105075026931621788308366, -1919588616500115539890758105075026931621786211213⟩, ⟨-1919588616500115539890758105075026927532782193756, -1919588616500115539890758105075026927532780096603⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4432047174048269527644776165804031130864675904, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452664369350591901250217311774540050861815457867⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008610412272733567070593870872814922068705325217⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452664369350591901250217311774540050312059643979, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-8864094348096539055289552331608061708630152947, -8864094348096539055289552331608061708628055794⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 441864642833471825996809190961403572059602547860⟩
def wholeDExp : DyadicInterval precision := ⟨798350393094904597531547569261377272814040010518, 817586731060820878424464751762154419137555379748⟩
def wholeDLog : DyadicInterval precision := ⟨636973437495070745585836635514540156039251184183, 649361398245907818978439547465799274251803053932⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨798350393094904597531547569261377273363795824406, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-883729285666943651993618381922807145125617651173, -883729285666943651993618381922807145125615554020⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨429325287008572579663595987881538496397581761005, 447458307624121207321456252854145892270757555801⟩
def wholeCExp : DyadicInterval precision := ⟨792262604856584709316786762562064946340209977933, 812167939653786128410994438555440940986139844520⟩
def wholeCLog : DyadicInterval precision := ⟨633031003164878592467946526695574811672582688954, 645882374608608025561610737769015380412713452421⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨792262604856584709316786762562064946889965791821, scale precision, 812167939653786128410994438555440940436384030632, scale precision,
    0, 128, 0, 128, ⟨-894916615248242414642912505708291785555660986911, -894916615248242414642912505708291785555658889758⟩, ⟨-858650574017145159327191975763076991805875307985, -858650574017145159327191975763076991805873210832⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨936981187970073304092208690985708409250606247125, 982867566360589560631482024090630462488363182164⟩
def wholeBExp : DyadicInterval precision := ⟨380775189387434363982461771371549768100804423169, 405452049075106252260352819774481037286650807715⟩
def wholeBLog : DyadicInterval precision := ⟨338392854239469167987722392198221512978606022694, 357839368985904470535700043977567941069252422351⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨380775189387434363982461771371549768650560237057, scale precision, 405452049075106252260352819774481036736894993827, scale precision,
    1, 128, 1, 128, ⟨-1965735132721179121262964048181260927086815056541, -1965735132721179121262964048181260927086812959388⟩, ⟨-1873962375940146608184417381971416816519551287173, -1873962375940146608184417381971416816519549190020⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0113StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0114StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0114StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨450610413097730743244362126978975884668402912586, 450610413097730743244362126978975884668402912587⟩
def centerDExp : DyadicInterval precision := ⟨788852527298295547523937279792077535251368933655, 788852527298295547523937279792077537450392189208⟩
def centerDLog : DyadicInterval precision := ⟨630817990789549768708034337561797068071575978800, 630817990789549768708034337561797070270599234353⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨788852527298295547523937279792077535801124747543, scale precision, 788852527298295547523937279792077536900636375320, scale precision,
    0, 128, 0, 128, ⟨-901220826195461486488724253957951770355335678976, -901220826195461486488724253957951770355333581823⟩, ⟨-901220826195461486488724253957951768318278068520, -901220826195461486488724253957951768318275971367⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨455170734387175735028656197326597435916225020714, 455170734387175735028656197326597435916225020715⟩
def centerCExp : DyadicInterval precision := ⟨783944945712762487392961091931155634834581693504, 783944945712762487392961091931155637033604949057⟩
def centerCLog : DyadicInterval precision := ⟨627627261585131103780743980165718725114597128187, 627627261585131103780743980165718727313620383740⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨783944945712762487392961091931155635384337507392, scale precision, 783944945712762487392961091931155636483849135169, scale precision,
    0, 128, 0, 128, ⟨-910341468774351470057312394653194872857355997583, -910341468774351470057312394653194872857353900430⟩, ⟨-910341468774351470057312394653194870807546182431, -910341468774351470057312394653194870807544085278⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1004364105186022945670307944342273829419421620691, 1004364105186022945670307944342273829419421620692⟩
def centerBExp : DyadicInterval precision := ⟨369737054472674840758227297470525650064408943906, 369737054472674840758227297470525652263432199459⟩
def centerBLog : DyadicInterval precision := ⟨329609822987099140198293507961657727005565743047, 329609822987099140198293507961657729204588998600⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨369737054472674840758227297470525650614164757794, scale precision, 369737054472674840758227297470525651713676385571, scale precision,
    1, 128, 1, 128, ⟨-2008728210372045891340615888684547661011926518020, -2008728210372045891340615888684547661011924420867⟩, ⟨-2008728210372045891340615888684547656665762061898, -2008728210372045891340615888684547656665759964745⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨441864642833471825996809190961403572059602547859, 459387967798615484561738103898747303530785179430⟩
def wholeDExp : DyadicInterval precision := ⟨779433753649515438129873373659005447292625435663, 798350393094904597531547569261377275013063266071⟩
def wholeDLog : DyadicInterval precision := ⟨624688092853175616303270580088334958317423405482, 636973437495070745585836635514540158238274439736⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨779433753649515438129873373659005447842381249551, scale precision, 798350393094904597531547569261377274463307452183, scale precision,
    0, 128, 0, 128, ⟨-918775935597230969123476207797494608092408240415, -918775935597230969123476207797494608092406143262⟩, ⟨-883729285666943651993618381922807143112794637420, -883729285666943651993618381922807143112792540267⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨446058686283385800154408068456410569105283096479, 464317520570543262685438368413322148488176723289⟩
def wholeCExp : DyadicInterval precision := ⟨774193486905237225075220857173521082813239522284, 793781495040654115179043461125939703865962970342⟩
def wholeCLog : DyadicInterval precision := ⟨621266473892704420673683486048983721089325581312, 634015628248851366627646684355155805952985758656⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨774193486905237225075220857173521083362995336172, scale precision, 793781495040654115179043461125939703316207156454, scale precision,
    0, 128, 0, 128, ⟨-928635041141086525370876736826644298014168731155, -928635041141086525370876736826644298014166634002⟩, ⟨-892117372566771600308816136912821137198362967247, -892117372566771600308816136912821137198360870094⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨981048425629993785951680320445070478956342417292, 1027945442466337676253244334030770129808762546614⟩
def wholeBExp : DyadicInterval precision := ⟨357996094801976668402723771470780132416169661223, 381724277013899774600889707398016226570146755094⟩
def wholeBLog : DyadicInterval precision := ⟨320209258854130237353084392786872700655804794001, 339145583648815250712096877657937445254953184505⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨357996094801976668402723771470780132965925475111, scale precision, 381724277013899774600889707398016226020390941206, scale precision,
    2, 128, 1, 128, ⟨-2055890884932675352506488668061540261861877501487, -2055890884932675352506488668061540261861875404334⟩, ⟨-1962096851259987571903360640890140955807844586674, -1962096851259987571903360640890140955807842489521⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0114StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0115StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0115StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4115470352964345628383522602588716836376905847⟩
def centerAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453293830838237185210198542808669484539789010133⟩
def centerALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1008926063354791867585944205900164502304869828050⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨433150018597706032584967812015361721770461165013, 433150018597706032584967812015361721770461165014⟩
def centerDExp : DyadicInterval precision := ⟨807928177963092639274651197161192176096781955567, 807928177963092639274651197161192178295805211120⟩
def centerDLog : DyadicInterval precision := ⟨643154536224866812603613452556143370937466856601, 643154536224866812603613452556143373136490112154⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨807928177963092639274651197161192176646537769455, scale precision, 807928177963092639274651197161192177746049397232, scale precision,
    0, 128, 0, 128, ⟨-866300037195412065169935624030723444535404130786, -866300037195412065169935624030723444535402033633⟩, ⟨-866300037195412065169935624030723442546442626421, -866300037195412065169935624030723442546440529268⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨437677775394546600281064377812702415753533591879, 437677775394546600281064377812702415753533591880⟩
def centerCExp : DyadicInterval precision := ⟨802937704174722885326088928610177605879115019752, 802937704174722885326088928610177608078138275305⟩
def centerCLog : DyadicInterval precision := ⟨639937156849299086777295548473147821365551819856, 639937156849299086777295548473147823564575075409⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨802937704174722885326088928610177606428870833640, scale precision, 802937704174722885326088928610177607528382461417, scale precision,
    0, 128, 0, 128, ⟨-875355550789093200562128755625404832507729949867, -875355550789093200562128755625404832507727852714⟩, ⟨-875355550789093200562128755625404830506406514804, -875355550789093200562128755625404830506404417651⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨958894796178183250227466524856674117818118946673, 958894796178183250227466524856674117818118946674⟩
def centerBExp : DyadicInterval precision := ⟨393473931087458697245828169407927160704561376708, 393473931087458697245828169407927162903584632261⟩
def centerBLog : DyadicInterval precision := ⟨348432366170670523154324688934403347210375989333, 348432366170670523154324688934403349409399244886⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨393473931087458697245828169407927161254317190596, scale precision, 393473931087458697245828169407927162353828818373, scale precision,
    1, 128, 1, 128, ⟨-1917789592356366500454933049713348237678226882292, -1917789592356366500454933049713348237678224785139⟩, ⟨-1917789592356366500454933049713348233594251001554, -1917789592356366500454933049713348233594248904401⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨424465904280623337412236094991656409259795096049, 441864642833471825996809190961403572059602547860⟩
def wholeDExp : DyadicInterval precision := ⟨798350393094904597531547569261377272814040010518, 817586731060820878424464751762154419137555379748⟩
def wholeDLog : DyadicInterval precision := ⟨636973437495070745585836635514540156039251184183, 649361398245907818978439547465799274251803053932⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨798350393094904597531547569261377273363795824406, scale precision, 817586731060820878424464751762154418587799565860, scale precision,
    0, 128, 0, 128, ⟨-883729285666943651993618381922807145125617651173, -883729285666943651993618381922807145125615554020⟩, ⟨-848931808561246674824472189983312817536858777432, -848931808561246674824472189983312817536856680279⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨428630511643972528454174557156597790389313925336, 446758396143924564664295531329901350112173885285⟩
def wholeCExp : DyadicInterval precision := ⟨793021795703973532967486569668771474398587913622, 812940491109497126172575141947222965256521559932⟩
def wholeCLog : DyadicInterval precision := ⟨633523233810714225471076050968041106150341188438, 646378881863236975591500270143725018767912030097⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨793021795703973532967486569668771474948343727510, scale precision, 812940491109497126172575141947222964706765746044, scale precision,
    0, 128, 0, 128, ⟨-893516792287849129328591062659802701237522765288, -893516792287849129328591062659802701237520668135⟩, ⟨-857261023287945056908349114313195579790279775400, -857261023287945056908349114313195579790277678247⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨936091811347084158792453157371867683459498655896, 981957793704943887900796543837743973923757106625⟩
def wholeBExp : DyadicInterval precision := ⟨381249543406319507828826343076981526270631644289, 405945813969940989796231915625078167275523205638⟩
def wholeBLog : DyadicInterval precision := ⟨338769116877203086834939915851727319244364310048, 358225850341201998654145885118158007302660573607⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨381249543406319507828826343076981526820387458177, scale precision, 405945813969940989796231915625078166725767391750, scale precision,
    1, 128, 1, 128, ⟨-1963915587409887775801593087675487949954977515948, -1963915587409887775801593087675487949954975418795⟩, ⟨-1872183622694168317584906314743735364939746463984, -1872183622694168317584906314743735364939744366831⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0115StableWitnesses

end


