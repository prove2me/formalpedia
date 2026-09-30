-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0000RStableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0000RStableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:09:16.540895+00:00
-- url     : https://prove2.me/theorems/3cae7936-40b9-4fc7-beeb-c45416f625d3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses, GeneralCK.Certificates.E8TAxisProd…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0024RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0028RStableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0024RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0028RStableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0024RStableWitnesses, GeneralCK.Certificates.E8TAxisProd0028RStableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0000RStableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0023RStableWitnesses, GeneralCK/Certificates/E8TAxisProd0024RStableWitnesses, GeneralCK/Certificates/E8TAxisProd0028RStableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 3798893981423257492988718450954299577395465181⟩
def centerAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1453923564186661310665317018859587709527417053272⟩
def centerALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009241782561842849966002591658486094460586802138⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

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

def centerCAlpha : DyadicInterval precision := ⟨28337475584291120905871946103453046799811665547, 28337475584291120905871946103453046799811665548⟩
def centerCExp : DyadicInterval precision := ⟨1405911505313178891752593673021890838587723197732, 1405911505313178891752593673021890840786746453285⟩
def centerCLog : DyadicInterval precision := ⟨984972968235820479042473659614684324240962526938, 984972968235820479042473659614684326439985782491⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1405911505313178891752593673021890839137479011620, scale precision, 1405911505313178891752593673021890840236990639397, scale precision,
    0, 128, 0, 128, ⟨-56674951168582241811743892206906094171117691373, -56674951168582241811743892206906094171115594220⟩, ⟨-56674951168582241811743892206906093028131067970, -56674951168582241811743892206906093028128970817⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨52894654640312737718564223508938723181660032364, 52894654640312737718564223508938723181660032365⟩
def centerBExp : DyadicInterval precision := ⟨1359450322131803465594110234910581442617532847657, 1359450322131803465594110234910581444816556103210⟩
def centerBLog : DyadicInterval precision := ⟨961098057212024705716880693696126327979971930321, 961098057212024705716880693696126330178995185874⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1359450322131803465594110234910581443167288661545, scale precision, 1359450322131803465594110234910581444266800289322, scale precision,
    0, 128, 0, 128, ⟨-105789309280625475437128447017877446954346036430, -105789309280625475437128447017877446954343939277⟩, ⟨-105789309280625475437128447017877445772296190180, -105789309280625475437128447017877445772294093027⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

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

def wholeCAlpha : DyadicInterval precision := ⟨26278910172762769820712328120209532577634289711, 30396171800123412460251093542107771996415104710⟩
def wholeCExp : DyadicInterval precision := ⟨1401956297293647672601908456314651953388375642381, 1409877619422784131283828294378918310061570896855⟩
def wholeCLog : DyadicInterval precision := ⟨982955633057142006343070852505364091564212909948, 986993073785723638762592089261738285149719803585⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1401956297293647672601908456314651953938131456269, scale precision, 1409877619422784131283828294378918309511815082967, scale precision,
    0, 128, 0, 128, ⟨-60792343600246824920502187084215544565936870261, -60792343600246824920502187084215544565934773108⟩, ⟨-52557820345525539641424656240419064585383979017, -52557820345525539641424656240419064585381881864⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨50041379200560764912647798132580101207504646537, 55748398395908772039271160915898769668087195979⟩
def wholeBExp : DyadicInterval precision := ⟨1354151720443880771904382793509246280248816644960, 1364768781850218961742407903668732586967498710911⟩
def wholeBLog : DyadicInterval precision := ⟨958350333400393051644393092717458428055445776861, 963850893691077814713601955824195279326845008154⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1354151720443880771904382793509246280798572458848, scale precision, 1364768781850218961742407903668732586417742897023, scale precision,
    0, 128, 0, 128, ⟨-111496796791817544078542321831797539929512959512, -111496796791817544078542321831797539929510862359⟩, ⟨-100082758401121529825295596265160201826288623501, -100082758401121529825295596265160201826286526348⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0000RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3482318024844347500022322904444928295572395252, 3482318024844347500022322904444928295572395253⟩
def centerAExp : DyadicInterval precision := ⟨1454553569581723058392238696431353224119669669100, 1454553569581723058392238696431353226318692924653⟩
def centerALog : DyadicInterval precision := ⟨1009557569928173087760872372803888449827653659813, 1009557569928173087760872372803888452026676915366⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1454553569581723058392238696431353224669425482988, scale precision, 1454553569581723058392238696431353225768937110765, scale precision,
    0, 128, 0, 128, ⟨-6964636049688695000044645808889857143527710010, -6964636049688695000044645808889857143525612857⟩, ⟨-6964636049688695000044645808889856038763968154, -6964636049688695000044645808889856038761871001⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨28891726686864493073308866557218512689468036345, 28891726686864493073308866557218512689468036346⟩
def centerDExp : DyadicInterval precision := ⟨1404845570733299448806020978545363434893586848252, 1404845570733299448806020978545363437092610103805⟩
def centerDLog : DyadicInterval precision := ⟨984429567376195802766596711550261497182688044895, 984429567376195802766596711550261499381711300448⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1404845570733299448806020978545363435443342662140, scale precision, 1404845570733299448806020978545363436542854289917, scale precision,
    0, 128, 0, 128, ⟨-57783453373728986146617733114437025950864056774, -57783453373728986146617733114437025950861959621⟩, ⟨-57783453373728986146617733114437024807010185760, -57783453373728986146617733114437024807008088607⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨32375819597432700004815808104022493188494765355, 32375819597432700004815808104022493188494765356⟩
def centerCExp : DyadicInterval precision := ⟨1398163453437037582989169885855459650058315245230, 1398163453437037582989169885855459652257338500783⟩
def centerCLog : DyadicInterval precision := ⟨981018491991497947701997922685885973047102775920, 981018491991497947701997922685885975246126031473⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1398163453437037582989169885855459650608071059118, scale precision, 1398163453437037582989169885855459651707582686895, scale precision,
    0, 128, 0, 128, ⟨-64751639194865400009631616208044986951650873945, -64751639194865400009631616208044986951648776792⟩, ⟨-64751639194865400009631616208044985802330284632, -64751639194865400009631616208044985802328187479⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨61298780459010944557365344852521392116593730739, 61298780459010944557365344852521392116593730740⟩
def centerBExp : DyadicInterval precision := ⟨1343905289746916721006128262387734117420306923243, 1343905289746916721006128262387734119619330178796⟩
def centerBLog : DyadicInterval precision := ⟨953022088881302897776228336070842513938338007378, 953022088881302897776228336070842516137361262931⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1343905289746916721006128262387734117970062737131, scale precision, 1343905289746916721006128262387734119069574364908, scale precision,
    0, 128, 0, 128, ⟨-122597560918021889114730689705042784831049853605, -122597560918021889114730689705042784831047756452⟩, ⟨-122597560918021889114730689705042783635327166507, -122597560918021889114730689705042783635325069354⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3165742448647063503620071141085134670978073808, 3798893981423257492988718450954299577395465181⟩
def wholeAExp : DyadicInterval precision := ⟨1453923564186661310665317018859587707328393797719, 1455183847209450510423929547351191477780877052172⟩
def wholeALog : DyadicInterval precision := ⟨1009241782561842849966002591658486092261563546585, 1009873425488092576137085252579843092274389747387⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453923564186661310665317018859587707878149611607, scale precision, 1455183847209450510423929547351191477231121238284, scale precision,
    0, 128, 0, 128, ⟨-7597787962846514985977436901908599707413204648, -7597787962846514985977436901908599707411107495⟩, ⟨-6331484897294127007240142282170268789814576090, -6331484897294127007240142282170268789812478937⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1407130684310035281592181556628555968954183377026⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 985594243690497964310298929048384652090474380348⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨30871275121883886504471543380315675920526649136, 33880443884864586154657489466470909049962329722⟩
def wholeCExp : DyadicInterval precision := ⟨1395287580650204456423074730230928989829504728271, 1401045100758393964311190852361738772483594107541⟩
def wholeCLog : DyadicInterval precision := ⟨979547967462026938251631715868490060297698725912, 982490486653824970692824039413070258140541956648⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1395287580650204456423074730230928990379260542159, scale precision, 1401045100758393964311190852361738771933838293653, scale precision,
    0, 128, 0, 128, ⟨-67760887769729172309314978932941818675770453771, -67760887769729172309314978932941818675768356618⟩, ⟨-61742550243767773008943086760631351267576004365, -61742550243767773008943086760631351267573907212⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨58602635770181898821662589353151101542136562992, 63995409354739664946199090038659955629555415884⟩
def wholeBExp : DyadicInterval precision := ⟨1338955127168439721994813637441323868967561666052, 1348872859460053731599279250908956040444361819487⟩
def wholeBLog : DyadicInterval precision := ⟨950440979888312503733346527924088744024055038443, 955607699899585814401544643147774225289199821907⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1338955127168439721994813637441323869517317479940, scale precision, 1348872859460053731599279250908956039894606005599, scale precision,
    0, 128, 0, 128, ⟨-127990818709479329892398180077319911859183537583, -127990818709479329892398180077319911859181440430⟩, ⟨-117205271540363797643325178706302202488614608506, -117205271540363797643325178706302202488612511353⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0023RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0024RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0024RStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 2849167218250950044280193223065006085312260898⟩
def centerAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1455814397256041217437249255499380274426951865358⟩
def centerALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010189349275934740575240882696318024149327762719⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨28891726686864493073308866557218512689468036345, 28891726686864493073308866557218512689468036346⟩
def centerDExp : DyadicInterval precision := ⟨1404845570733299448806020978545363434893586848252, 1404845570733299448806020978545363437092610103805⟩
def centerDLog : DyadicInterval precision := ⟨984429567376195802766596711550261497182688044895, 984429567376195802766596711550261499381711300448⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1404845570733299448806020978545363435443342662140, scale precision, 1404845570733299448806020978545363436542854289917, scale precision,
    0, 128, 0, 128, ⟨-57783453373728986146617733114437025950864056774, -57783453373728986146617733114437025950861959621⟩, ⟨-57783453373728986146617733114437024807010185760, -57783453373728986146617733114437024807008088607⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨31742317673156053471706854483597748201101272410, 31742317673156053471706854483597748201101272411⟩
def centerCExp : DyadicInterval precision := ⟨1399376073743061330778404526245109957644537208669, 1399376073743061330778404526245109959843560464222⟩
def centerCLog : DyadicInterval precision := ⟨981638099833148392232818258933628544682050768681, 981638099833148392232818258933628546881074024234⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1399376073743061330778404526245109958194293022557, scale precision, 1399376073743061330778404526245109959293804650334, scale precision,
    0, 128, 0, 128, ⟨-63484635346312106943413708967195496976365919884, -63484635346312106943413708967195496976363822731⟩, ⟨-63484635346312106943413708967195495828041266911, -63484635346312106943413708967195495828039169758⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨60664350701943895908274812532193838400488968342, 60664350701943895908274812532193838400488968343⟩
def centerBExp : DyadicInterval precision := ⟨1345072560048415338197584206881288726431064297522, 1345072560048415338197584206881288728630087553075⟩
def centerBLog : DyadicInterval precision := ⟨953630062231040205313701479787567000636983336588, 953630062231040205313701479787567002836006592141⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1345072560048415338197584206881288726980820111410, scale precision, 1345072560048415338197584206881288728080331739187, scale precision,
    0, 128, 0, 128, ⟨-121328701403887791816549625064387677398321497476, -121328701403887791816549625064387677398319400323⟩, ⟨-121328701403887791816549625064387676203636473047, -121328701403887791816549625064387676203634375894⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1407130684310035281592181556628555968954183377026⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 985594243690497964310298929048384652090474380348⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨30237805692459661685740618735843772034829551821, 33246907903282438156649407690019560789354518786⟩
def wholeCExp : DyadicInterval precision := ⟨1396497771810909895881831475728914446763378183869, 1402260157947636484963162216733466196569549911461⟩
def wholeCLog : DyadicInterval precision := ⟨980166956721191716537059094422688474620535809983, 983110714532861567518714518882903790548499049889⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1396497771810909895881831475728914447313133997757, scale precision, 1402260157947636484963162216733466196019794097573, scale precision,
    0, 128, 0, 128, ⟨-66493815806564876313298815380039122154055810536, -66493815806564876313298815380039122154053713383⟩, ⟨-60475611384919323371481237471687543496678728212, -60475611384919323371481237471687543496676631059⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨57968316843561369459396042560216062604255734918, 63360863746962342702697993485127651995684952634⟩
def wholeBExp : DyadicInterval precision := ⟨1340118310385255731396483422015350658626993302998, 1350044239666637883354013223985990280729442368579⟩
def wholeBLog : DyadicInterval precision := ⟨951047895604627342379828868169897140353010055619, 956216735247228220778188764646695071734019103629⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1340118310385255731396483422015350659176749116886, scale precision, 1350044239666637883354013223985990280179686554691, scale precision,
    0, 128, 0, 128, ⟨-126721727493924685405395986970255304590921766561, -126721727493924685405395986970255304590919669408⟩, ⟨-115936633687122738918792085120432124613369782700, -115936633687122738918792085120432124613367685547⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0024RStableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0028RStableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0028RStableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2216017656540843594568486214625237657012954245⟩
def centerAExp : DyadicInterval precision := ⟨1457076315351450948047082186788007224970773813488, 1457076315351450948047082186788007227169797069041⟩
def centerALog : DyadicInterval precision := ⟨1010821401672838003372446069258059721789517968263, 1010821401672838003372446069258059723988541223816⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1457076315351450948047082186788007225520529627376, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-4432035313081687189136972429250475865452447731, -4432035313081687189136972429250475865450350578⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨28891726686864493073308866557218512689468036345, 28891726686864493073308866557218512689468036346⟩
def centerDExp : DyadicInterval precision := ⟨1404845570733299448806020978545363434893586848252, 1404845570733299448806020978545363437092610103805⟩
def centerDLog : DyadicInterval precision := ⟨984429567376195802766596711550261497182688044895, 984429567376195802766596711550261499381711300448⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨1404845570733299448806020978545363435443342662140, scale precision, 1404845570733299448806020978545363436542854289917, scale precision,
    0, 128, 0, 128, ⟨-57783453373728986146617733114437025950864056774, -57783453373728986146617733114437025950861959621⟩, ⟨-57783453373728986146617733114437024807010185760, -57783453373728986146617733114437024807008088607⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨31108829621349088379827857241274568617344624416, 31108829621349088379827857241274568617344624417⟩
def centerCExp : DyadicInterval precision := ⟨1400589719160132909177891218898852692901823311817, 1400589719160132909177891218898852695100846567370⟩
def centerCLog : DyadicInterval precision := ⟨982257968565562660756601713031926344871249032929, 982257968565562660756601713031926347070272288482⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨1400589719160132909177891218898852693451579125705, scale precision, 1400589719160132909177891218898852694551090753482, scale precision,
    0, 128, 0, 128, ⟨-62217659242698176759655714482549137808355098127, -62217659242698176759655714482549137808353000974⟩, ⟨-62217659242698176759655714482549136661025496690, -62217659242698176759655714482549136661023399537⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨60029947474202747129949095628972490566356783837, 60029947474202747129949095628972490566356783838⟩
def centerBExp : DyadicInterval precision := ⟨1346240795326888997301745443723736731141899927153, 1346240795326888997301745443723736733340923182706⟩
def centerBLog : DyadicInterval precision := ⟨954238285068984294799845441384944184409053010383, 954238285068984294799845441384944186608076265936⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨1346240795326888997301745443723736731691655741041, scale precision, 1346240795326888997301745443723736732791167368818, scale precision,
    0, 128, 0, 128, ⟨-120059894948405494259898191257944981729538769047, -120059894948405494259898191257944981729536671894⟩, ⟨-120059894948405494259898191257944980535890463455, -120059894948405494259898191257944980535888366302⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1899443256066344012630337314537754309230277491, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457707683773513925477741956702213446679176875042⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1011137530350683182654731711817158199758569694808⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457707683773513925477741956702213446129421061154, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-3798886512132688025260674629075508067274948598, -3798886512132688025260674629075508067272851445⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨27704057351801426546684601097727000326331977355, 30079440410711523067074041860544926828153469389⟩
def wholeDExp : DyadicInterval precision := ⟨1402564082875305177309105820725636620755742670220, 1407130684310035281592181556628555968954183377026⟩
def wholeDLog : DyadicInterval precision := ⟨983265812352629886822137551849227701825556338687, 985594243690497964310298929048384652090474380348⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨1402564082875305177309105820725636621305498484108, scale precision, 1407130684310035281592181556628555968404427563138, scale precision,
    0, 128, 0, 128, ⟨-60158880821423046134148083721089854229165250662, -60158880821423046134148083721089854229163153509⟩, ⟨-55408114703602853093369202195454000081666850032, -55408114703602853093369202195454000081664752879⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨29604349477686278840500225678485288188201714455, 32613386452068186512645484902019899271106700538⟩
def wholeCExp : DyadicInterval precision := ⟨1397708984828652127800670294526114219544144078877, 1403476243515952084979548352513547540110303879298⟩
def wholeCLog : DyadicInterval precision := ⟨980786206259123103316407863840628217789319410175, 983731203916706700343910178277001908942452415293⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨1397708984828652127800670294526114220093899892765, scale precision, 1403476243515952084979548352513547539560548065410, scale precision,
    0, 128, 0, 128, ⟨-65226772904136373025290969804039799117061596556, -65226772904136373025290969804039799117059499403⟩, ⟨-59208698955372557681000451356970575803919531025, -59208698955372557681000451356970575803917433872⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨57334023265324906204241187355924973457080023360, 62726345849935814033225453180246540326085371400⟩
def wholeBExp : DyadicInterval precision := ⟨1341282453225232093451256320206580481756154570619, 1351216590245120509540448040538346135098066204871⟩
def wholeBLog : DyadicInterval precision := ⟨951655059784641468691969283733877776036313667213, 956826021113942824039684340222150683001146903734⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨1341282453225232093451256320206580482305910384507, scale precision, 1351216590245120509540448040538346134548310390983, scale precision,
    0, 128, 0, 128, ⟨-125452691699871628066450906360493081251202234366, -125452691699871628066450906360493081251200137213⟩, ⟨-114668046530649812408482374711849946319534720866, -114668046530649812408482374711849946319532623713⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0028RStableWitnesses

end


