-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0645StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0645StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:55:36.485068+00:00
-- url     : https://prove2.me/theorems/c950b5d2-56f7-4315-acae-393eb5402e0d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0645StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0646StableWitnesses, GeneralCK.Certificates.E8TAxisProd06…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0645StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0646StableWitnesses, GeneralCK.Certificates.E8TAxisProd0647StableWitnesses, GeneralCK.Certificates.E8TAxisProd0648StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0645StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0646StableWitnesses, GeneralCK.Certificates.E8TAxisProd0647StableWitnesses, GeneralCK.Certificates.E8TAxisProd0648StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0645StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0646StableWitnesses, GeneralCK.Certificates.E8TAxisProd0647StableWitnesses, GeneralCK.Certificates.E8TAxisProd0648StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0645StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0646StableWitnesses, GeneralCK/Certificates/E8TAxisProd0647StableWitnesses, GeneralCK/Certificates/E8TAxisProd0648StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0645StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0645StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1741156135795404262119345367673058305863553519, 1741156135795404262119345367673058305863553520⟩
def centerAExp : DyadicInterval precision := ⟨1458023470409865756601312007099833957031930691260, 1458023470409865756601312007099833959230953946813⟩
def centerALog : DyadicInterval precision := ⟨1011295620324512224091084430898450250872009997488, 1011295620324512224091084430898450253071033253041⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458023470409865756601312007099833957581686505148, scale precision, 1458023470409865756601312007099833958681198132925, scale precision,
    0, 128, 0, 128, ⟨-3482312271590808524238690735346117162795431580, -3482312271590808524238690735346117162793334427⟩, ⟨-3482312271590808524238690735346116060660879652, -3482312271590808524238690735346116060658782499⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨578305529745348302256248804406759576517080537351, 578305529745348302256248804406759576517080537352⟩
def centerDExp : DyadicInterval precision := ⟨662376618137962680502649166797816345145246286664, 662376618137962680502649166797816347344269542217⟩
def centerDLog : DyadicInterval precision := ⟨546279142756386118646189338978646827486920449598, 546279142756386118646189338978646829685943705151⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨662376618137962680502649166797816345695002100552, scale precision, 662376618137962680502649166797816346794513728329, scale precision,
    1, 128, 1, 128, ⟨-1156611059490696604512497608813519154247171459854, -1156611059490696604512497608813519154247169362701⟩, ⟨-1156611059490696604512497608813519151821152786705, -1156611059490696604512497608813519151821150689552⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨580347513475881250329437954699759447222184266680, 580347513475881250329437954699759447222184266681⟩
def centerCExp : DyadicInterval precision := ⟨660528280473997834065686580898602974891913091013, 660528280473997834065686580898602977090936346566⟩
def centerCLog : DyadicInterval precision := ⟨545006694751095343839403488705832241436099657419, 545006694751095343839403488705832243635122912972⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨660528280473997834065686580898602975441668904901, scale precision, 660528280473997834065686580898602976541180532678, scale precision,
    1, 128, 1, 128, ⟨-1160695026951762500658875909399518895660773248337, -1160695026951762500658875909399518895660771151184⟩, ⟨-1160695026951762500658875909399518893227965915535, -1160695026951762500658875909399518893227963818382⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1352400016545832112341887951213382091749260606137, 1352400016545832112341887951213382091749260606138⟩
def centerBExp : DyadicInterval precision := ⟨229641735172374234281037531593164513935748355035, 229641735172374234281037531593164516134771610588⟩
def centerBLog : DyadicInterval precision := ⟨213292171664350252275690841532355393224243898268, 213292171664350252275690841532355395423267153821⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨229641735172374234281037531593164514485504168923, scale precision, 229641735172374234281037531593164515585015796700, scale precision,
    2, 128, 2, 128, ⟨-2704800033091664224683775902426764186997315812150, -2704800033091664224683775902426764186997313714997⟩, ⟨-2704800033091664224683775902426764179999728709552, -2704800033091664224683775902426764179999726612399⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1582869063071984205522252427078437298396921978, 1899443256066344012630337314537754309230277492⟩
def wholeAExp : DyadicInterval precision := ⟨1457707683773513925477741956702213444480153619489, 1458339325360928401721230227698749082343136271522⟩
def wholeALog : DyadicInterval precision := ⟨1011137530350683182654731711817158197559546439255, 1011453727394019217297123487654775992957886515170⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1457707683773513925477741956702213445029909433377, scale precision, 1458339325360928401721230227698749081793380457634, scale precision,
    0, 128, 0, 128, ⟨-3798886512132688025260674629075509169648258520, -3798886512132688025260674629075509169646161367⟩, ⟨-3165738126143968411044504854156874045846969675, -3165738126143968411044504854156874045844872522⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨572977884517961874928161575521614457065497220141, 583646737036782134467503622221012937253099239180⟩
def wholeDExp : DyadicInterval precision := ⟨657552822402718366845230970835233705473068642680, 667223417983630662234844101180676645055775852155⟩
def wholeDLog : DyadicInterval precision := ⟨542955975091047008060968952594356691378926416678, 549610565162722028431892812520915520687805740148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨657552822402718366845230970835233706022824456568, scale precision, 667223417983630662234844101180676644506020038267, scale precision,
    1, 128, 1, 128, ⟨-1167293474073564268935007244442025875728107478292, -1167293474073564268935007244442025875728105381139⟩, ⟨-1145955769035923749856323151043228912926797613794, -1145955769035923749856323151043228912926795516641⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨574829448098859215518237886076935244653154005076, 585880152057432188418505255622762617524218951071⟩
def wholeCExp : DyadicInterval precision := ⟨655546192573611839376135802192388950215625094889, 665534959011211340744417088981921268632929985571⟩
def wholeCLog : DyadicInterval precision := ⟨541571356496125645975277697242054125011360708886, 548450873486251373841944323417891075129686547017⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨655546192573611839376135802192388950765380908777, scale precision, 665534959011211340744417088981921268083174171683, scale precision,
    1, 128, 1, 128, ⟨-1171760304114864376837010511245525236274087167778, -1171760304114864376837010511245525236274085070625⟩, ⟨-1149658896197718431036475772153870488099056139478, -1149658896197718431036475772153870488099054042325⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1336862946128872783326455698680329416807435664231, 1368022945141982234593854556912719975894408074440⟩
def wholeBExp : DyadicInterval precision := ⟨224784269102460914383776033416993710151171554777, 234576605696187466204238219259251134387419169026⟩
def wholeBLog : DyadicInterval precision := ⟨209088264536798084065466415177722833139583347383, 217550721751784476750157391975104740631259550299⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨224784269102460914383776033416993710700927368665, scale precision, 234576605696187466204238219259251133837663355138, scale precision,
    2, 128, 2, 128, ⟨-2736045890283964469187709113825439955363217778682, -2736045890283964469187709113825439955363215681529⟩, ⟨-2673725892257745566652911397360658830189684175747, -2673725892257745566652911397360658830189682078594⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0645StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0646StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0646StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨589001631572899351572124980299114401874513713575, 589001631572899351572124980299114401874513713576⟩
def centerDExp : DyadicInterval precision := ⟨652751929826838909185228475799900996561578066054, 652751929826838909185228475799900998760601321607⟩
def centerDLog : DyadicInterval precision := ⟨539641066124454758744190885645098755336345326342, 539641066124454758744190885645098757535368581895⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨652751929826838909185228475799900997111333879942, scale precision, 652751929826838909185228475799900998210845507719, scale precision,
    1, 128, 1, 128, ⟨-1178003263145798703144249960598228804979923376863, -1178003263145798703144249960598228804979921279710⟩, ⟨-1178003263145798703144249960598228802518133574591, -1178003263145798703144249960598228802518131477438⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨590680779220097312382926663808900529431099145449, 590680779220097312382926663808900529431099145450⟩
def centerCExp : DyadicInterval precision := ⟨651253733026137268820828311605999752462582105898, 651253733026137268820828311605999754661605361451⟩
def centerCLog : DyadicInterval precision := ⟨538605053567430944594931447222569875316286390102, 538605053567430944594931447222569877515309645655⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨651253733026137268820828311605999753012337919786, scale precision, 651253733026137268820828311605999754111849547563, scale precision,
    1, 128, 1, 128, ⟨-1181361558440194624765853327617801060095925890871, -1181361558440194624765853327617801060095923793718⟩, ⟨-1181361558440194624765853327617801057628472788079, -1181361558440194624765853327617801057628470690926⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1382654303624709323720654508540246961204789570527, 1382654303624709323720654508540246961204789570528⟩
def centerBExp : DyadicInterval precision := ⟨220328314998101926320244711500570585750912170762, 220328314998101926320244711500570587949935426315⟩
def centerBLog : DyadicInterval precision := ⟨205221183775932414371577033572958888082042500126, 205221183775932414371577033572958890281065755679⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨220328314998101926320244711500570586300667984650, scale precision, 220328314998101926320244711500570587400179612427, scale precision,
    2, 128, 2, 128, ⟨-2765308607249418647441309017080493926056270004046, -2765308607249418647441309017080493926056267906893⟩, ⟨-2765308607249418647441309017080493918762890375221, -2765308607249418647441309017080493918762888278068⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨583646737036782134467503622221012937253099239179, 594370338528145575810628189240163754488538282194⟩
def wholeDExp : DyadicInterval precision := ⟨647973841382699837641744325099416506198004171002, 657552822402718366845230970835233707672091898233⟩
def wholeDLog : DyadicInterval precision := ⟨536334420746670162773197764634792505120063760737, 542955975091047008060968952594356693577949672231⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨647973841382699837641744325099416506747759984890, scale precision, 657552822402718366845230970835233707122336084345, scale precision,
    1, 128, 1, 128, ⟨-1188740677056291151621256378480327510217048998869, -1188740677056291151621256378480327510217046901716⟩, ⟨-1167293474073564268935007244442025873284291575580, -1167293474073564268935007244442025873284289478427⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨585135414874183516355930465363154272349082057657, 596240975513991740820924259419889050090429034401⟩
def wholeCExp : DyadicInterval precision := ⟨646317225094759285129826668843677885928988919635, 656214626291254207620467297084032376088516616974⟩
def wholeCLog : DyadicInterval precision := ⟨535186221287046626719277367887300458176371187171, 542032736142934345829575509604221259241548045397⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨646317225094759285129826668843677886478744733523, scale precision, 656214626291254207620467297084032375538760803086, scale precision,
    1, 128, 1, 128, ⟨-1192481951027983481641848518839778101424008751850, -1192481951027983481641848518839778101424006654697⟩, ⟨-1170270829748367032711860930726308543473765417316, -1170270829748367032711860930726308543473763320163⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1366951989582410779880347492015451898315356483223, 1398441139983579138030353927920207028283471589783⟩
def wholeBExp : DyadicInterval precision := ⟨215619480823575714287486335424806045362171058384, 225113944344955153715298670981569977932275980218⟩
def wholeBLog : DyadicInterval precision := ⟨201123491835880096225141775802176241333027303299, 209373965681599239063108405400281125669979024175⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨215619480823575714287486335424806045911926872272, scale precision, 225113944344955153715298670981569977382520166330, scale precision,
    2, 128, 2, 128, ⟨-2796882279967158276060707855840414060293272754032, -2796882279967158276060707855840414060293270656879⟩, ⟨-2733903979164821559760694984030903793061548077889, -2733903979164821559760694984030903793061545980736⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0646StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0647StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0647StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨1424582033573572438591305530993584070055182816, 1424582033573572438591305530993584070055182817⟩
def centerAExp : DyadicInterval precision := ⟨1458655248650088110751137895023802507105717993838, 1458655248650088110751137895023802509304741249391⟩
def centerALog : DyadicInterval precision := ⟨1011611851563511234375923245561748361600484378174, 1011611851563511234375923245561748363799507633727⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1458655248650088110751137895023802507655473807726, scale precision, 1458655248650088110751137895023802508754985435503, scale precision,
    0, 128, 0, 128, ⟨-2849164067147144877182611061987168690940009844, -2849164067147144877182611061987168690937912691⟩, ⟨-2849164067147144877182611061987167589282818573, -2849164067147144877182611061987167589280721420⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨578305529745348302256248804406759576517080537351, 578305529745348302256248804406759576517080537352⟩
def centerDExp : DyadicInterval precision := ⟨662376618137962680502649166797816345145246286664, 662376618137962680502649166797816347344269542217⟩
def centerDLog : DyadicInterval precision := ⟨546279142756386118646189338978646827486920449598, 546279142756386118646189338978646829685943705151⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨662376618137962680502649166797816345695002100552, scale precision, 662376618137962680502649166797816346794513728329, scale precision,
    1, 128, 1, 128, ⟨-1156611059490696604512497608813519154247171459854, -1156611059490696604512497608813519154247169362701⟩, ⟨-1156611059490696604512497608813519151821152786705, -1156611059490696604512497608813519151821150689552⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨579976095720525503357809475562064181224329896292, 579976095720525503357809475562064181224329896293⟩
def centerCExp : DyadicInterval precision := ⟨660864091646353220408259499926896705061227731319, 660864091646353220408259499926896707260250986872⟩
def centerCLog : DyadicInterval precision := ⟨545237959044106090029679037965336652095149202013, 545237959044106090029679037965336654294172457566⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨660864091646353220408259499926896705610983545207, scale precision, 660864091646353220408259499926896706710495172984, scale precision,
    1, 128, 1, 128, ⟨-1159952191441051006715618951124128363664446404768, -1159952191441051006715618951124128363664444307615⟩, ⟨-1159952191441051006715618951124128361232875277553, -1159952191441051006715618951124128361232873180400⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1351867413486591413641524633189448656501009631897, 1351867413486591413641524633189448656501009631898⟩
def centerBExp : DyadicInterval precision := ⟨229809169091090868115065317646808602812859988728, 229809169091090868115065317646808605011883244281⟩
def centerBLog : DyadicInterval precision := ⟨213436862432416597481617606452027201283726009094, 213436862432416597481617606452027203482749264647⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨229809169091090868115065317646808603362615802616, scale precision, 229809169091090868115065317646808604462127430393, scale precision,
    2, 128, 2, 128, ⟨-2703734826973182827283049266378897316498264719453, -2703734826973182827283049266378897316498262622300⟩, ⟨-2703734826973182827283049266378897309505775905294, -2703734826973182827283049266378897309505773808141⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨1266295042977660303900587558721132456011189595, 1582869063071984205522252427078437298396921979⟩
def wholeAExp : DyadicInterval precision := ⟨1458339325360928401721230227698749080144113015969, 1458971240300741788424025014233787500747732609133⟩
def wholeALog : DyadicInterval precision := ⟨1011453727394019217297123487654775990758863259617, 1011769992837296815097311935000023819380660234895⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1458339325360928401721230227698749080693868829857, scale precision, 1458971240300741788424025014233787500197976795245, scale precision,
    0, 128, 0, 128, ⟨-3165738126143968411044504854156875147742815392, -3165738126143968411044504854156875147740718239⟩, ⟨-2532590085955320607801175117442264361314133481, -2532590085955320607801175117442264361312036328⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨572977884517961874928161575521614457065497220141, 583646737036782134467503622221012937253099239180⟩
def wholeDExp : DyadicInterval precision := ⟨657552822402718366845230970835233705473068642680, 667223417983630662234844101180676645055775852155⟩
def wholeDLog : DyadicInterval precision := ⟨542955975091047008060968952594356691378926416678, 549610565162722028431892812520915520687805740148⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨657552822402718366845230970835233706022824456568, scale precision, 667223417983630662234844101180676644506020038267, scale precision,
    1, 128, 1, 128, ⟨-1167293474073564268935007244442025875728107478292, -1167293474073564268935007244442025875728105381139⟩, ⟨-1145955769035923749856323151043228912926797613794, -1145955769035923749856323151043228912926795516641⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨574459005079048372291755768391354445292314880301, 585507750241977719479689728530740050759673290636⟩
def wholeCExp : DyadicInterval precision := ⟨655880354098834822646716556856326701530684926107, 665872427372279259394790663188665080370799624491⟩
def wholeCLog : DyadicInterval precision := ⟨541802026332616788080511484532265761319254309230, 548682731951537084006717931822772484936646698512⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨655880354098834822646716556856326702080440739995, scale precision, 665872427372279259394790663188665079821043810603, scale precision,
    1, 128, 1, 128, ⟨-1171015500483955438959379457061480102744371396924, -1171015500483955438959379457061480102744369299771⟩, ⟨-1148918010158096744583511536782708889377989733350, -1148918010158096744583511536782708889377987636197⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1336333289681603698866814540801674205478732348211, 1367487417561352753424375612258832862152641419935⟩
def wholeBExp : DyadicInterval precision := ⟨224949061659390323047419951717428778534687927217, 234746691102026676805667728003971512221381770819⟩
def wholeBLog : DyadicInterval precision := ⟨209231083037108268429267798889114139362688500602, 217697276096769846891834281530541988010054577306⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨224949061659390323047419951717428779084443741105, scale precision, 234746691102026676805667728003971511671625956931, scale precision,
    2, 128, 2, 128, ⟨-2734974835122705506848751224517665727877065945251, -2734974835122705506848751224517665727877063848098⟩, ⟨-2672666579363207397733629081603348407534759259304, -2672666579363207397733629081603348407534757162151⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0647StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0648StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0648StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2374304945389442440708671056104672722900487814, 2374304945389442440708671056104672722900487815⟩
def centerAExp : DyadicInterval precision := ⟨1456760733519020528598233539146530576837684754745, 1456760733519020528598233539146530579036708010298⟩
def centerALog : DyadicInterval precision := ⟨1010663362960215057194405650418097343575557659645, 1010663362960215057194405650418097345774580915198⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456760733519020528598233539146530577387440568633, scale precision, 1456760733519020528598233539146530578486952196410, scale precision,
    0, 128, 0, 128, ⟨-4748609890778884881417342112209345997346971596, -4748609890778884881417342112209345997344874443⟩, ⟨-4748609890778884881417342112209344894257076814, -4748609890778884881417342112209344894254979661⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨567663676182737085008043281595790637958622415352, 567663676182737085008043281595790637958622415353⟩
def centerDExp : DyadicInterval precision := ⟨672093324830871043359987491990956794091407910102, 672093324830871043359987491990956796290431165655⟩
def centerDLog : DyadicInterval precision := ⟨552950239283275349899356499051421616923499990001, 552950239283275349899356499051421619122523245554⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨672093324830871043359987491990956794641163723990, scale precision, 672093324830871043359987491990956795740675351767, scale precision,
    1, 128, 1, 128, ⟨-1135327352365474170016086563191581277112718282361, -1135327352365474170016086563191581277112716185208⟩, ⟨-1135327352365474170016086563191581274721773476199, -1135327352365474170016086563191581274721771379046⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨570434637876623750595498047069407980259466925942, 570434637876623750595498047069407980259466925943⟩
def centerCExp : DyadicInterval precision := ⟨669549614552105832938955560638818160957008548235, 669549614552105832938955560638818163156031803788⟩
def centerCLog : DyadicInterval precision := ⟨551206771247900190292955192232076416664226390255, 551206771247900190292955192232076418863249645808⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨669549614552105832938955560638818161506764362123, scale precision, 669549614552105832938955560638818162606275989900, scale precision,
    1, 128, 1, 128, ⟨-1140869275753247501190996094138815961718949066206, -1140869275753247501190996094138815961718946969053⟩, ⟨-1140869275753247501190996094138815959318920734720, -1140869275753247501190996094138815959318918637567⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1322993035830588980233433415021541102141514239324, 1322993035830588980233433415021541102141514239325⟩
def centerBExp : DyadicInterval precision := ⟨239071475227625255500522506329665171865931487900, 239071475227625255500522506329665174064954743453⟩
def centerBLog : DyadicInterval precision := ⟨221418803769475746887708654350085201235758465485, 221418803769475746887708654350085203434781721038⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨239071475227625255500522506329665172415687301788, scale precision, 239071475227625255500522506329665173515198929565, scale precision,
    2, 128, 2, 128, ⟨-2645986071661177960466866830043082207643819522626, -2645986071661177960466866830043082207643817425473⟩, ⟨-2645986071661177960466866830043082200922239531828, -2645986071661177960466866830043082200922237434675⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2216017656540843594568486214625237657012954244, 2532592299075639559542598685704412299858871782⟩
def wholeAExp : DyadicInterval precision := ⟨1456445219907862366338488118605723266224391715309, 1457076315351450948047082186788007227169797069041⟩
def wholeALog : DyadicInterval precision := ⟨1010505341326056445575717809135292020753352555862, 1010821401672838003372446069258059723988541223816⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1456445219907862366338488118605723266774147529197, scale precision, 1457076315351450948047082186788007226620041255153, scale precision,
    0, 128, 0, 128, ⟨-5065184598151279119085197371408825151383222183, -5065184598151279119085197371408825151381125030⟩, ⟨-4432035313081687189136972429250474762601466399, -4432035313081687189136972429250474762599369246⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨562362779591003425345044647758252905789383238157, 572977884517961874928161575521614457065497220142⟩
def wholeDExp : DyadicInterval precision := ⟨667223417983630662234844101180676642856752596602, 676986443527636285719880989929562988819692333983⟩
def wholeDLog : DyadicInterval precision := ⟨549610565162722028431892812520915518488782484595, 556298163020790248856133545839930270877081982575⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨667223417983630662234844101180676643406508410490, scale precision, 676986443527636285719880989929562988269936520095, scale precision,
    1, 128, 1, 128, ⟨-1145955769035923749856323151043228915335193363926, -1145955769035923749856323151043228915335191266773⟩, ⟨-1124725559182006850690089295516505810391935750325, -1124725559182006850690089295516505810391933653172⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨564942430804982345369665948834805982555401644699, 575941168743398398654547049140752194854652404906⟩
def wholeCExp : DyadicInterval precision := ⟨664523223671909711508073142713378976374938082836, 674600801276555767032981701719573265543683107762⟩
def wholeCLog : DyadicInterval precision := ⟨547755537715698138036627498470242770148408461537, 554666839317544591819523572458185968835220343766⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨664523223671909711508073142713378976924693896724, scale precision, 674600801276555767032981701719573264993927293874, scale precision,
    1, 128, 1, 128, ⟨-1151882337486796797309094098281504390918396817902, -1151882337486796797309094098281504390918394720749⟩, ⟨-1129884861609964690739331897669611963919775479710, -1129884861609964690739331897669611963919773382557⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1307620550225108951453861218728417427818316419908, 1338452521891654134139349306851269664059557544403⟩
def wholeBExp : DyadicInterval precision := ⟨234066894289650241005793764998220897621028797216, 244153989249496857304327678935707647294495147330⟩
def wholeBLog : DyadicInterval precision := ⟨217111440122342940053328510291414210716879487823, 225780288946381983926347977281148736343416474046⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨234066894289650241005793764998220898170784611104, scale precision, 244153989249496857304327678935707646744739333442, scale precision,
    2, 128, 2, 128, ⟨-2676905043783308268278698613702539331551763135876, -2676905043783308268278698613702539331551761038723⟩, ⟨-2615241100450217902907722437456834852345804913611, -2615241100450217902907722437456834852345802816458⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0648StableWitnesses

end


