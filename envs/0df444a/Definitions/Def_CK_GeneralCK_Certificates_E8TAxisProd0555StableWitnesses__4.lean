-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0555StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0555StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:37:08.373278+00:00
-- url     : https://prove2.me/theorems/ce920a77-b62b-4fb1-a118-0d3ffbd02155
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0555StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0556StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0555StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0556StableWitnesses, GeneralCK.Certificates.E8TAxisProd0557StableWitnesses, GeneralCK.Certificates.E8TAxisProd0558StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0555StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0556StableWitnesses, GeneralCK.Certificates.E8TAxisProd0557StableWitnesses, GeneralCK.Certificates.E8TAxisProd0558StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0555StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0556StableWitnesses, GeneralCK.Certificates.E8TAxisProd0557StableWitnesses, GeneralCK.Certificates.E8TAxisProd0558StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0555StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0556StableWitnesses, GeneralCK/Certificates/E8TAxisProd0557StableWitnesses, GeneralCK/Certificates/E8TAxisProd0558StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0555StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0555StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114759613, 2690879721921964209596752456793030551114759614⟩
def centerAExp : DyadicInterval precision := ⟨1456129774494643406468543322663438605390699476049, 1456129774494643406468543322663438607589722731602⟩
def centerALog : DyadicInterval precision := ⟨1010347336766062430648993258467353377680688109432, 1010347336766062430648993258467353379879711364985⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456129774494643406468543322663438605940455289937, scale precision, 1456129774494643406468543322663438607039966917714, scale precision,
    0, 128, 0, 128, ⟨-5381759443843928419193504913586061654014506435, -5381759443843928419193504913586061654012409282⟩, ⟨-5381759443843928419193504913586060550446629170, -5381759443843928419193504913586060550444532017⟩⟩
def centerALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerAAlpha) centerAExp centerAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerAExp) centerALog centerALogWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨599752983055354003753543703993878049904129928193, 599752983055354003753543703993878049904129928194⟩
def centerDExp : DyadicInterval precision := ⟨643218459949503680164771431112985722806282727100, 643218459949503680164771431112985725005305982653⟩
def centerDLog : DyadicInterval precision := ⟨533036044781290419045280039370268756967708914819, 533036044781290419045280039370268759166732170372⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨643218459949503680164771431112985723356038540988, scale precision, 643218459949503680164771431112985724455550168765, scale precision,
    1, 128, 1, 128, ⟨-1199505966110708007507087407987756101057399529178, -1199505966110708007507087407987756101057397432025⟩, ⟨-1199505966110708007507087407987756098559122280751, -1199505966110708007507087407987756098559120183598⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨602942372258977721807579590463912828113488290083, 602942372258977721807579590463912828113488290084⟩
def centerCExp : DyadicInterval precision := ⟨640417226481022831449365475230930080088708564902, 640417226481022831449365475230930082287731820455⟩
def centerCLog : DyadicInterval precision := ⟨531089593971636221755790423043090890159697200435, 531089593971636221755790423043090892358720455988⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨640417226481022831449365475230930080638464378790, scale precision, 640417226481022831449365475230930081737976006567, scale precision,
    1, 128, 1, 128, ⟨-1205884744517955443615159180927825657481580079940, -1205884744517955443615159180927825657481577982787⟩, ⟨-1205884744517955443615159180927825654972375177551, -1205884744517955443615159180927825654972373080398⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1415944199605273507570017888369893255504964547747, 1415944199605273507570017888369893255504964547748⟩
def centerBExp : DyadicInterval precision := ⟨210516288993155272453228566444760906997983163278, 210516288993155272453228566444760909197006418831⟩
def centerBLog : DyadicInterval precision := ⟨196669613457659828199846884968280012315704848274, 196669613457659828199846884968280014514728103827⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨210516288993155272453228566444760907547738977166, scale precision, 210516288993155272453228566444760908647250604943, scale precision,
    2, 128, 2, 128, ⟨-2831888399210547015140035776739786514826589776314, -2831888399210547015140035776739786514826587679161⟩, ⟨-2831888399210547015140035776739786507193270511824, -2831888399210547015140035776739786507193268414671⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 2849167218250950044280193223065006085312260898⟩
def wholeAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
def wholeALogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeA_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeAAlpha) wholeAExp wholeAExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeAExp) wholeALog wholeALogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨594370338528145575810628189240163754488538282193, 605149690269836019889894242842311313124295302838⟩
def wholeDExp : DyadicInterval precision := ⟨638485690296710810307667032247350011657984843106, 647973841382699837641744325099416508397027426555⟩
def wholeDLog : DyadicInterval precision := ⟨529745944986552956313550471423206441742828804091, 536334420746670162773197764634792507319087016290⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨638485690296710810307667032247350012207740656994, scale precision, 647973841382699837641744325099416507847271612667, scale precision,
    1, 128, 1, 128, ⟨-1210299380539672039779788485684622627506989507705, -1210299380539672039779788485684622627506987410552⟩, ⟨-1188740677056291151621256378480327507737106227057, -1188740677056291151621256378480327507737104129904⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨597364169276553689769606820790370619824847283891, 608535712406863613780026749995151366517249283175⟩
def wholeCExp : DyadicInterval precision := ⟨635534033480750035766323538988544261336008752802, 645324572272762725209018457638345262011452135478⟩
def wholeCLog : DyadicInterval precision := ⟨527690272676836317108677112656713213183248618642, 534497781939637426269575773813094698788198620085⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨635534033480750035766323538988544261885764566690, scale precision, 645324572272762725209018457638345261461696321590, scale precision,
    1, 128, 1, 128, ⟨-1217071424813727227560053499990302734298741936819, -1217071424813727227560053499990302734298739839666⟩, ⟨-1194728338553107379539213641580741238404633741060, -1194728338553107379539213641580741238404631643907⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1400065052089220568352804381582397523604702815664, 1431906225539347023523513417378235562564215287216⟩
def wholeBExp : DyadicInterval precision := ⟨205967771976471162095358347048491584854409341903, 215140852121726958652794579640541540875091651385⟩
def wholeBLog : DyadicInterval precision := ⟨192688362139709359013393414519646657483985314891, 200706338620556312021267027861196190266878609127⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨205967771976471162095358347048491585404165155791, scale precision, 215140852121726958652794579640541540325335837497, scale precision,
    2, 128, 2, 128, ⟨-2863812451078694047047026834756471129029376971979, -2863812451078694047047026834756471129029374874826⟩, ⟨-2800130104178441136705608763164795043474788106974, -2800130104178441136705608763164795043474786009821⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0555StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0556StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0556StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨592548091012701094527429175081137630155460773744, 592548091012701094527429175081137630155460773745⟩
def centerCExp : DyadicInterval precision := ⟨649591687216705453921195864223406796019104011121, 649591687216705453921195864223406798218127266674⟩
def centerCLog : DyadicInterval precision := ⟨537454878467597045506863035973286935018239046726, 537454878467597045506863035973286937217262302279⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨649591687216705453921195864223406796568859825009, scale precision, 649591687216705453921195864223406797668371452786, scale precision,
    1, 128, 1, 128, ⟨-1185096182025402189054858350162275261547805761201, -1185096182025402189054858350162275261547803664048⟩, ⟨-1185096182025402189054858350162275259074039430930, -1185096182025402189054858350162275259074037333777⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1385346939292778143554712670766280444401614329892, 1385346939292778143554712670766280444401614329893⟩
def centerBExp : DyadicInterval precision := ⟨219517953667537170920085142049210295740421803741, 219517953667537170920085142049210297939445059294⟩
def centerBLog : DyadicInterval precision := ⟨204516814211302630538078764143319449797713638905, 204516814211302630538078764143319451996736894458⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨219517953667537170920085142049210296290177617629, scale precision, 219517953667537170920085142049210297389689245406, scale precision,
    2, 128, 2, 128, ⟨-2770693878585556287109425341532560892463381457710, -2770693878585556287109425341532560892463379360557⟩, ⟨-2770693878585556287109425341532560885143077959008, -2770693878585556287109425341532560885143075861855⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨586997756611164898492153323582114889546905289670, 598113303974901217915534016505274355515745863121⟩
def wholeCExp : DyadicInterval precision := ⟨644663351918886140824961859264356222338402385757, 654544371667220581187867142016931249783168722177⟩
def wholeCLog : DyadicInterval precision := ⟨534039022548910507962908532708828212983048434144, 540879586845813069156231377071785960179087300692⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨644663351918886140824961859264356222888158199645, scale precision, 654544371667220581187867142016931249233412908289, scale precision,
    1, 128, 1, 128, ⟨-1196226607949802435831068033010548712277831689132, -1196226607949802435831068033010548712277829591979⟩, ⟨-1173995513222329796984306647164229777866287479960, -1173995513222329796984306647164229777866285382807⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1369630125216920363176883636352355366486253116408, 1401148149293055066965999826179586348532041277065⟩
def wholeBExp : DyadicInterval precision := ⟨214822212924647051705015338656991960087569379868, 224290432077221277637262214791490482481005508374⟩
def wholeBLog : DyadicInterval precision := ⟨200428559685446262723142904916507785681508936697, 208660193993179024195139108539438082272356978795⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨214822212924647051705015338656991960637325193756, scale precision, 224290432077221277637262214791490481931249694486, scale precision,
    2, 128, 2, 128, ⟨-2802296298586110133931999652359172700804241620776, -2802296298586110133931999652359172700804239523623⟩, ⟨-2739260250433840726353767272704710729390236674977, -2739260250433840726353767272704710729390234577824⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0556StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0557StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0557StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3007454792385135386557447160398116569795982507, 3007454792385135386557447160398116569795982508⟩
def centerAExp : DyadicInterval precision := ⟨1455499088168743985690617101081856958065120579782, 1455499088168743985690617101081856960264143835335⟩
def centerALog : DyadicInterval precision := ⟨1010031378851376569271247815372298287995916580825, 1010031378851376569271247815372298290194939836378⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1455499088168743985690617101081856958614876393670, scale precision, 1455499088168743985690617101081856959714388021447, scale precision,
    0, 128, 0, 128, ⟨-6014909584770270773114894320796233691616047245, -6014909584770270773114894320796233691613950092⟩, ⟨-6014909584770270773114894320796232587569979939, -6014909584770270773114894320796232587567882786⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨581833843548112633001773246340773375912309547165, 581833843548112633001773246340773375912309547166⟩
def centerCExp : DyadicInterval precision := ⟨659186146798836201619453291098058368028178264099, 659186146798836201619453291098058370227201519652⟩
def centerCLog : DyadicInterval precision := ⟨544082037129730972058693218899748118247109571797, 544082037129730972058693218899748120446132827350⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨659186146798836201619453291098058368577934077987, scale precision, 659186146798836201619453291098058369677445705764, scale precision,
    1, 128, 1, 128, ⟨-1163667687096225266003546492681546753043500463788, -1163667687096225266003546492681546753043498366635⟩, ⟨-1163667687096225266003546492681546750605739822027, -1163667687096225266003546492681546750605737724874⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1354531432098181340611259267568023669621201786202, 1354531432098181340611259267568023669621201786203⟩
def centerBExp : DyadicInterval precision := ⟨228972904117552689130194828196967138677017052217, 228972904117552689130194828196967140876040307770⟩
def centerBLog : DyadicInterval precision := ⟨212714047394051911585621408184403357977839201906, 212714047394051911585621408184403360176862457459⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨228972904117552689130194828196967139226772866105, scale precision, 228972904117552689130194828196967140326284493882, scale precision,
    2, 128, 2, 128, ⟨-2709062864196362681222518535136047342751418166612, -2709062864196362681222518535136047342751416069459⟩, ⟨-2709062864196362681222518535136047335733391075357, -2709062864196362681222518535136047335733388978204⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2849167218250950044280193223065006085312260897, 3165742448647063503620071141085134670978073809⟩
def wholeAExp : DyadicInterval precision := ⟨1455183847209450510423929547351191475581853796619, 1455814397256041217437249255499380274426951865358⟩
def wholeALog : DyadicInterval precision := ⟨1009873425488092576137085252579843090075366491834, 1010189349275934740575240882696318024149327762719⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455183847209450510423929547351191476131609610507, scale precision, 1455814397256041217437249255499380273877196051470, scale precision,
    0, 128, 0, 128, ⟨-6331484897294127007240142282170269894099816297, -6331484897294127007240142282170269894097719144⟩, ⟨-5698334436501900088560386446130011618722097206, -5698334436501900088560386446130011618720000053⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨576311872960411135781275250290339654214148110809, 587370424638666576351289549392854511831220080639⟩
def wholeCExp : DyadicInterval precision := ⟨654210652477106789434898558516562257276132945316, 664186201691213820714473875448160099047721173196⟩
def wholeCLog : DyadicInterval precision := ⟨540649076920939186129601216645292944839624428720, 547523839003961433647041148994703662726764457984⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨654210652477106789434898558516562257825888759204, scale precision, 664186201691213820714473875448160098497965359308, scale precision,
    1, 128, 1, 128, ⟨-1174740849277333152702579098785709024890591529766, -1174740849277333152702579098785709024890589432613⟩, ⟨-1152623745920822271562550500580679307218592792618, -1152623745920822271562550500580679307218590695465⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1338982582539360470879974385816609223046114525915, 1370166050926911397914080846841849263076181025221⟩
def wholeBExp : DyadicInterval precision := ⟨224125999908434273197343448791366724786119094037, 233897172054041643994244457485096481157035692911⟩
def wholeBLog : DyadicInterval precision := ⟨208517632161658141218086448271231787062713715496, 216965140084332544136277106501232775893844582289⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨224125999908434273197343448791366725335874907925, scale precision, 233897172054041643994244457485096480607279879023, scale precision,
    2, 128, 2, 128, ⟨-2740332101853822795828161693683698529737261872289, -2740332101853822795828161693683698529737259775136⟩, ⟨-2677965165078720941759948771633218442657092278631, -2677965165078720941759948771633218442657090181478⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0557StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0558StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0558StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨2690879721921964209596752456793030551114759613, 2690879721921964209596752456793030551114759614⟩
def centerAExp : DyadicInterval precision := ⟨1456129774494643406468543322663438605390699476049, 1456129774494643406468543322663438607589722731602⟩
def centerALog : DyadicInterval precision := ⟨1010347336766062430648993258467353377680688109432, 1010347336766062430648993258467353379879711364985⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1456129774494643406468543322663438605940455289937, scale precision, 1456129774494643406468543322663438607039966917714, scale precision,
    0, 128, 0, 128, ⟨-5381759443843928419193504913586061654014506435, -5381759443843928419193504913586061654012409282⟩, ⟨-5381759443843928419193504913586060550446629170, -5381759443843928419193504913586060550444532017⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨592174494336716384525605608527109171149309900455, 592174494336716384525605608527109171149309900456⟩
def centerCExp : DyadicInterval precision := ⟨649923876159839145494128488927037903713628054962, 649923876159839145494128488927037905912651310515⟩
def centerCLog : DyadicInterval precision := ⟨537684833479719738099834231193273871750174319626, 537684833479719738099834231193273873949197575179⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨649923876159839145494128488927037904263383868850, scale precision, 649923876159839145494128488927037905362895496627, scale precision,
    1, 128, 1, 128, ⟨-1184348988673432769051211217054218343534871819182, -1184348988673432769051211217054218343534869722029⟩, ⟨-1184348988673432769051211217054218341062369879793, -1184348988673432769051211217054218341062367782640⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1384808214744395507051366326324293221821967437483, 1384808214744395507051366326324293221821967437484⟩
def centerBExp : DyadicInterval precision := ⟨219679846490494726375156308642354893567811786754, 219679846490494726375156308642354895766835042307⟩
def centerBLog : DyadicInterval precision := ⟨204657559289150257813741958798242769677952546433, 204657559289150257813741958798242771876975801986⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨219679846490494726375156308642354894117567600642, scale precision, 219679846490494726375156308642354895217079228419, scale precision,
    2, 128, 2, 128, ⟨-2769616429488791014102732652648586447301390328061, -2769616429488791014102732652648586447301388230908⟩, ⟨-2769616429488791014102732652648586439986481519028, -2769616429488791014102732652648586439986479421875⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨2532592299075639559542598685704412299858871781, 2849167218250950044280193223065006085312260898⟩
def wholeAExp : DyadicInterval precision := ⟨1455814397256041217437249255499380272227928609805, 1456445219907862366338488118605723268423414970862⟩
def wholeALog : DyadicInterval precision := ⟨1010189349275934740575240882696318021950304507166, 1010505341326056445575717809135292022952375811415⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1455814397256041217437249255499380272777684423693, scale precision, 1456445219907862366338488118605723267873659156974, scale precision,
    0, 128, 0, 128, ⟨-5698334436501900088560386446130012722529043537, -5698334436501900088560386446130012722526946384⟩, ⟨-5065184598151279119085197371408824048054362095, -5065184598151279119085197371408824048052264942⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨586625155199885309584369518654946193492368951368, 597738702711983722292570871011260839992564352993⟩
def wholeCExp : DyadicInterval precision := ⟨644993907297760795738916604289247292742418610717, 654878201391149919024821096469864438052400026034⟩
def wholeCLog : DyadicInterval precision := ⟨534268382225324109892801122666003397636412940312, 541110136751081703576582452698845421733853421466⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨644993907297760795738916604289247293292174424605, scale precision, 654878201391149919024821096469864437502644212146, scale precision,
    1, 128, 1, 128, ⟨-1195477405423967444585141742022521681230829927912, -1195477405423967444585141742022521681230827830759⟩, ⟨-1173250310399770619168739037309892385757840544214, -1173250310399770619168739037309892385757838447061⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1369094298997536217987867442453591460488193929131, 1400606551798693916152074311465248844794460113010⟩
def wholeBExp : DyadicInterval precision := ⟨214981487872288050538812633139589332036561710098, 224454954324029844598477599373961063897781266113⟩
def wholeBLog : DyadicInterval precision := ⟨200567416827322955963145623872256998933311060875, 208802820005642893614716121999205343037762147989⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨214981487872288050538812633139589332586317523986, scale precision, 224454954324029844598477599373961063348025452225, scale precision,
    2, 128, 2, 128, ⟨-2801213103597387832304148622930497693326308293739, -2801213103597387832304148622930497693326306196586⟩, ⟨-2738188597995072435975734884907182917396744053154, -2738188597995072435975734884907182917396741956001⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0558StableWitnesses

end


