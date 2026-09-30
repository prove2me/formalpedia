-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0525StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0525StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T18:56:47.063758+00:00
-- url     : https://prove2.me/theorems/64914af1-5dc1-4e34-8336-c9329e2bb8dd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0525StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0526StableWitnesses, GeneralCK.Certificates.E8TAxisProd05…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0525StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0526StableWitnesses, GeneralCK.Certificates.E8TAxisProd0527StableWitnesses, GeneralCK.Certificates.E8TAxisProd0528StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0525StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0526StableWitnesses, GeneralCK.Certificates.E8TAxisProd0527StableWitnesses, GeneralCK.Certificates.E8TAxisProd0528StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0525StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0526StableWitnesses, GeneralCK.Certificates.E8TAxisProd0527StableWitnesses, GeneralCK.Certificates.E8TAxisProd0528StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0525StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0526StableWitnesses, GeneralCK/Certificates/E8TAxisProd0527StableWitnesses, GeneralCK/Certificates/E8TAxisProd0528StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisProd0525StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0525StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4273758705152157645723775860095423839948701825, 4273758705152157645723775860095423839948701826⟩
def centerAExp : DyadicInterval precision := ⟨1452979066123426753084482090982379267943336487380, 1452979066123426753084482090982379270142359742933⟩
def centerALog : DyadicInterval precision := ⟨1008768229300280628272830658947964075013109562599, 1008768229300280628272830658947964077212132818152⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1452979066123426753084482090982379268493092301268, scale precision, 1452979066123426753084482090982379269592603929045, scale precision,
    0, 128, 0, 128, ⟨-8547517410304315291447551720190848232878905189, -8547517410304315291447551720190848232876808036⟩, ⟨-8547517410304315291447551720190847126917999264, -8547517410304315291447551720190847126915902111⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨583321230124475957315469143716190595647538379637, 583321230124475957315469143716190595647538379638⟩
def centerCExp : DyadicInterval precision := ⟨657845789117548736563709011862862301925367994748, 657845789117548736563709011862862304124391250301⟩
def centerCLog : DyadicInterval precision := ⟨543158018854516379154729566315647718666428793616, 543158018854516379154729566315647720865452049169⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨657845789117548736563709011862862302475123808636, scale precision, 657845789117548736563709011862862303574635436413, scale precision,
    1, 128, 1, 128, ⟨-1166642460248951914630938287432381192516441591615, -1166642460248951914630938287432381192516439494462⟩, ⟨-1166642460248951914630938287432381190073714024086, -1166642460248951914630938287432381190073711926933⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1356664451705674172221068987286604883270835939519, 1356664451705674172221068987286604883270835939520⟩
def centerBExp : DyadicInterval precision := ⟨228305519882720717001860245584019446374755370182, 228305519882720717001860245584019448573778625735⟩
def centerBLog : DyadicInterval precision := ⟨212136945689779501156043239730482968787390877245, 212136945689779501156043239730482970986414132798⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨228305519882720717001860245584019446924511184070, scale precision, 228305519882720717001860245584019448024022811847, scale precision,
    2, 128, 2, 128, ⟨-2713328903411348344442137974573209770060944045297, -2713328903411348344442137974573209770060941948144⟩, ⟨-2713328903411348344442137974573209763022401809937, -2713328903411348344442137974573209763022399712784⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4115470352964345628383522602588716836376905846, 4432047174048269527644776165804031130864675905⟩
def wholeAExp : DyadicInterval precision := ⟨1452664369350591901250217311774540048662792202314, 1453293830838237185210198542808669484539789010133⟩
def wholeALog : DyadicInterval precision := ⟨1008610412272733567070593870872814919869682069664, 1008926063354791867585944205900164502304869828050⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1452664369350591901250217311774540049212548016202, scale precision, 1453293830838237185210198542808669483990033196245, scale precision,
    0, 128, 0, 128, ⟨-8864094348096539055289552331608062814830647821, -8864094348096539055289552331608062814828550668⟩, ⟨-8230940705928691256767045205177433119894175747, -8230940705928691256767045205177433119892078594⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨577795344296361913144627987513975815860277877666, 588861763753680108366770224518431633788519099326⟩
def wholeCExp : DyadicInterval precision := ⟨652876880390815664568888885861835115539666366265, 662839228508688548736828603416588953658175877784⟩
def wholeCLog : DyadicInterval precision := ⟨539727437059653204612552191287254250804484281446, 546597443577331684892518540024019748070955134333⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨652876880390815664568888885861835116089422180153, scale precision, 662839228508688548736828603416588953108420063896, scale precision,
    1, 128, 1, 128, ⟨-1177723527507360216733540449036863268807698574065, -1177723527507360216733540449036863268807696476912⟩, ⟨-1155590688592723826289255975027951630508394053771, -1155590688592723826289255975027951630508391956618⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1341103834785148575638072842843409155928006369948, 1372310748113476323340635733260407059383944446929⟩
def wholeBExp : DyadicInterval precision := ⟨223469171758670438282322617093533927844209922253, 233219190646209564335857911345968921209797465939⟩
def wholeBLog : DyadicInterval precision := ⟨207948026826723265198468224914945064118478095111, 216380576082569187988791452167885248569331490483⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨223469171758670438282322617093533928393965736141, scale precision, 233219190646209564335857911345968920660041652051, scale precision,
    2, 128, 2, 128, ⟨-2744621496226952646681271466520814122363325571462, -2744621496226952646681271466520814122363323474309⟩, ⟨-2682207669570297151276145685686818308410889826314, -2682207669570297151276145685686818308410887729161⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0525StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0526StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0526StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨593669284667159560555129766294223775295609510204, 593669284667159560555129766294223775295609510205⟩
def centerCExp : DyadicInterval precision := ⟨648595780521555372873669730594218955644346455338, 648595780521555372873669730594218957843369710891⟩
def centerCLog : DyadicInterval precision := ⟨536765253486675517440669767737221433382517261704, 536765253486675517440669767737221435581540517257⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨648595780521555372873669730594218956194102269226, scale precision, 648595780521555372873669730594218957293613897003, scale precision,
    1, 128, 1, 128, ⟨-1187338569334319121110259532588447551830002445098, -1187338569334319121110259532588447551830000347945⟩, ⟨-1187338569334319121110259532588447549352437692876, -1187338569334319121110259532588447549352435595723⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1386963704707725194730028112495003401404876516074, 1386963704707725194730028112495003401404876516075⟩
def centerBExp : DyadicInterval precision := ⟨219032813312294016016386528305978091456345028225, 219032813312294016016386528305978093655368283778⟩
def centerBLog : DyadicInterval precision := ⟨204094965614098720517870145552195916360690202939, 204094965614098720517870145552195918559713458492⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨219032813312294016016386528305978092006100842113, scale precision, 219032813312294016016386528305978093105612469890, scale precision,
    2, 128, 2, 128, ⟨-2773927409415450389460056224990006806478012776670, -2773927409415450389460056224990006806478010679517⟩, ⟨-2773927409415450389460056224990006799141495384779, -2773927409415450389460056224990006799141493287626⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨588115960710894201778487515529925542769898258112, 599237515149752794258111248899872561107203853897⟩
def wholeCExp : DyadicInterval precision := ⟨643672343039679205184933916662793066839539384712, 653543545565438044665927929414784320433862440062⟩
def wholeCLog : DyadicInterval precision := ⟨533351183770435094611755841978205442402806593330, 540188177019184370198227144443194827607176208320⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨643672343039679205184933916662793067389295198600, scale precision, 653543545565438044665927929414784319884106626174, scale precision,
    1, 128, 1, 128, ⟨-1198475030299505588516222497799745123462666555261, -1198475030299505588516222497799745123462664458108⟩, ⟨-1176231921421788403556975031059851084310393606057, -1176231921421788403556975031059851084310391508904⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1371238200706945393711929933819565950000312779647, 1402773528170824463486737059533635358346260580044⟩
def wholeBExp : DyadicInterval precision := ⟨214344923749200940725785806934126634231476295374, 223797405754012980077677352515885812351227729486⟩
def wholeBLog : DyadicInterval precision := ⟨200012376239789832825256381899533609242005576966, 208232701077853617372567481752259519229660199308⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨214344923749200940725785806934126634781232109262, scale precision, 223797405754012980077677352515885811801471915598, scale precision,
    2, 128, 2, 128, ⟨-2805547056341648926973474119067270720441008564564, -2805547056341648926973474119067270720441006467411⟩, ⟨-2742476401413890787423859867639131896410464249093, -2742476401413890787423859867639131896410462151940⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0526StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0527StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0527StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨3957182113162240766624229437560720104187299711, 3957182113162240766624229437560720104187299712⟩
def centerAExp : DyadicInterval precision := ⟨1453608663518239684990297266292415545523124059933, 1453608663518239684990297266292415547722147315486⟩
def centerALog : DyadicInterval precision := ⟨1009083914440550911538268226967653949061006604559, 1009083914440550911538268226967653951260029860112⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1453608663518239684990297266292415546072879873821, scale precision, 1453608663518239684990297266292415547172391501598, scale precision,
    0, 128, 0, 128, ⟨-7914364226324481533248458875121440761116590109, -7914364226324481533248458875121440761114492956⟩, ⟨-7914364226324481533248458875121439655634705892, -7914364226324481533248458875121439655632608739⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨582949284285624209589585630048879407980219886394, 582949284285624209589585630048879407980219886395⟩
def centerCExp : DyadicInterval precision := ⟨658180712156905584008241447864625327142627758327, 658180712156905584008241447864625329341651013880⟩
def centerCLog : DyadicInterval precision := ⟨543388963479721474714356251142656377188542063978, 543388963479721474714356251142656379387565319531⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨658180712156905584008241447864625327692383572215, scale precision, 658180712156905584008241447864625328791895199992, scale precision,
    1, 128, 1, 128, ⟨-1165898568571248419179171260097758817181183099725, -1165898568571248419179171260097758817181181002572⟩, ⟨-1165898568571248419179171260097758814739698543008, -1165898568571248419179171260097758814739696445855⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1356131046515185588788336617446362421008481536658, 1356131046515185588788336617446362421008481536659⟩
def centerBExp : DyadicInterval precision := ⟨228472230343953814593586116701462054029874142530, 228472230343953814593586116701462056228897398083⟩
def centerBLog : DyadicInterval precision := ⟨212281125215290626675468284336481188941920899727, 212281125215290626675468284336481191140944155280⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨228472230343953814593586116701462054579629956418, scale precision, 228472230343953814593586116701462055679141584195, scale precision,
    2, 128, 2, 128, ⟨-2712262093030371177576673234892724845533667315629, -2712262093030371177576673234892724845533665218476⟩, ⟨-2712262093030371177576673234892724838500260928160, -2712262093030371177576673234892724838500258831007⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨3798893981423257492988718450954299577395465180, 4115470352964345628383522602588716836376905847⟩
def wholeAExp : DyadicInterval precision := ⟨1453293830838237185210198542808669482340765754580, 1453923564186661310665317018859587709527417053272⟩
def wholeALog : DyadicInterval precision := ⟨1008926063354791867585944205900164500105846572497, 1009241782561842849966002591658486094460586802138⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1453293830838237185210198542808669482890521568468, scale precision, 1453923564186661310665317018859587708977661239384, scale precision,
    0, 128, 0, 128, ⟨-8230940705928691256767045205177434225615544793, -8230940705928691256767045205177434225613447640⟩, ⟨-7597787962846514985977436901908598602170753227, -7597787962846514985977436901908598602168656074⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨577424378207907997554830794984037128427899521323, 588488828839898142638022082084261252748686702567⟩
def wholeCExp : DyadicInterval precision := ⟨653210157777551100129846091772951019357601663877, 663175804662254000628401359755338859015635175107⟩
def wholeCLog : DyadicInterval precision := ⟨539957787045762423527061811172151511425129797568, 546828982518759402168470322397106815571896085782⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨653210157777551100129846091772951019907357477765, scale precision, 663175804662254000628401359755338858465879361219, scale precision,
    1, 128, 1, 128, ⟨-1176977657679796285276044164168522506727405880139, -1176977657679796285276044164168522506727403782986⟩, ⟨-1154848756415815995109661589968074255644252540059, -1154848756415815995109661589968074255644250442906⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1340573370324104589807718871131856219167470062775, 1371774424720947859913237278791780016675686381313⟩
def wholeBExp : DyadicInterval precision := ⟨223633243742854821392331458969436373744830662835, 233388549890435575537849263322242548065743133873⟩
def wholeBLog : DyadicInterval precision := ⟨208090331843693480379777124013410007150366786451, 216526621638728627545102847914969812709130632464⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨223633243742854821392331458969436374294586476723, scale precision, 233388549890435575537849263322242547515987319985, scale precision,
    2, 128, 2, 128, ⟨-2743548849441895719826474557583560036944171593335, -2743548849441895719826474557583560036944169496182⟩, ⟨-2681146740648209179615437742263712434892317178615, -2681146740648209179615437742263712434892315081462⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0527StableWitnesses

end

-- ===== source module GeneralCK.Certificates.E8TAxisProd0528StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0528StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerAAlpha : DyadicInterval precision := ⟨4906913324212444341793886191975635191530054563, 4906913324212444341793886191975635191530054564⟩
def centerAExp : DyadicInterval precision := ⟨1451720686451934407431403951699999116082005297895, 1451720686451934407431403951699999118281028553448⟩
def centerALog : DyadicInterval precision := ⟨1008137063309063130766142500412726798681612460495, 1008137063309063130766142500412726800880635716048⟩
def centerAInput : Inputs precision := ⟨centerAAlpha, centerAExp, centerALog, logTwo⟩
def centerAExpWitness : ExpWitness precision :=
  ⟨1451720686451934407431403951699999116631761111783, scale precision, 1451720686451934407431403951699999117731272739560, scale precision,
    0, 128, 0, 128, ⟨-9813826648424888683587772383951270936520944858, -9813826648424888683587772383951270936518847705⟩, ⟨-9813826648424888683587772383951269829601370550, -9813826648424888683587772383951269829599273397⟩⟩
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

def centerCAlpha : DyadicInterval precision := ⟨573394344401085141358507779904307833260347908489, 573394344401085141358507779904307833260347908490⟩
def centerCExp : DyadicInterval precision := ⟨666843271134526964647535307561517938231532702115, 666843271134526964647535307561517940430555957668⟩
def centerCLog : DyadicInterval precision := ⟨549349547491603143834059740229904944599003224317, 549349547491603143834059740229904946798026479870⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨666843271134526964647535307561517938781288516003, scale precision, 666843271134526964647535307561517939880800143780, scale precision,
    1, 128, 1, 128, ⟨-1146788688802170282717015559808615667725581216810, -1146788688802170282717015559808615667725579119657⟩, ⟨-1146788688802170282717015559808615665315812514299, -1146788688802170282717015559808615665315810417146⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1327212651466846975368966930143223010928145022227, 1327212651466846975368966930143223010928145022228⟩
def centerBExp : DyadicInterval precision := ⟨237694969376914570766959971867659229248542084564, 237694969376914570766959971867659231447565340117⟩
def centerBLog : DyadicInterval precision := ⟨220235332046001125429509308159743352436453302103, 220235332046001125429509308159743354635476557656⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨237694969376914570766959971867659229798297898452, scale precision, 237694969376914570766959971867659230897809526229, scale precision,
    2, 128, 2, 128, ⟨-2654425302933693950737933860286446025236543625244, -2654425302933693950737933860286446025236541528091⟩, ⟨-2654425302933693950737933860286446018476038560821, -2654425302933693950737933860286446018476036463668⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeAAlpha : DyadicInterval precision := ⟨4748624479255801076876082777124010865681651338, 5065202303167835215808940955361609459283110735⟩
def wholeAExp : DyadicInterval precision := ⟨1451406261215048238048665418490328880814971300707, 1452035179538035812075122148102075718654446240893⟩
def wholeALog : DyadicInterval precision := ⟨1007979314346565773386485143059333172819831600857, 1008294829281404787796718047455216465384960373552⟩
def wholeAInput : Inputs precision := ⟨wholeAAlpha, wholeAExp, wholeALog, logTwo⟩
def wholeAExpWitness : ExpWitness precision :=
  ⟨1451406261215048238048665418490328881364727114595, scale precision, 1452035179538035812075122148102075718104690427005, scale precision,
    0, 128, 0, 128, ⟨-10130404606335670431617881910723219472146955901, -10130404606335670431617881910723219472144858748⟩, ⟨-9497248958511602153752165554248021178024436730, -9497248958511602153752165554248021178022339577⟩⟩
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

def wholeCAlpha : DyadicInterval precision := ⟨567894451010262947723637521760626815702547159960, 578908636169564917181082409926354638433424683696⟩
def wholeCExp : DyadicInterval precision := ⟨661830168134719800276399939772022238695983458351, 671881107849787291930214422714323230466075581346⟩
def wholeCLog : DyadicInterval precision := ⟨545903066429852830913219883894645190303661671828, 552804864506629412855800948393297088946572053354⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨661830168134719800276399939772022239245739272239, scale precision, 671881107849787291930214422714323229916319767458, scale precision,
    1, 128, 1, 128, ⟨-1157817272339129834362164819852709278080861291892, -1157817272339129834362164819852709278080859194739⟩, ⟨-1135788902020525895447275043521253630209245369527, -1135788902020525895447275043521253630209243272374⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1311816315929484659436961567433321599157552963209, 1342695833424318923104561764283477898850008086733⟩
def wholeBExp : DyadicInterval precision := ⟨232711657186532729391322261336495250105922194916, 242756142563984799299377264386521146677354820133⟩
def wholeBLog : DyadicInterval precision := ⟨215942821342552301824831957924112161978438459710, 224582044245990533872398728589104102653175744798⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨232711657186532729391322261336495250655678008804, scale precision, 242756142563984799299377264386521146127599006245, scale precision,
    2, 128, 2, 128, ⟨-2685391666848637846209123528566955801152654841676, -2685391666848637846209123528566955801152652744523⟩, ⟨-2623632631858969318873923134866643195005328636766, -2623632631858969318873923134866643195005326539613⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0528StableWitnesses

end


