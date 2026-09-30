-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:31:51.272095+00:00
-- url     : https://prove2.me/theorems/5c324c7f-16ee-4814-95ca-f201b64a8be0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0475StableWitnesses, GeneralCK/Certificates/E8TAxisProd0476StableWitnesses, GeneralCK/Certificates/E8TAxisProd0477StableWitnesses).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q02

-- ===== source module GeneralCK.Certificates.E8TAxisProd0477StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0477StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨621425438279266372444929921138880061854681288003, 621425438279266372444929921138880061854681288004⟩
def centerDExp : DyadicInterval precision := ⟨624422127721977427615890341813457419000892162445, 624422127721977427615890341813457421199915417998⟩
def centerDLog : DyadicInterval precision := ⟨519925384247664018477884675236132695692606507204, 519925384247664018477884675236132697891629762757⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨624422127721977427615890341813457419550647976333, scale precision, 624422127721977427615890341813457420650159604110, scale precision,
    1, 128, 1, 128, ⟨-1242850876558532744889859842277760124996103774330, -1242850876558532744889859842277760124996101677177⟩, ⟨-1242850876558532744889859842277760122422623474837, -1242850876558532744889859842277760122422621377684⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨626547232273745277585281862987138854318931343553, 626547232273745277585281862987138854318931343554⟩
def centerCExp : DyadicInterval precision := ⟨620060887626260050699316767646281686900748825715, 620060887626260050699316767646281689099772081268⟩
def centerCLog : DyadicInterval precision := ⟨516866484266268447355758184945849648942281831173, 516866484266268447355758184945849651141305086726⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨620060887626260050699316767646281687450504639603, scale precision, 620060887626260050699316767646281688550016267380, scale precision,
    1, 128, 1, 128, ⟨-1253094464547490555170563725974277709933654259106, -1253094464547490555170563725974277709933652161953⟩, ⟨-1253094464547490555170563725974277707342073212263, -1253094464547490555170563725974277707342071115110⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1481947480382002029622298339662904031606947586128, 1481947480382002029622298339662904031606947586129⟩
def centerBExp : DyadicInterval precision := ⟨192335352843622699221592074717690794230717128069, 192335352843622699221592074717690796429740383622⟩
def centerBLog : DyadicInterval precision := ⟨180690724839817350545542003235157327048861067626, 180690724839817350545542003235157329247884323179⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨192335352843622699221592074717690794780472941957, scale precision, 192335352843622699221592074717690795879984569734, scale precision,
    2, 128, 2, 128, ⟨-2963894960764004059244596679325808067391334275000, -2963894960764004059244596679325808067391332177847⟩, ⟨-2963894960764004059244596679325808059036458166670, -2963894960764004059244596679325808059036456069517⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨615985792935344704096715461380744242879788980549, 626879646060933815899481326077700461408842647973⟩
def wholeDExp : DyadicInterval precision := ⟨619778890111929048152500802482413362411072053473, 629087614762237432177832619094338713110027667137⟩
def wholeDLog : DyadicInterval precision := ⟨516668475441837355502384214637433233345583580834, 523190605620864448684409715253755541203210012554⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨619778890111929048152500802482413362960827867361, scale precision, 629087614762237432177832619094338712560271853249, scale precision,
    1, 128, 1, 128, ⟨-1253759292121867631798962652155400924114066448699, -1253759292121867631798962652155400924114064351546⟩, ⟨-1231971585870689408193430922761488484482381679326, -1231971585870689408193430922761488484482379582173⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨620904496501149506561546131014710455895255192107, 632205686514054014973477281022546712202048803962⟩
def wholeCExp : DyadicInterval precision := ⟨615278084828305768807811408752816923282709577118, 624867428006533102722056543604489853515141265558⟩
def wholeCLog : DyadicInterval precision := ⟨513504530493722425503735242902309428485704225575, 520237350412988151220132185391395730375445104584⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨615278084828305768807811408752816923832465391006, scale precision, 624867428006533102722056543604489852965385451670, scale precision,
    1, 128, 1, 128, ⟨-1264411373028108029946954562045093425709961878255, -1264411373028108029946954562045093425709959781102⟩, ⟨-1241808993002299013123092262029420910504688254756, -1241808993002299013123092262029420910504686157603⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1465733897068799245219320896475733445646285359867, 1498240209165424724988809637242899970684243967137⟩
def wholeBExp : DyadicInterval precision := ⟨188094520106729574409737325373892967592335253920, 196650500815489806429002090398234948795727095187⟩
def wholeBLog : DyadicInterval precision := ⟨176938272698947761433232776198593084345124825473, 184499070308585927473511326934250296123526323135⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨188094520106729574409737325373892968142091067808, scale precision, 196650500815489806429002090398234948245971281299, scale precision,
    2, 128, 2, 128, ⟨-2996480418330849449977619274485799945640112747726, -2996480418330849449977619274485799945640110650573⟩, ⟨-2931467794137598490438641792951466887206800215236, -2931467794137598490438641792951466887206798118083⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0477StableWitnesses

end


