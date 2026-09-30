-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T00:21:49.789933+00:00
-- url     : https://prove2.me/theorems/24e5bd7f-f846-4984-984d-6a86cd588d5d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd04…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK.Certificates.E8TAxisProd0475StableWitnesses, GeneralCK.Certificates.E8TAxisProd0476StableWitnesses, GeneralCK.Certificates.E8TAxisProd0477StableWitnesses) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisProd0474StableWitnesses (+3 modules: GeneralCK/Certificates/E8TAxisProd0475StableWitnesses, GeneralCK/Certificates/E8TAxisProd0476StableWitnesses, GeneralCK/Certificates/E8TAxisProd0477StableWitnesses) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisProd0474StableWitnesses__4_q01

-- ===== source module GeneralCK.Certificates.E8TAxisProd0476StableWitnesses =====
section

/-! Executable primitive and denominator checks for all eight stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisProd0476StableWitnesses

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

def centerDAlpha : DyadicInterval precision := ⟨632348540951967311680475479396950834210417986731, 632348540951967311680475479396950834210417986732⟩
def centerDExp : DyadicInterval precision := ⟨615157815904934041673261697075548683721928749060, 615157815904934041673261697075548685920952004613⟩
def centerDLog : DyadicInterval precision := ⟨513419890646572039308129704473371304747530047246, 513419890646572039308129704473371306946553302799⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨615157815904934041673261697075548684271684562948, scale precision, 615157815904934041673261697075548685371196190725, scale precision,
    1, 128, 1, 128, ⟨-1264697081903934623360950958793901669726955551880, -1264697081903934623360950958793901669726953454727⟩, ⟨-1264697081903934623360950958793901667114718492198, -1264697081903934623360950958793901667114716395045⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨637498031000176566063084854238282733675844370976, 637498031000176566063084854238282733675844370977⟩
def centerCExp : DyadicInterval precision := ⟨610838130153708908333692379123003237121415908454, 610838130153708908333692379123003239320439164007⟩
def centerCLog : DyadicInterval precision := ⟨510376636240660619251739070579457496466632276654, 510376636240660619251739070579457498665655532207⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨610838130153708908333692379123003237671171722342, scale precision, 610838130153708908333692379123003238770683350119, scale precision,
    1, 128, 1, 128, ⟨-1274996062000353132126169708476565468667044845276, -1274996062000353132126169708476565468667042748123⟩, ⟨-1274996062000353132126169708476565466036334735781, -1274996062000353132126169708476565466036332638628⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1514050110697073921257095455069784427987641860155, 1514050110697073921257095455069784427987641860156⟩
def centerBExp : DyadicInterval precision := ⟨184068773317654195566554178788417761631940248055, 184068773317654195566554178788417763830963503608⟩
def centerBLog : DyadicInterval precision := ⟨173367200748917419188480625382645038838518523175, 173367200748917419188480625382645041037541778728⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨184068773317654195566554178788417762181696061943, scale precision, 184068773317654195566554178788417763281207689720, scale precision,
    2, 128, 2, 128, ⟨-3028100221394147842514190910139568860340332721610, -3028100221394147842514190910139568860340330624457⟩, ⟨-3028100221394147842514190910139568851610236816166, -3028100221394147842514190910139568851610234719013⟩⟩
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

def wholeDAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408842647972, 637832247480472324939326434952621888088060941845⟩
def wholeDExp : DyadicInterval precision := ⟨610558820864912509175272747825498143969983465431, 619778890111929048152500802482413364610095309026⟩
def wholeDLog : DyadicInterval precision := ⟨510179642243321146984571771117295505605924827098, 516668475441837355502384214637433235544606836387⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨610558820864912509175272747825498144519739279319, scale precision, 619778890111929048152500802482413364060339495138, scale precision,
    1, 128, 1, 128, ⟨-1275664494960944649878652869905243777492079715909, -1275664494960944649878652869905243777492077618756⟩, ⟨-1253759292121867631798962652155400921521306240344, -1253759292121867631798962652155400921521304143191⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨631824790608321489077406891244306585186757880928, 643187256389327373999400012702566255441633014947⟩
def wholeCExp : DyadicInterval precision := ⟨606100943736283097014906634825296432100263227231, 615598875426161546353628580452797602548523553568⟩
def wholeCLog : DyadicInterval precision := ⟨507031947767145693047493296758041180896347525538, 513730264486242346622020607863163800197329348161⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨606100943736283097014906634825296432650019041119, scale precision, 615598875426161546353628580452797601998767739680, scale precision,
    1, 128, 1, 128, ⟨-1286374512778654747998800025405132512208902734433, -1286374512778654747998800025405132512208900637280⟩, ⟨-1263649581216642978154813782488613169068334078294, -1263649581216642978154813782488613169068331981141⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1497681896921787781698810661071464891129934665772, 1530495459705123933741161012530517214526812079568⟩
def wholeBExp : DyadicInterval precision := ⟨179972619780108543028402320872481117780310146782, 188238284025045768085716116564178618262060093233⟩
def wholeBLog : DyadicInterval precision := ⟨169724695820757069929313149600939227068980360030, 177065638445948611301324634195755713222676911129⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨179972619780108543028402320872481118330065960670, scale precision, 188238284025045768085716116564178617712304279345, scale precision,
    3, 128, 2, 128, ⟨-3060990919410247867482322025061034433518021086997, -3060990919410247867482322025061034433518018989844⟩, ⟨-2995363793843575563397621322142929777991508998207, -2995363793843575563397621322142929777991506901054⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 128, 0, 128⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerA_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisProd0476StableWitnesses

end


