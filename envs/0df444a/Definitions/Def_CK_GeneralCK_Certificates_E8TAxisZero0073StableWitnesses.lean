-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0073StableWitnesses
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0073StableWitnesses
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:27:40.585354+00:00
-- url     : https://prove2.me/theorems/a0b45b04-3b2b-4a9b-a769-b0038dfed3fd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0073StableWitnesses` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0073StableWitnesses` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0073StableWitnesses` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0073StableWitnesses (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0073StableWitnesses.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisStableInterval

-- ===== source module GeneralCK.Certificates.E8TAxisZero0073StableWitnesses =====
section

/-! Executable primitive and denominator checks for the six positive stable
parameter evaluations in the first historical E8 t-axis cell. -/

namespace GeneralCK.Certificates.E8TAxisZero0073StableWitnesses

open DyadicInterval E8TAxisStableInterval

set_option maxRecDepth 100000

def precision : ℕ := 160
def logTwo : DyadicInterval precision := ⟨1013035739299659071135698605846798550487025271590, 1013035739299659071135698605846798552686048527143⟩
def logTwoWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem logTwo_checked :
    logBoxCheck (ofInt precision 2) logTwo logTwoWitness = true := by decide

def centerDAlpha : DyadicInterval precision := ⟨632348540951967311680475479396950834210417986731, 632348540951967311680475479396950834210417986732⟩
def centerDExp : DyadicInterval precision := ⟨615157815904934041673261697075548683721928749060, 615157815904934041673261697075548685920952004613⟩
def centerDLog : DyadicInterval precision := ⟨513419890646572039308129704473371304747530047246, 513419890646572039308129704473371306946553302799⟩
def centerDInput : Inputs precision := ⟨centerDAlpha, centerDExp, centerDLog, logTwo⟩
def centerDExpWitness : ExpWitness precision :=
  ⟨615157815904934041673261697075548684271684562948, scale precision, 615157815904934041673261697075548685371196190725, scale precision,
    0, 512, 0, 512, ⟨-1264697081903934623360950958793901669726955551880, -1264697081903934623360950958793901669726953454727⟩, ⟨-1264697081903934623360950958793901667114718492198, -1264697081903934623360950958793901667114716395045⟩⟩
def centerDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerDAlpha) centerDExp centerDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerDExp) centerDLog centerDLogWitness = true := by decide

def centerCAlpha : DyadicInterval precision := ⟨632539029215864159943307696716124840714804548188, 632539029215864159943307696716124840714804548189⟩
def centerCExp : DyadicInterval precision := ⟨614997480713057483937382074919114649441891553658, 614997480713057483937382074919114651640914809211⟩
def centerCLog : DyadicInterval precision := ⟨513307046341908969661656930205502364641858866472, 513307046341908969661656930205502366840882122025⟩
def centerCInput : Inputs precision := ⟨centerCAlpha, centerCExp, centerCLog, logTwo⟩
def centerCExpWitness : ExpWitness precision :=
  ⟨614997480713057483937382074919114649991647367546, scale precision, 614997480713057483937382074919114651091158995323, scale precision,
    0, 512, 0, 512, ⟨-1265078058431728319886615393432249682736069191256, -1265078058431728319886615393432249682736067094103⟩, ⟨-1265078058431728319886615393432249680123151098653, -1265078058431728319886615393432249680123149001500⟩⟩
def centerCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerCAlpha) centerCExp centerCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerCExp) centerCLog centerCLogWitness = true := by decide

def centerBAlpha : DyadicInterval precision := ⟨1506765763606623212861368774261080471379868926643, 1506765763606623212861368774261080471379868926644⟩
def centerBExp : DyadicInterval precision := ⟨185912802657785673210363626533128461049345070891, 185912802657785673210363626533128463248368326444⟩
def centerBLog : DyadicInterval precision := ⟨175004045316287213206621006700734219480724230425, 175004045316287213206621006700734221679747485978⟩
def centerBInput : Inputs precision := ⟨centerBAlpha, centerBExp, centerBLog, logTwo⟩
def centerBExpWitness : ExpWitness precision :=
  ⟨185912802657785673210363626533128461599100884779, scale precision, 185912802657785673210363626533128462698612512556, scale precision,
    0, 512, 0, 512, ⟨-3013531527213246425722737548522160947081490877224, -3013531527213246425722737548522160947081488780071⟩, ⟨-3013531527213246425722737548522160938437986926512, -3013531527213246425722737548522160938437984829359⟩⟩
def centerBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem centerB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul centerBAlpha) centerBExp centerBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add centerBExp) centerBLog centerBLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408842647972, 637832247480472324939326434952621888088060941845⟩
def wholeDExp : DyadicInterval precision := ⟨610558820864912509175272747825498143969983465431, 619778890111929048152500802482413364610095309026⟩
def wholeDLog : DyadicInterval precision := ⟨510179642243321146984571771117295505605924827098, 516668475441837355502384214637433235544606836387⟩
def wholeDInput : Inputs precision := ⟨wholeDAlpha, wholeDExp, wholeDLog, logTwo⟩
def wholeDExpWitness : ExpWitness precision :=
  ⟨610558820864912509175272747825498144519739279319, scale precision, 619778890111929048152500802482413364060339495138, scale precision,
    0, 512, 0, 512, ⟨-1275664494960944649878652869905243777492079715909, -1275664494960944649878652869905243777492077618756⟩, ⟨-1253759292121867631798962652155400921521306240344, -1253759292121867631798962652155400921521304143191⟩⟩
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨626879646060933815899481326077700461408842647972, 638214276936524724655614060741713069379132445769⟩
def wholeCExp : DyadicInterval precision := ⟨610239710043427550164798603207363952337690858435, 619778890111929048152500802482413364610095309026⟩
def wholeCLog : DyadicInterval precision := ⟨509954544127679946806730822617685935793078450560, 516668475441837355502384214637433235544606836387⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨610239710043427550164798603207363952887446672323, scale precision, 619778890111929048152500802482413364060339495138, scale precision,
    0, 512, 0, 512, ⟨-1276428553873049449311228121483426140074910873092, -1276428553873049449311228121483426140074908775939⟩, ⟨-1253759292121867631798962652155400921521306240344, -1253759292121867631798962652155400921521304143191⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1490432167721794696980616209388009438020839305529, 1523176960709381972906813366267502281260654095710⟩
def wholeBExp : DyadicInterval precision := ⟨181784108770710961996236050710722836548691041392, 190115077622846987918604476073469169586896573744⟩
def wholeBLog : DyadicInterval precision := ⟨171336682323016084429662620851658148768124383402, 178727341505497326528163329779799874234248683950⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨181784108770710961996236050710722837098446855280, scale precision, 190115077622846987918604476073469169037140759856, scale precision,
    0, 512, 0, 512, ⟨-3046353921418763945813626732535004566941217160244, -3046353921418763945813626732535004566941215063091⟩, ⟨-2980864335443589393961232418776018871815455037283, -2980864335443589393961232418776018871815452940130⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBAlpha) wholeBExp wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBExp) wholeBLog wholeBLogWitness = true := by decide

#print axioms logTwo_checked
#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks

end GeneralCK.Certificates.E8TAxisZero0073StableWitnesses

end


