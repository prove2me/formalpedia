-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0066StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0066StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T20:30:04.62231+00:00
-- url     : https://prove2.me/theorems/5b9a802a-3677-4703-a997-76d58691e44d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0066StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0066StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0066StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0066StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨704837076587479092158941059188951191105662022838, 716625997303320235477651725761357209197888139371⟩
def wholeCExp : DyadicInterval precision := ⟨548149957608301623724888081959574617878244407003, 557064765387537285209117120927584104924255812884⟩
def wholeCLog : DyadicInterval precision := ⟨465483807067719270488136912617592969713335478733, 471952686082951260798866870121334520250908543212⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨548149957608301623724888081959574618428000220891, scale precision, 557064765387537285209117120927584104374499998996, scale precision,
    0, 512, 0, 512, ⟨-1433251994606640470955303451522714419861560569618, -1433251994606640470955303451522714419861558472465⟩, ⟨-1409674153174958184317882118377902380768999045198, -1409674153174958184317882118377902380768996948045⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1721617121406158624966933532531531410851325140774, 1756277128622506345972574320203850945403883756703⟩
def wholeBExp : DyadicInterval precision := ⟨132136113374318253076307810432189808254612680282, 138554428200967600586296245961158631291914150155⟩
def wholeBLog : DyadicInterval precision := ⟨126500085155101967253583616649889665524015608471, 132374405485356308080071161745818596826074513223⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨132136113374318253076307810432189808804368494170, scale precision, 138554428200967600586296245961158630742158336267, scale precision,
    0, 512, 0, 512, ⟨-3512554257245012691945148640407701896888384993121, -3512554257245012691945148640407701896888382895968⟩, ⟨-3443234242812317249933867065063062815903709841475, -3443234242812317249933867065063062815903707744322⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0066StableWitnesses


