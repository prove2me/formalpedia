-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0062StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:40:48.309566+00:00
-- url     : https://prove2.me/theorems/63b81837-11ab-48c3-8ec3-7397efefe59c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0062StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0062StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0062StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0062StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨750806424999049798752938234956163650116084001297, 762876909785888165393154880160235516169744878865⟩
def wholeCExp : DyadicInterval precision := ⟨514531397025813982780993152721752415808724183542, 523100967242339682629524513379347097451596710168⟩
def wholeCLog : DyadicInterval precision := ⟨440828195206760661385960788505450107751285980299, 447152665109602019123525890115620511802318039062⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨514531397025813982780993152721752416358479997430, scale precision, 523100967242339682629524513379347096901840896280, scale precision,
    0, 512, 0, 512, ⟨-1525753819571776330786309760320471033901045702227, -1525753819571776330786309760320471033901043605074⟩, ⟨-1501612849998099597505876469912327298696195936143, -1501612849998099597505876469912327298696193838990⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1859222499772511904185765406804394030961491242428, 1894759203024597281437738693188751142905570040276⟩
def wholeBExp : DyadicInterval precision := ⟨109325097867054829211979291634075373602771238021, 114773014466603861731379503668117538736849001850⟩
def wholeBLog : DyadicInterval precision := ⟨105429275780767724443552352067922825290276493926, 110489263372212502614332650133708632698323897471⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨109325097867054829211979291634075374152527051909, scale precision, 114773014466603861731379503668117538187093187962, scale precision,
    0, 512, 0, 512, ⟨-3789518406049194562875477386377502293160496746510, -3789518406049194562875477386377502293160494649357⟩, ⟨-3718444999545023808371530813608788054922478877657, -3718444999545023808371530813608788054922476780504⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0062StableWitnesses


