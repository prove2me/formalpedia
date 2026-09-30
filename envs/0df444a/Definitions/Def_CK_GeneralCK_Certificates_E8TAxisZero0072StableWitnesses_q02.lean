-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072StableWitnesses_q02
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0072StableWitnesses_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T19:08:27.120746+00:00
-- url     : https://prove2.me/theorems/ea73a41a-cf22-48a8-bea5-3e6f71ca21d0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0072StableWitnesses (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0072StableWitnesses (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0072StableWitnesses (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0072StableWitnesses (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0072StableWitnesses (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0072StableWitnesses_q01

namespace GeneralCK.Certificates.E8TAxisZero0072StableWitnesses
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
def wholeDLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDAlpha) wholeDExp wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDExp) wholeDLog wholeDLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨637832247480472324939326434952621888088060941844, 649228718111606835228787531534818497468994603744⟩
def wholeCExp : DyadicInterval precision := ⟨601110678192711313158291435371246244764827609179, 610558820864912509175272747825498146169006720984⟩
def wholeCLog : DyadicInterval precision := ⟨503500274479321981929762507552810300330354046220, 510179642243321146984571771117295507804948082651⟩
def wholeCInput : Inputs precision := ⟨wholeCAlpha, wholeCExp, wholeCLog, logTwo⟩
def wholeCExpWitness : ExpWitness precision :=
  ⟨601110678192711313158291435371246245314583423067, scale precision, 610558820864912509175272747825498145619250907096, scale precision,
    0, 512, 0, 512, ⟨-1298457436223213670457575063069636996274630996745, -1298457436223213670457575063069636996274628899592⟩, ⟨-1275664494960944649878652869905243774860166148623, -1275664494960944649878652869905243774860164051470⟩⟩
def wholeCLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCAlpha) wholeCExp wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCExp) wholeCLog wholeCLogWitness = true := by decide

def wholeBAlpha : DyadicInterval precision := ⟨1522614624326126476353155181323798227424114923756, 1555660400236567938276652742619986074567329047519⟩
def wholeBExp : DyadicInterval precision := ⟨173880385804471352621301659180749184977944837861, 181924051358533222199362926776269958639778826550⟩
def wholeBLog : DyadicInterval precision := ⟨164290328593358241285855179044268991417612355310, 171461138835500366828241253176154038651115249964⟩
def wholeBInput : Inputs precision := ⟨wholeBAlpha, wholeBExp, wholeBLog, logTwo⟩
def wholeBExpWitness : ExpWitness precision :=
  ⟨173880385804471352621301659180749185527700651749, scale precision, 181924051358533222199362926776269958090023012662, scale precision,
    0, 512, 0, 512, ⟨-3111320800473135876553305485239972153755473724935, -3111320800473135876553305485239972153755471627782⟩, ⟨-3045229248652252952706310362647596450431722929546, -3045229248652252952706310362647596450431720832393⟩⟩
def wholeBLogWitness : FastLogBoxWitness := ⟨0, 512, 0, 512⟩

end GeneralCK.Certificates.E8TAxisZero0072StableWitnesses


