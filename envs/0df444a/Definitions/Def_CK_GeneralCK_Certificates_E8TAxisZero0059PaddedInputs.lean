-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059PaddedInputs
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0059PaddedInputs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T21:39:59.723044+00:00
-- url     : https://prove2.me/theorems/c4da12a0-ece0-4e68-8019-9f7d4e35c119
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0059PaddedInputs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0059PaddedInputs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0059PaddedInputs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0059PaddedInputs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0059PaddedInputs.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0059PaddedInputs_part00

namespace GeneralCK.Certificates.E8TAxisZero0059PaddedInputs
open DyadicInterval E8TAxisStableInterval
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def wholeBAlpha : DyadicInterval precision := ⟨1964566720915303568265002566982811316140938345387, 2000654635874828483152190903567570468179094245703⟩
def wholeBInput : Inputs precision :=
  { E8TAxisZero0059StableWitnesses.wholeBInput with alpha := wholeBAlpha }

theorem wholeB_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeBInput.alpha)
      wholeBInput.expNegTwo E8TAxisZero0059StableWitnesses.wholeBExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeBInput.expNegTwo)
      wholeBInput.logOnePlusExp E8TAxisZero0059StableWitnesses.wholeBLogWitness = true := by decide

def wholeCAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172012299980, 798300648385302148205461270420216151660352823184⟩
def wholeCInput : Inputs precision :=
  { E8TAxisZero0059StableWitnesses.wholeCInput with alpha := wholeCAlpha }

theorem wholeC_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeCInput.alpha)
      wholeCInput.expNegTwo E8TAxisZero0059StableWitnesses.wholeCExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeCInput.expNegTwo)
      wholeCInput.logOnePlusExp E8TAxisZero0059StableWitnesses.wholeCLogWitness = true := by decide

def wholeDAlpha : DyadicInterval precision := ⟨786008954924549138888839394711577924172012299980, 797886217135535601213561462349015058648205080964⟩
def wholeDInput : Inputs precision :=
  { E8TAxisZero0059StableWitnesses.wholeDInput with alpha := wholeDAlpha }

theorem wholeD_primitive_checks :
    expBoxCheck ((ofInt precision (-2)).mul wholeDInput.alpha)
      wholeDInput.expNegTwo E8TAxisZero0059StableWitnesses.wholeDExpWitness = true ∧
    logBoxCheck ((ofInt precision 1).add wholeDInput.expNegTwo)
      wholeDInput.logOnePlusExp E8TAxisZero0059StableWitnesses.wholeDLogWitness = true := by decide

#print axioms centerB_primitive_checks
#print axioms wholeB_primitive_checks
end GeneralCK.Certificates.E8TAxisZero0059PaddedInputs


