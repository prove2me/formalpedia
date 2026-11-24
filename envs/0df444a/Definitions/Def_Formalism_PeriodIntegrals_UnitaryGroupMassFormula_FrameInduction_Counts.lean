-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:57.177785+00:00
-- url     : https://prove2.me/theorems/922ea6be-749e-4e10-8fab-72b6eb1c9895
-- title:
--   Counts
-- statement:
--   Definitions and structural lemmas for Counts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FrameInduction/Counts.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
namespace PI.FrameInd.CountsW
open PI.FrameInd
def extZ {n : Type*} (p : n → Prop) [DecidablePred p] : ({i // p i} → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun y i := if h : p i then y ⟨i, h⟩ else 0
  map_add' y y' := by funext i; by_cases h : p i <;> simp [h]
  map_smul' c y := by funext i; by_cases h : p i <;> simp [h]
end PI.FrameInd.CountsW


