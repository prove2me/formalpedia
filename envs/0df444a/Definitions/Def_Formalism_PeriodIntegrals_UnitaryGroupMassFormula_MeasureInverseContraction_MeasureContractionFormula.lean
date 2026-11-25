-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_MeasureContractionFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_MeasureContractionFormula
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:13.353031+00:00
-- url     : https://prove2.me/theorems/2ef538e6-806d-4192-9106-9ce047b14f66
-- title:
--   Measure Contraction Formula
-- statement:
--   Definitions and structural lemmas for Measure Contraction Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/MeasureContractionFormula.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_ConjSubMulVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_inv_mul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Amat_mul_inv
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_inUJ_A

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory NumberField
namespace PI.NMeasInv.UnitaryGroupMassFormula
section Inst
variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}
def wt (r : ℕ) (lam : ℝ) : Fin r → ℝ := fun b => lam ^ (r - b.val)
def Cmat (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {M | ∀ i j, ‖(M - 1) i j‖ ≤ 1}
def aUJ (hG : Gram ε e f) (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Formalism.REAL.UJ ε :=
  ⟨⟨Amat ε e f s, Amat ε e f s⁻¹, Amat_mul_inv hG s hs, Amat_inv_mul hG s hs⟩, inUJ_A hG s hs⟩
end Inst
end PI.NMeasInv.UnitaryGroupMassFormula


