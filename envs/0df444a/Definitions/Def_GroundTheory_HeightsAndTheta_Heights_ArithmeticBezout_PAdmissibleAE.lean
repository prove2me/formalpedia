-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAE
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAdmissibleAE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:48.784605+00:00
-- url     : https://prove2.me/theorems/d67631ca-55e7-46d7-b70f-28fbeac49022
-- title:
--   PAdmissible AE
-- statement:
--   Definitions and structural lemmas for PAdmissible AE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAdmissibleAE.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section
namespace AdmissibleAE
variable {n : ℕ}
def formsIn (W : Ideal (MvPolynomial (Fin n) ℂ)) : Submodule ℝ (Fin n → ℂ) where
  carrier := {u | linForm u ∈ W}
  zero_mem' := by simp [linForm]
  add_mem' := by
    intro a b ha hb
    have : linForm (a + b) = linForm a + linForm b := by
      simp [linForm, Finset.sum_add_distrib, add_mul]
    simp only [Set.mem_ofPred_eq, this] at ha hb ⊢
    exact W.add_mem ha hb
  smul_mem' := by
    intro c u hu
    have : linForm (c • u) = C (c : ℂ) * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, Complex.real_smul]
    simp only [Set.mem_ofPred_eq, this] at hu ⊢
    exact W.mul_mem_left _ hu
end AdmissibleAE
end
end GroundTheory.Heights₂.Heights


