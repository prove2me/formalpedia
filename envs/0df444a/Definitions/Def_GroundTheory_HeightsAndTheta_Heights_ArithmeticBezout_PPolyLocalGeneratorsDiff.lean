-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPolyLocalGeneratorsDiff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:40.819071+00:00
-- url     : https://prove2.me/theorems/c923bb9f-33f5-4a55-a9bc-d7a6d2f7d5fd
-- title:
--   PPoly Local Generators Diff
-- statement:
--   Definitions and structural lemmas for PPoly Local Generators Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PPolyLocalGeneratorsDiff.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPolyLocalGenerators
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
open MvPolynomial Module
noncomputable section
variable {n : ℕ}
def polyDiff (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := eval p (pderiv j f)
  map_add' f g := by ext j; simp
  map_smul' c f := by ext j; simp
def dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun w v => ∑ j, w j * v j)
    (fun w w' v => by simp [add_mul, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_assoc, Finset.mul_sum])
    (fun w v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_left_comm, Finset.mul_sum])
def tanLinPoly (p w : Fin n → ℂ) : MvPolynomial (Fin n) ℂ := ∑ j, C (w j) * (X j - C (p j))
end
end GroundTheory.Heights₂.Heights


