-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:20.618494+00:00
-- url     : https://prove2.me/theorems/4565d4f8-80b8-4362-b030-0ccfc9063938
-- title:
--   Inter Div Push C
-- statement:
--   Definitions and structural lemmas for Inter Div Push C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def projOfForms {e r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w j := if h : (j : ℕ) < r then ∑ t, (L ⟨j, h⟩ t : ℂ) * w t else 0
  map_add' := by
    intro w w'
    funext j
    simp only [Pi.add_apply]
    split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c w
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [Finset.mul_sum, mul_left_comm]
end
end ReciprocityTheory.ChartRestriction.G.Geo


