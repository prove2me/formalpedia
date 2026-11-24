-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:29.642204+00:00
-- url     : https://prove2.me/theorems/fa43ecf2-73d2-4a15-a59e-addd543055ce
-- title:
--   Mem Div Supp Of Div Cycle Ne Zero
-- statement:
--   Definitions and structural lemmas for Mem Div Supp Of Div Cycle Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/MultihomogeneousIdeals/MemDivSuppOfDivCycleNeZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
section DivMul
variable {R : Type*} [CommRing R]
def mulQ (V : Ideal R) (f g : R) : (R ⧸ (V ⊔ Ideal.span {g})) →ₗ[R] (R ⧸ (V ⊔ Ideal.span {f * g})) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R f) fun x hx => by
    have h : Ideal.span {f} * (V ⊔ Ideal.span {g}) ≤ V ⊔ Ideal.span {f * g} := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
      exact sup_le_sup_right (Ideal.mul_le.mpr fun a _ b hb => V.mul_mem_left a hb) _
    exact h (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hx)
theorem sup_span_mul_le (V : Ideal R) (f g : R) :
    V ⊔ Ideal.span {f * g} ≤ V ⊔ Ideal.span {f} :=
  sup_le_sup_left (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right f g)) V
end DivMul
section DivMul2
variable {R : Type*} [CommRing R]
end DivMul2
end ReciprocityTheory.ChartRestriction.G.AI.I1


