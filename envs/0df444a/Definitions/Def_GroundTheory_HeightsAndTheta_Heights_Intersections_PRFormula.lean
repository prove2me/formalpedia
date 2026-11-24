-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:39.426472+00:00
-- url     : https://prove2.me/theorems/c1e95345-f375-4d88-a213-94bcfc161c23
-- title:
--   PRFormula
-- statement:
--   Definitions and structural lemmas for PRFormula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PRFormula.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
namespace DiagRAux
section General
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end General
section Lines
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def halfInvLine (A B : HermLine ι) (c : K → ℤ) (hc : ∀ k, 2 * c k = -(A.a k + B.a k)) : HermLine ι where
  a := c
  h z := |A.h z * B.h z| ^ (-(1 / 2 : ℝ))
  pos z hz := Real.rpow_pos_of_pos (abs_pos.2 (mul_pos (A.pos z hz) (B.pos z hz)).ne') _
  smul c' z hc' := by
    rw [A.smul c' z hc', B.smul c' z hc']
    have hp : ∀ k, 0 < ‖c' k‖ := fun k => norm_pos_iff.2 (hc' k)
    have e1 : (∏ k, ‖c' k‖ ^ A.a k) * A.h z * ((∏ k, ‖c' k‖ ^ B.a k) * B.h z) =
        (∏ k, ‖c' k‖ ^ (A.a k + B.a k)) * (A.h z * B.h z) := by
      rw [show (∏ k, ‖c' k‖ ^ (A.a k + B.a k)) = (∏ k, ‖c' k‖ ^ A.a k) * ∏ k, ‖c' k‖ ^ B.a k by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun k _ => zpow_add₀ (hp k).ne' _ _]
      ring
    have hpos : 0 < ∏ k, ‖c' k‖ ^ (A.a k + B.a k) := Finset.prod_pos fun k _ => zpow_pos (hp k) _
    rw [e1, abs_mul, abs_of_pos hpos, Real.mul_rpow hpos.le (abs_nonneg _)]
    congr 1
    rw [← Real.finsetProd_rpow _ _ (fun k _ => (zpow_pos (hp k) _).le)]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← Real.rpow_intCast, ← Real.rpow_mul (hp k).le, ← Real.rpow_intCast]
    congr 1
    have := hc k
    push_cast
    have h2 : ((c k : ℤ) : ℝ) * 2 = -((A.a k : ℝ) + B.a k) := by exact_mod_cast (by linarith)
    linarith
end Lines
section Cycles
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open Classical in

def cycTerm (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ} (L : Fin n → HermLine ι)
    (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)
end Cycles
section Cone
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
end Cone
section Tuples
variable {α : Type*}
end Tuples
section Smooth
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
end Smooth
section FibreSquare
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
end FibreSquare
end DiagRAux
open DiagRAux
section Main
end Main
end
end GroundTheory.Heights₂.Heights.Inter


