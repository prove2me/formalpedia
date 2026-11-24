-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:16.256188+00:00
-- url     : https://prove2.me/theorems/ed7ae058-81f4-411f-916f-0d922167afeb
-- title:
--   Inter Red F
-- statement:
--   Definitions and structural lemmas for Inter Red F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedF.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def oneLine : HermLine ι := HermLine.ofWeight (fun _ => 1) (fun _ _ _ => rfl)
def HermLine.sqMetric (b : K → ℕ) : HermLine ι where
  a k := b k
  h z := ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ b k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    refine pow_pos (Real.sqrt_pos.mpr ?_) _
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ i))
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : ∑ i, ‖c k * z ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
      simp [mul_pow, Finset.mul_sum]
    simp only
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _), mul_pow, zpow_natCast]
variable {P J : Ideal (MRing ι)} {e : ℕ}
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
end ReciprocityTheory.ChartRestriction.G.Geo


