-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:02.660832+00:00
-- url     : https://prove2.me/theorems/f3bfc6f3-8e4e-429e-b2dc-8a1d1e66f75c
-- title:
--   Eq Sum Multihomogeneous Components
-- statement:
--   Definitions and structural lemmas for Eq Sum Multihomogeneous Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/EqSumMultihomogeneousComponents.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def i2bdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩
open Classical in

def i2comp (a : K → ℕ) (h : MRing ι) : MRing ι :=
  ∑ m ∈ h.support.filter (fun m => i2bdeg m = a), monomial m (coeff m h)
open Classical in
theorem coeff_i2comp (a : K → ℕ) (h : MRing ι) (m : (Σ k, ι k) →₀ ℕ) :
    coeff m (i2comp a h) = if i2bdeg m = a then coeff m h else 0 := by
  unfold i2comp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h0 : coeff m h = 0 <;> by_cases e : i2bdeg m = a <;> simp [Finset.mem_filter, mem_support_iff, h0, e]
def i2compHom (a : K → ℕ) : MRing ι →+ MRing ι where
  toFun := i2comp a
  map_zero' := by
    classical
    ext m
    rw [coeff_i2comp]
    simp
  map_add' x y := by
    classical
    ext m
    rw [coeff_add, coeff_i2comp, coeff_i2comp, coeff_i2comp, coeff_add]
    split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


