-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:38.121474+00:00
-- url     : https://prove2.me/theorems/ae4b6279-4134-4f26-8972-250ed3d9cd8f
-- title:
--   Algebra Map OLInjective
-- statement:
--   Definitions and structural lemmas for Algebra Map OLInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace ValPl
open IsDedekindDomain WithZero IsLocalRing
section
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
variable (L) in
open Classical in

noncomputable def addv : AddValuation L (WithTop ℤ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else (((-log (v.valuation L x) : ℤ)) : WithTop ℤ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      rw [← WithTop.coe_min, WithTop.coe_le_coe]
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      have hxy' : v.valuation L (x + y) ≠ 0 := by simpa using hxy
      have h := (v.valuation L).map_add x y
      rcases le_max_iff.mp h with h | h
      · have := (log_le_log hxy' hx').mpr h
        rw [min_le_iff]; left; omega
      · have := (log_le_log hxy' hy').mpr h
        rw [min_le_iff]; right; omega)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      simp only [hx, hy, mul_eq_zero, or_self, ite_false, map_mul, log_mul hx' hy']
      rw [← WithTop.coe_add]; congr 1; ring)
end
def PlacesOver (O L : Type*) [CommRing O] [IsLocalRing O] [Field L] [Algebra O L] :
    Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : O, 0 ≤ w (algebraMap O L x) ∧
    (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)}
section DVR
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
end DVR
end ValPl
end ReciprocityTheory.ChartRestriction.G.T0


