-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:12.357614+00:00
-- url     : https://prove2.me/theorems/a771dc00-9757-48bc-907f-57f854686c89
-- title:
--   Val Pl Wt Add Eq Zero
-- statement:
--   Definitions and structural lemmas for Val Pl Wt Add Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/PlaceSumHeights/PlaceSumStatements/PlaceSumLemmas/GaussValuationSums/ValPlWtAddEqZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
section Addv
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
      simp only [hx, hy, mul_eq_zero, or_self, if_false, map_mul, log_mul hx' hy']
      rw [← WithTop.coe_add]; congr 1; ring)
end Addv
section Places
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
def PlacesOver : Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ a : O, 0 ≤ w (algebraMap O L a) ∧
    (0 < w (algebraMap O L a) ↔ a ∈ maximalIdeal O)}
noncomputable def fres (w : AddValuation L (WithTop ℤ)) : ℕ :=
  letI := resAlg (F := F) w
  Module.finrank (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w))
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
theorem valPl_comap (Q : Ideal (integralClosure O L)) [Q.IsMaximal] :
    Q.comap (algebraMap O (integralClosure O L)) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
theorem valPl_ne_bot (Q : Ideal (integralClosure O L)) [Q.IsMaximal] : Q ≠ ⊥ := by
  intro h
  have hc := valPl_comap Q
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure O L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective O L
  rw [h, Ideal.comap_bot_of_injective _ hinj] at hc
  exact IsDiscreteValuationRing.not_a_field O hc.symm
def valPl_hv (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    HeightOneSpectrum (integralClosure O L) :=
  have := Q.2
  ⟨Q.1, Q.2.isPrime, valPl_ne_bot Q.1⟩
variable (O L) in

noncomputable def plOf (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    AddValuation L (WithTop ℤ) :=
  addv L (valPl_hv Q)
end Places
section Main
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
end Main
end PI.HtPlacesSumWork


