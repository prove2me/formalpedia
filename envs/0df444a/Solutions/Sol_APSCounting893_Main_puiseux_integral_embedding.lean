-- Prove2me | solution 1 for APSCounting893.Main.puiseux_integral_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:41:36.709194+00:00
-- url     : https://prove2.me/submissions/02522ef8-a3ac-4ce9-8b09-4896e27a2373

import Definitions.Def_APSCounting893_Main_Geometry
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open Polynomial HahnSeries
open scoped LaurentSeries RatFunc
namespace APSCounting893.Main

noncomputable def seriesValuationRing : ValuationSubring PuiseuxAmbient :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ ℂ)).valuationSubring

lemma mem_seriesValuationRing (z : PuiseuxAmbient) :
    z ∈ seriesValuationRing ↔ 0 ≤ z.orderTop := Iff.rfl

lemma orderTop_nonnegative_of_monic_root (z : PuiseuxAmbient)
    (p : Polynomial PuiseuxAmbient) (hp : p.Monic)
    (hcoeff : ∀ i, 0 ≤ (p.coeff i).orderTop) (hz : p.eval z = 0) :
    0 ≤ z.orderTop := by
  classical
  let T := seriesValuationRing.toSubring
  have hT : (↑p.coeffs : Set PuiseuxAmbient) ⊆ T := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Polynomial.mem_coeffs_iff.mp ha
    exact hcoeff i
  letI : IsFractionRing T PuiseuxAmbient :=
    inferInstanceAs (IsFractionRing seriesValuationRing PuiseuxAmbient)
  letI : IsIntegrallyClosed T := inferInstanceAs (IsIntegrallyClosed seriesValuationRing)
  have hint : IsIntegral T z := by
    refine ⟨p.toSubring T hT, (Polynomial.monic_toSubring _ _ _).mpr hp, ?_⟩
    change Polynomial.eval₂ T.subtype z (p.toSubring T hT) = 0
    rw [← Polynomial.eval_map, Polynomial.map_toSubring]
    exact hz
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hu]
  exact u.property

noncomputable def ramOneAlgHom : LaurentSeries ℂ →ₐ[ℂ] PuiseuxAmbient where
  toRingHom := HahnSeries.puiseuxRamEmb (by decide : 0 < 1)
  commutes' c := by
    simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.embDomainRingHom_C (R := ℂ)

noncomputable def rationalSeriesHom : RatFunc ℂ →ₐ[ℂ] PuiseuxAmbient where
  toRingHom := ramOneAlgHom.toRingHom.comp (algebraMap (RatFunc ℂ) (LaurentSeries ℂ))
  commutes' c := by
    change ramOneAlgHom (algebraMap (RatFunc ℂ) (LaurentSeries ℂ) (algebraMap ℂ (RatFunc ℂ) c)) = _
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ),
      ← IsScalarTower.algebraMap_apply (Polynomial ℂ) (RatFunc ℂ) (LaurentSeries ℂ)]
    have hL : algebraMap (Polynomial ℂ) (LaurentSeries ℂ) (algebraMap ℂ (Polynomial ℂ) c) =
        algebraMap ℂ (LaurentSeries ℂ) c := by
      rw [HahnSeries.algebraMap_apply',
        ← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (PowerSeries ℂ)]
      simp [HahnSeries.algebraMap_apply', HahnSeries.ofPowerSeries_C]
    rw [hL]
    exact ramOneAlgHom.commutes c

lemma rationalSeriesHom_X :
    rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) =
      HahnSeries.single (1 : ℚ) (1 : ℂ) := by
  change ramOneAlgHom (algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X) = _
  rw [RatFunc.coe_X]
  change HahnSeries.embDomain _ (HahnSeries.single (1 : ℤ) (1 : ℂ)) = _
  rw [HahnSeries.embDomain_single]
  simp [HahnSeries.ramScale]

lemma rationalSeriesHom_puiseux (r : RatFunc ℂ) :
    HahnSeries.HasRamBound 1 (rationalSeriesHom r) := by
  apply (HahnSeries.mem_puiseuxRamSubfield_iff (by decide : 0 < 1)).mp
  exact ⟨algebraMap (RatFunc ℂ) (LaurentSeries ℂ) r, rfl⟩

lemma rationalSeriesHom_unique {M : Type} [Field M] [Algebra ℂ M] [Algebra (RatFunc ℂ) M]
    [IsScalarTower ℂ (RatFunc ℂ) M] (rho : M →ₐ[ℂ] PuiseuxAmbient)
    (ht : rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : ℂ)) :
    rho.toRingHom.comp (algebraMap (RatFunc ℂ) M) = rationalSeriesHom.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
  have hpoly : (rho.toRingHom.comp (algebraMap (RatFunc ℂ) M)).comp
        (algebraMap (Polynomial ℂ) (RatFunc ℂ)) =
      rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      change rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (algebraMap ℂ (Polynomial ℂ) c))) =
        rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
      rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ),
        ← IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) M]
      exact (rho.commutes c).trans (rationalSeriesHom.commutes c).symm
    · change rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)) =
        rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)
      rw [rationalSeriesHom_X]
      exact ht
  exact fun p => RingHom.congr_fun hpoly p

lemma algebraic_image_puiseux {M : Type} [Field M] [Algebra ℂ M] [Algebra (RatFunc ℂ) M]
    [IsScalarTower ℂ (RatFunc ℂ) M] [Algebra.IsAlgebraic (RatFunc ℂ) M]
    (rho : M →ₐ[ℂ] PuiseuxAmbient)
    (ht : rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : ℂ)) (z : M) : IsPuiseux (rho z) := by
  classical
  have hz : IsIntegral (RatFunc ℂ) z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  let q := (minpoly (RatFunc ℂ) z).map rationalSeriesHom.toRingHom
  have hq : q ≠ 0 := (minpoly.monic hz).map rationalSeriesHom.toRingHom |>.ne_zero
  have hcoeff : ∀ i, HahnSeries.HasRamBound 1 (q.coeff i) := by
    intro i
    simpa [q] using rationalSeriesHom_puiseux ((minpoly (RatFunc ℂ) z).coeff i)
  have hroot : q.IsRoot (rho z) := by
    have heq := rationalSeriesHom_unique rho ht
    change q.eval (rho z) = 0
    dsimp only [q]
    rw [Polynomial.eval_map]
    rw [← heq]
    rw [← Polynomial.eval₂_map]
    change Polynomial.eval₂ rho.toRingHom (rho.toRingHom z)
      ((minpoly (RatFunc ℂ) z).map (algebraMap (RatFunc ℂ) M)) = 0
    rw [Polynomial.eval₂_at_apply]
    simpa using congrArg rho (minpoly.aeval (RatFunc ℂ) z)
  exact ⟨q.natDegree.factorial, Nat.factorial_pos _,
    (HahnSeries.mem_puiseuxRamSubfield_iff (Nat.factorial_pos _)).mpr
      (HahnSeries.hasRamBound_natDegree_factorial_of_isRoot hq hcoeff hroot)⟩

lemma polynomial_image_nonnegative {M : Type} [Field M] [Algebra ℂ M] [Algebra (RatFunc ℂ) M]
    [IsScalarTower ℂ (RatFunc ℂ) M] (rho : M →ₐ[ℂ] PuiseuxAmbient)
    (ht : rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : ℂ)) (p : Polynomial ℂ) :
    0 ≤ (rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) p))).orderTop := by
  let f : Polynomial ℂ →+* PuiseuxAmbient :=
    rho.toRingHom.comp ((algebraMap (RatFunc ℂ) M).comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)))
  have hc (c : ℂ) : f (Polynomial.C c) ∈ seriesValuationRing := by
    change rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (algebraMap ℂ (Polynomial ℂ) c))) ∈ seriesValuationRing
    rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ),
      ← IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) M, rho.commutes]
    rw [mem_seriesValuationRing]
    simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
    by_cases hc : c = 0
    · simp [hc]
    · rw [HahnSeries.orderTop_single hc]
      exact le_rfl
  have hX : f Polynomial.X ∈ seriesValuationRing := by
    change (HahnSeries.addVal ℚ ℂ) (f Polynomial.X) ≥ 0
    change 0 ≤ (f Polynomial.X).orderTop
    change 0 ≤ (rho (algebraMap (RatFunc ℂ) M
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X))).orderTop
    rw [ht]
    simp
  have hf : f p ∈ seriesValuationRing := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using seriesValuationRing.add_mem _ _ hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact seriesValuationRing.mul_mem _ _ (hc c) (seriesValuationRing.pow_mem hX n)
  exact hf

end APSCounting893.Main



open APSCounting893.Main

theorem solution (M : Type) [Field M] [Algebra ℂ M] [Algebra (RatFunc ℂ) M]
    [IsScalarTower ℂ (RatFunc ℂ) M] [IsGalois (RatFunc ℂ) M] :
    let tM := algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
    let t := HahnSeries.single (1 : ℚ) (1 : ℂ)
    (∃ rho : M →ₐ[ℂ] PuiseuxAmbient, rho tM = t ∧ ∀ z, IsPuiseux (rho z)) ∧
    (∀ rho : M →ₐ[ℂ] PuiseuxAmbient, rho tM = t → (∀ z, IsPuiseux (rho z)) →
      ∀ z : M,
        (∃ p : Polynomial (Polynomial ℂ), p.Monic ∧
          Polynomial.eval₂
            ((algebraMap (RatFunc ℂ) M).comp
              (algebraMap (Polynomial ℂ) (RatFunc ℂ))) z p = 0) →
        PuiseuxIntegral (rho z)) ∧
    (∀ z : PuiseuxAmbient, IsPuiseux z →
      (∃ p : Polynomial PuiseuxAmbient, p.Monic ∧
        (∀ i, PuiseuxIntegral (p.coeff i)) ∧ Polynomial.eval z p = 0) → PuiseuxIntegral z) := by
  classical
  dsimp only
  constructor
  · letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
    letI : Algebra (RatFunc ℂ) PuiseuxAmbient := rationalSeriesHom.toRingHom.toAlgebra
    letI : Module.IsTorsionFree (RatFunc ℂ) PuiseuxAmbient :=
      DivisionSemiring.to_moduleIsTorsionFree
    let sigma : M →ₐ[RatFunc ℂ] PuiseuxAmbient := IsAlgClosed.lift
    let rho : M →ₐ[ℂ] PuiseuxAmbient :=
      { sigma.toRingHom with
        commutes' := fun c => by
          change sigma (algebraMap ℂ M c) = algebraMap ℂ PuiseuxAmbient c
          rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) M]
          exact (sigma.commutes (algebraMap ℂ (RatFunc ℂ) c)).trans (rationalSeriesHom.commutes c) }
    have ht : rho (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)) =
        HahnSeries.single (1 : ℚ) (1 : ℂ) := by
      change sigma (algebraMap (RatFunc ℂ) M (algebraMap (Polynomial ℂ) (RatFunc ℂ) X)) = _
      rw [sigma.commutes]
      exact rationalSeriesHom_X
    exact ⟨rho, ht, algebraic_image_puiseux rho ht⟩
  · constructor
    · intro rho ht hpu z hint
      obtain ⟨p, hp, hz⟩ := hint
      refine ⟨hpu z, ?_⟩
      let f := (algebraMap (RatFunc ℂ) M).comp (algebraMap (Polynomial ℂ) (RatFunc ℂ))
      let q := p.map (rho.toRingHom.comp f)
      apply orderTop_nonnegative_of_monic_root (rho z) q
      · exact hp.map _
      · intro i
        dsimp only [q]
        rw [Polynomial.coeff_map]
        change 0 ≤ (rho (algebraMap (RatFunc ℂ) M
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.coeff i)))).orderTop
        exact polynomial_image_nonnegative rho ht (p.coeff i)
      · dsimp only [q]
        rw [Polynomial.eval_map, ← Polynomial.eval₂_map]
        change Polynomial.eval₂ rho.toRingHom (rho.toRingHom z) (p.map f) = 0
        rw [Polynomial.eval₂_at_apply, Polynomial.eval_map]
        change rho (Polynomial.eval₂ f z p) = 0
        rw [hz, map_zero]
    · intro z hpu hint
      obtain ⟨p, hp, hc, hz⟩ := hint
      exact ⟨hpu, orderTop_nonnegative_of_monic_root z p hp (fun i => (hc i).2) hz⟩
