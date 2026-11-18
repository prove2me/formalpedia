-- Prove2me | solution 1 for APSCounting893.Main.approximate_vanishing_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:50:53.710635+00:00
-- url     : https://prove2.me/submissions/ccef7b2b-1079-4fc3-bb69-b93002320813

import Definitions.Def_APSCounting893_Main_Geometry
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat
import Mathlib
import Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma evaluation_substitution {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) (x : Affine K n) :
    eval x (eval₂Hom MvPolynomial.C F p) = eval (evaluate F x) p := by
  have heq : (eval x).comp (eval₂Hom MvPolynomial.C F) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i; simp [evaluate]
  exact RingHom.congr_fun heq p

lemma image_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (Set.range (evaluate F)) = RingHom.ker (eval₂Hom MvPolynomial.C F) := by
  ext p
  constructor
  · intro hp
    rw [RingHom.mem_ker]
    apply MvPolynomial.funext
    intro x
    rw [evaluation_substitution]
    simpa only [map_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] using
      hp (evaluate F x) (Set.mem_range_self x)
  · intro hp y hy
    obtain ⟨x, rfl⟩ := hy
    rw [RingHom.mem_ker] at hp
    rw [aeval_def, Algebra.algebraMap_self, eval₂_id, ← evaluation_substitution, hp, map_zero]

lemma hasAPS_iff_annihilator {n m : ℕ} (F : PolynomialMap ℂ n m) :
    hasAPS F ↔ ∀ p ∈ annihilator F, eval (0 : Affine ℂ m) p = 0 := by
  unfold hasAPS imageClosure RSCapacity.zClosure
  rw [image_vanishingIdeal_eq_kernel]
  rfl

lemma isAlgSet_zeroLocus {K : Type} [Field K] {n : ℕ}
    (I : Ideal (Polynomials K n)) : RSCapacity.IsAlgSet (zeroLocus K I) := by
  refine ⟨I, ?_⟩
  ext x
  simp only [mem_zeroLocus_iff, RSCapacity.zeroSet, Set.mem_setOf_eq,
    aeval_def, Algebra.algebraMap_self, eval₂_id, SetLike.mem_coe]

lemma isAlgSet_eq_zeroLocus {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : RSCapacity.IsAlgSet X) :
    X = zeroLocus K (vanishingIdeal K X) := by
  apply Set.Subset.antisymm (zeroLocus_vanishingIdeal_le X)
  obtain ⟨S, rfl⟩ := hX
  intro x hx p hp
  have hv : p ∈ vanishingIdeal K (RSCapacity.zeroSet S) := by
    intro y hy
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hy p hp
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hx p hv

lemma irreducibleAffine_ideal_prime {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hX : IrreducibleAffine X) :
    (vanishingIdeal K X).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨x, hx⟩ := hX.1
    have hone : (1 : Polynomials K n) ∈ vanishingIdeal K X := by rw [htop]; trivial
    have := hone x hx
    simpa using this
  · intro p q hpq
    let A := RSCapacity.zeroSet ({p} : Set (Polynomials K n))
    let B := RSCapacity.zeroSet ({q} : Set (Polynomials K n))
    have hAB : X ⊆ A ∪ B := by
      intro x hx
      have hprod : eval x p * eval x q = 0 := by
        simpa only [map_mul, aeval_def, Algebra.algebraMap_self, eval₂_id] using hpq x hx
      rcases mul_eq_zero.mp hprod with hp | hq
      · left; simpa [A, RSCapacity.zeroSet] using hp
      · right; simpa [B, RSCapacity.zeroSet] using hq
    rcases hX.2.2 A B ⟨{p}, rfl⟩ ⟨{q}, rfl⟩ hAB with hA | hB
    · left
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hA hx) p (Set.mem_singleton p)
    · right
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using (hB hx) q (Set.mem_singleton q)

lemma prime_ideal_irreducibleAffine {K : Type} [Field K] {n : ℕ}
    {X : Set (Affine K n)} (hne : X.Nonempty) (hclosed : RSCapacity.IsAlgSet X)
    (hprime : (vanishingIdeal K X).IsPrime) : IrreducibleAffine X := by
  classical
  refine ⟨hne, hclosed, ?_⟩
  intro A B hA hB hAB
  by_cases hXA : X ⊆ A
  · exact Or.inl hXA
  by_cases hXB : X ⊆ B
  · exact Or.inr hXB
  obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hXA
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hXB
  rw [isAlgSet_eq_zeroLocus hA] at hxA
  rw [isAlgSet_eq_zeroLocus hB] at hyB
  simp only [mem_zeroLocus_iff, not_forall, exists_prop] at hxA hyB
  obtain ⟨p, hpA, hpx⟩ := hxA
  obtain ⟨q, hqB, hqy⟩ := hyB
  have hpq : p * q ∈ vanishingIdeal K X := by
    intro z hz
    rcases hAB hz with hzA | hzB
    · simp only [map_mul, hpA z hzA, zero_mul]
    · simp only [map_mul, hqB z hzB, mul_zero]
  rcases hprime.mem_or_mem hpq with hpX | hqX
  · exact (hpx (hpX x hx)).elim
  · exact (hqy (hqX y hy)).elim

lemma vanishingIdeal_zClosure {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    vanishingIdeal K (RSCapacity.zClosure X) = vanishingIdeal K X := by
  apply le_antisymm
  · exact vanishingIdeal_anti_mono (zeroLocus_vanishingIdeal_le X)
  · intro p hp x hx
    exact hx p hp

lemma irreducibleAffine_imageClosure {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : IrreducibleAffine (imageClosure F) := by
  apply prime_ideal_irreducibleAffine
  · exact ⟨evaluate F 0, zeroLocus_vanishingIdeal_le _ (Set.mem_range_self 0)⟩
  · exact isAlgSet_zeroLocus _
  · unfold imageClosure
    rw [vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact RingHom.ker_isPrime _

noncomputable def coordinatePullback {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Polynomials K m →+* CoordinateRing X :=
  (Ideal.Quotient.mk (vanishingIdeal K X)).comp (eval₂Hom MvPolynomial.C F)

noncomputable def coordinatePullbackAlgebra {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) :
    Algebra (Polynomials K m) (CoordinateRing X) := (coordinatePullback X F).toAlgebra

lemma finiteMorphism_module_finite {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F) :
    letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
    Module.Finite (Polynomials K m) (CoordinateRing X) := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
  have halg : algebraMap (Polynomials K m) (CoordinateRing X) = coordinatePullback X F := rfl
  obtain ⟨s, generators, hgen⟩ := hfinite
  let g : Fin s → CoordinateRing X := fun i => Ideal.Quotient.mk _ (generators i)
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [Submodule.eq_top_iff']
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨coefficients, hcoeff⟩ := hgen p
  have hz : p - ∑ i : Fin s, (eval₂Hom MvPolynomial.C F (coefficients i)) * generators i ∈
      vanishingIdeal K X := by
    intro x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
      evaluation_substitution, sub_eq_zero]
    exact hcoeff x hx
  have heq : Ideal.Quotient.mk (vanishingIdeal K X) p =
      ∑ i : Fin s, coefficients i • g i := by
    apply sub_eq_zero.mp
    have h := (Ideal.Quotient.eq_zero_iff_mem).mpr hz
    simpa only [map_sub, map_sum, map_mul, Algebra.smul_def,
      halg, coordinatePullback, RingHom.comp_apply, g] using h
  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

lemma coordinatePullback_injective_of_dominant {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m)
    (hdom : RSCapacity.zClosure (evaluate F '' X) = Set.univ) :
    Function.Injective (coordinatePullback X F) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro p hp
  have hz : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K X :=
    Ideal.Quotient.eq_zero_iff_mem.mp hp
  have hpI : p ∈ vanishingIdeal K (evaluate F '' X) := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hz x hx
  rw [Ideal.mem_bot]
  apply MvPolynomial.funext
  intro y
  have hy : y ∈ RSCapacity.zClosure (evaluate F '' X) := by rw [hdom]; trivial
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_zero] using hy p hpI

noncomputable def hahnValuationRing : ValuationSubring PuiseuxAmbient :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ ℂ)).valuationSubring

lemma constant_in_hahnValuationRing (c : ℂ) : HahnSeries.C c ∈ hahnValuationRing := by
  change 0 ≤ (HahnSeries.single (0 : ℚ) c).orderTop
  exact HahnSeries.orderTop_single_le

lemma positive_series_relation {m : ℕ} (p : Polynomials ℂ m)
    (y : Affine PuiseuxAmbient m) (hy : ∀ i, 0 < (y i).orderTop)
    (hrel : MvPolynomial.eval₂ HahnSeries.C y p = 0) :
    eval (0 : Affine ℂ m) p = 0 := by
  classical
  let V := hahnValuationRing
  let c0 : ℂ →+* V :=
    { toFun := fun c => ⟨HahnSeries.C c, constant_in_hahnValuationRing c⟩
      map_zero' := Subtype.ext (HahnSeries.C.map_zero)
      map_one' := Subtype.ext (HahnSeries.C.map_one)
      map_add' := fun a b => Subtype.ext (HahnSeries.C.map_add a b)
      map_mul' := fun a b => Subtype.ext (HahnSeries.C.map_mul a b) }
  let z : Fin m → V := fun i => ⟨y i, le_of_lt (hy i)⟩
  have hz : MvPolynomial.eval₂ c0 z p = 0 := by
    apply Subtype.val_injective
    change V.subtype (MvPolynomial.eval₂ c0 z p) = 0
    rw [MvPolynomial.hom_eval₂]
    exact hrel
  let res := IsLocalRing.residue V
  have hzi (i : Fin m) : res (z i) = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply (Valuation.mem_maximalIdeal_iff (v := AddValuation.toValuation (HahnSeries.addVal ℚ ℂ))).mpr
    exact hy i
  let phi : ℂ →+* IsLocalRing.ResidueField V := res.comp c0
  have heq : MvPolynomial.eval₂ phi (fun _ : Fin m => 0) p = 0 := by
    have h := congrArg res hz
    rw [MvPolynomial.hom_eval₂] at h
    simpa only [hzi, map_zero] using h
  apply phi.injective
  rw [map_zero]
  have hmap : phi (eval (0 : Affine ℂ m) p) = MvPolynomial.eval₂ phi (fun _ : Fin m => 0) p := by
    simpa only [RingHom.comp_id, Pi.zero_apply, map_zero, eval₂_id] using
      (MvPolynomial.hom_eval₂ p (RingHom.id ℂ) phi (0 : Affine ℂ m))
  exact hmap.trans heq

lemma approximateVanishing_implies_hasAPS {n m : ℕ} (F : PolynomialMap ℂ n m)
    (hF : (approximateVanishing F).Nonempty) : hasAPS F := by
  rw [hasAPS_iff_annihilator]
  obtain ⟨x, hx⟩ := hF
  intro p hp
  apply positive_series_relation p (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) hx.2
  have heq : (MvPolynomial.eval₂Hom HahnSeries.C x).comp (MvPolynomial.eval₂Hom MvPolynomial.C F) =
      MvPolynomial.eval₂Hom HahnSeries.C (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  have hp0 : MvPolynomial.eval₂Hom MvPolynomial.C F p = 0 := hp
  have h := RingHom.congr_fun heq p
  rw [RingHom.comp_apply, hp0, map_zero] at h
  exact h.symm

end APSCounting893.Main

end


section

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




end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

lemma ramBound_mul_right {e f : ℕ} (he : 0 < e) (hf : 0 < f)
    {s : PuiseuxAmbient} (hs : HahnSeries.HasRamBound e s) :
    HahnSeries.HasRamBound (e * f) s := by
  intro q hq
  obtain ⟨k, hk⟩ := hs hq
  refine ⟨k * (f : ℤ), ?_⟩
  rw [← hk]
  have he0 : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hf0 : (f : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  push_cast
  field_simp

lemma isPuiseux_zero : IsPuiseux (0 : PuiseuxAmbient) := by
  exact ⟨1, by decide, (HahnSeries.puiseuxRamSubfield ℂ (by decide : 0 < 1)).zero_mem⟩

lemma isPuiseux_one : IsPuiseux (1 : PuiseuxAmbient) := by
  exact ⟨1, by decide, (HahnSeries.puiseuxRamSubfield ℂ (by decide : 0 < 1)).one_mem⟩

lemma isPuiseux_single (q : ℚ) (c : ℂ) : IsPuiseux (HahnSeries.single q c) := by
  refine ⟨q.den, q.den_pos, (HahnSeries.mem_puiseuxRamSubfield_iff q.den_pos).mpr ?_⟩
  intro r hr
  have hrq : r = q := by
    by_contra h
    exact hr (HahnSeries.coeff_single_of_ne h)
  subst r
  exact ⟨q.num, Rat.num_div_den q⟩

lemma isPuiseux_inv {s : PuiseuxAmbient} (hs : IsPuiseux s) : IsPuiseux s⁻¹ := by
  obtain ⟨e, he, hs⟩ := hs
  exact ⟨e, he, (HahnSeries.puiseuxRamSubfield ℂ he).inv_mem hs⟩

lemma isPuiseux_mul {s t : PuiseuxAmbient} (hs : IsPuiseux s) (ht : IsPuiseux t) :
    IsPuiseux (s * t) := by
  obtain ⟨e, he, hs⟩ := hs
  obtain ⟨f, hf, ht⟩ := ht
  refine ⟨e * f, Nat.mul_pos he hf, ?_⟩
  have hs' := ramBound_mul_right he hf ((HahnSeries.mem_puiseuxRamSubfield_iff he).mp hs)
  have ht' := ramBound_mul_right hf he ((HahnSeries.mem_puiseuxRamSubfield_iff hf).mp ht)
  rw [Nat.mul_comm f e] at ht'
  exact (HahnSeries.puiseuxRamSubfield ℂ (Nat.mul_pos he hf)).mul_mem
    ((HahnSeries.mem_puiseuxRamSubfield_iff (Nat.mul_pos he hf)).mpr hs')
    ((HahnSeries.mem_puiseuxRamSubfield_iff (Nat.mul_pos he hf)).mpr ht')

lemma isPuiseux_div {s t : PuiseuxAmbient} (hs : IsPuiseux s) (ht : IsPuiseux t) :
    IsPuiseux (s / t) := by
  rw [div_eq_mul_inv]
  exact isPuiseux_mul hs (isPuiseux_inv ht)

lemma positive_orderTop_of_integral_residue_zero (s : PuiseuxAmbient)
    (hs : 0 ≤ s.orderTop) (hres : s.coeff 0 = 0) : 0 < s.orderTop := by
  by_cases hzero : s = 0
  · simp [hzero]
  have horder : 0 ≤ s.order := HahnSeries.zero_le_orderTop_iff.mp hs
  have hne : s.order ≠ 0 := by
    intro h
    have hlead := HahnSeries.leadingCoeff_ne_zero.mpr hzero
    rw [HahnSeries.leadingCoeff_eq, h] at hlead
    exact hlead hres
  exact HahnSeries.zero_lt_orderTop_of_order (lt_of_le_of_ne horder (Ne.symm hne))

lemma normalize_puiseux_coordinates {n : ℕ} (w : Fin n → PuiseuxAmbient)
    (hw : ∀ j, IsPuiseux (w j)) (hn : ∃ j, w j ≠ 0) :
    ∃ a : PuiseuxAmbient, a ≠ 0 ∧ IsPuiseux a ∧
      (∀ j, 0 ≤ (a * w j).orderTop) ∧ ∃ j, (a * w j).orderTop = 0 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j => w j ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := hn
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image S (fun i => (w i).order) hS
  have hj0 : w j ≠ 0 := (Finset.mem_filter.mp hj).2
  let a : PuiseuxAmbient := HahnSeries.single (-(w j).order) (1 : ℂ)
  have ha : a ≠ 0 := by simp [a]
  have hao : a.order = -(w j).order := HahnSeries.order_single one_ne_zero
  refine ⟨a, ha, isPuiseux_single _ _, ?_, j, ?_⟩
  · intro i
    by_cases hi : w i = 0
    · simp [hi]
    · have hle : (w j).order ≤ (w i).order :=
        hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero ha hi), HahnSeries.order_mul ha hi, hao]
      have hh : 0 ≤ -(w j).order + (w i).order := by linarith
      exact_mod_cast hh
  · rw [← HahnSeries.order_eq_orderTop_of_ne_zero (mul_ne_zero ha hj0), HahnSeries.order_mul ha hj0, hao]
    simp

end APSCounting893.Main

end


section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma coeff_zero_mul_nonnegative (x y : PuiseuxAmbient)
    (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hxo : 0 ≤ x.order := HahnSeries.zero_le_orderTop_iff.mp hx
  have hyo : 0 ≤ y.order := HahnSeries.zero_le_orderTop_iff.mp hy
  by_cases hxord : x.order = 0
  · by_cases hyord : y.order = 0
    · simpa only [HahnSeries.leadingCoeff_eq, hxord, hyord, add_zero] using HahnSeries.coeff_mul_order_add_order x y
    · have hpos : 0 < y.order := lt_of_le_of_ne hyo (Ne.symm hyord)
      rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, mul_zero]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [HahnSeries.order_mul hx0 hy0, hxord, zero_add]
      exact hpos
  · have hpos : 0 < x.order := lt_of_le_of_ne hxo (Ne.symm hxord)
    rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, zero_mul]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul hx0 hy0]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right hyo)

noncomputable def seriesResidueHom : seriesValuationRing →+* ℂ where
  toFun s := s.val.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := coeff_zero_mul_nonnegative x.val y.val x.property y.property

noncomputable def constantSeriesHom : ℂ →+* seriesValuationRing where
  toFun c := ⟨HahnSeries.C c, constant_in_hahnValuationRing c⟩
  map_zero' := Subtype.ext (HahnSeries.C.map_zero)
  map_one' := Subtype.ext (HahnSeries.C.map_one)
  map_add' a b := Subtype.ext (HahnSeries.C.map_add a b)
  map_mul' a b := Subtype.ext (HahnSeries.C.map_mul a b)

lemma seriesResidue_constant (c : ℂ) : seriesResidueHom (constantSeriesHom c) = c := by
  simp [seriesResidueHom, constantSeriesHom]


end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped LaurentSeries RatFunc
open HahnSeries
namespace APSCounting893.Main

lemma seriesResidue_surjective : Function.Surjective seriesResidueHom := by
  intro c
  exact ⟨constantSeriesHom c, seriesResidue_constant c⟩

noncomputable def polynomialSeriesHom : Polynomial ℂ →+* seriesValuationRing :=
  Polynomial.eval₂RingHom constantSeriesHom
    ⟨HahnSeries.single (1 : ℚ) (1 : ℂ), by
      exact (show (0 : WithTop ℚ) ≤ 1 by norm_num).trans HahnSeries.orderTop_single_le⟩

lemma polynomialSeriesHom_residue (p : Polynomial ℂ) :
    seriesResidueHom (polynomialSeriesHom p) = p.eval 0 := by
  change (seriesResidueHom.comp polynomialSeriesHom) p = _
  have h : seriesResidueHom.comp polynomialSeriesHom = Polynomial.evalRingHom (0 : ℂ) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [polynomialSeriesHom, seriesResidue_constant]
    · simp [polynomialSeriesHom, seriesResidueHom]
  rw [h]
  rfl

lemma finite_flat_series_lift
    (B : Type) [CommRing B] [Algebra (Polynomial ℂ) B]
    [Module.Finite (Polynomial ℂ) B] [Module.Flat (Polynomial ℂ) B]
    (φ₀ : B →+* ℂ)
    (hcomp : φ₀.comp (algebraMap (Polynomial ℂ) B) = Polynomial.evalRingHom (0 : ℂ)) :
    ∃ φ : B →+* seriesValuationRing,
      φ.comp (algebraMap (Polynomial ℂ) B) = polynomialSeriesHom ∧
      seriesResidueHom.comp φ = φ₀ := by
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : Algebra (Polynomial ℂ) seriesValuationRing := polynomialSeriesHom.toAlgebra
  apply ValuationSubring.exists_ringHom_comp_eq_of_moduleFinite_of_flat
      seriesValuationRing seriesResidueHom seriesResidue_surjective φ₀
  rw [hcomp]
  apply DFunLike.ext
  intro p
  exact (polynomialSeriesHom_residue p).symm

lemma polynomialSeriesHom_injective : Function.Injective polynomialSeriesHom := by
  have heq : seriesValuationRing.subtype.comp polynomialSeriesHom =
      rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change HahnSeries.C c = rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))
      change HahnSeries.C c = rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
      rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
      simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using (rationalSeriesHom.commutes c).symm
    · simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      change HahnSeries.single (1 : ℚ) (1 : ℂ) =
        rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
      exact rationalSeriesHom_X.symm
  have h : Function.Injective (seriesValuationRing.subtype.comp polynomialSeriesHom) := by
    rw [heq]
    exact rationalSeriesHom.injective.comp (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
  exact fun x y hxy => h (congrArg seriesValuationRing.subtype hxy)

lemma finite_series_lift_injective
    (B : Type) [CommRing B] [IsDomain B] [Algebra (Polynomial ℂ) B]
    [Module.Finite (Polynomial ℂ) B] (φ : B →+* seriesValuationRing)
    (hφ : φ.comp (algebraMap (Polynomial ℂ) B) = polynomialSeriesHom) :
    Function.Injective φ := by
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := Polynomial ℂ)
  change RingHom.ker (φ.comp (algebraMap (Polynomial ℂ) B)) = ⊥
  rw [hφ]
  exact (RingHom.injective_iff_ker_eq_bot _).mp polynomialSeriesHom_injective

lemma finite_curve_series_embedding
    (B E : Type) [CommRing B] [IsDomain B] [Field E]
    [Algebra ℂ B] [Algebra (Polynomial ℂ) B] [IsScalarTower ℂ (Polynomial ℂ) B]
    [Module.Finite (Polynomial ℂ) B] [Module.Flat (Polynomial ℂ) B]
    [Algebra B E] [Algebra ℂ E] [IsScalarTower ℂ B E]
    [Module.IsTorsionFree B E] [Algebra.IsAlgebraic B E]
    (φ₀ : B →+* ℂ)
    (hcomp : φ₀.comp (algebraMap (Polynomial ℂ) B) = Polynomial.evalRingHom (0 : ℂ)) :
    ∃ ρ : E →ₐ[ℂ] PuiseuxAmbient,
      ρ (algebraMap B E (algebraMap (Polynomial ℂ) B Polynomial.X)) =
        HahnSeries.single (1 : ℚ) (1 : ℂ) ∧
      ∀ b : B, 0 ≤ (ρ (algebraMap B E b)).orderTop ∧
        (ρ (algebraMap B E b)).coeff 0 = φ₀ b := by
  obtain ⟨φ, hφ, hφres⟩ := finite_flat_series_lift B φ₀ hcomp
  let f : B →+* PuiseuxAmbient := seriesValuationRing.subtype.comp φ
  have hf : Function.Injective f := Subtype.val_injective.comp (finite_series_lift_injective B φ hφ)
  letI : Algebra B PuiseuxAmbient := f.toAlgebra
  letI : Module.IsTorsionFree B PuiseuxAmbient :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hf
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  let σ : E →ₐ[B] PuiseuxAmbient := IsAlgClosed.lift
  have hσ (b : B) : σ (algebraMap B E b) = f b := σ.commutes b
  have hc (c : ℂ) : σ (algebraMap ℂ E c) = HahnSeries.C c := by
    rw [IsScalarTower.algebraMap_apply ℂ B E, hσ,
      IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) B]
    have hh := RingHom.congr_fun hφ (Polynomial.C c)
    simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] at hh
    change (φ (algebraMap (Polynomial ℂ) B (Polynomial.C c))).val = _
    rw [hh]
    rfl
  let ρ : E →ₐ[ℂ] PuiseuxAmbient :=
    { σ.toRingHom with
      commutes' := fun c => by
        change σ (algebraMap ℂ E c) = algebraMap ℂ PuiseuxAmbient c
        simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using hc c }
  refine ⟨ρ, ?_, ?_⟩
  · change σ _ = _
    rw [hσ]
    have hh := RingHom.congr_fun hφ Polynomial.X
    simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at hh
    change (φ (algebraMap (Polynomial ℂ) B Polynomial.X)).val = _
    rw [hh]
  · intro b
    change 0 ≤ (σ (algebraMap B E b)).orderTop ∧ (σ (algebraMap B E b)).coeff 0 = φ₀ b
    rw [hσ]
    exact ⟨(φ b).property, RingHom.congr_fun hφres b⟩

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

-- Integral-dimension helpers adapted from Prove2Me submission fb0d0add-1707-549d-bae9-43fc73bcf273 (Apache 2.0).
private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem integral_dimension_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)


lemma curve_normalization_parameter (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] (hdim : ringKrullDim B = 1) (ψ : B →ₐ[ℂ] ℂ) :
    ∃ g : Polynomial ℂ →ₐ[ℂ] B, Function.Injective g ∧ g.Finite ∧ ψ (g Polynomial.X) = 0 := by
  classical
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ B
  have hs : s = 1 := by
    letI : Algebra (MvPolynomial (Fin s) ℂ) B := g.toRingHom.toAlgebra
    letI : Module.Finite (MvPolynomial (Fin s) ℂ) B := hfin
    have hd := integral_dimension_eq (R := MvPolynomial (Fin s) ℂ) (S := B) hinj
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin, hdim] at hd
    exact_mod_cast hd
  subst s
  let e := MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
  let g₀ : Polynomial ℂ →ₐ[ℂ] B := g.comp e.symm.toAlgHom
  let c : ℂ := ψ (g₀ Polynomial.X)
  let shift := Polynomial.algEquivAevalXAddC (-c)
  let g₁ : Polynomial ℂ →ₐ[ℂ] B := g₀.comp shift.toAlgHom
  have hg₀ : g₀.Finite := hfin.comp (RingHom.Finite.of_surjective _ e.symm.surjective)
  have hg₁ : g₁.Finite := hg₀.comp (RingHom.Finite.of_surjective _ shift.surjective)
  refine ⟨g₁, (hinj.comp e.symm.injective).comp shift.injective, hg₁, ?_⟩
  change ψ (g₀ (shift Polynomial.X)) = 0
  have hconst (z : ℂ) : ψ (g₀ (Polynomial.C z)) = z := by
    change ψ (g₀ (algebraMap ℂ (Polynomial ℂ) z)) = z
    rw [g₀.commutes, ψ.commutes]
    rfl
  simp [shift, Polynomial.algEquivAevalXAddC, hconst, c]

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc LaurentSeries
open HahnSeries
namespace APSCounting893.Main

lemma curve_branch_embedding (B E : Type) [CommRing B] [IsDomain B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] (hdim : ringKrullDim B = 1)
    [Field E] [Algebra ℂ E] [Algebra B E] [IsScalarTower ℂ B E]
    [Module.IsTorsionFree B E] [Algebra.IsAlgebraic B E] (ψ : B →ₐ[ℂ] ℂ) :
    ∃ ρ : E →ₐ[ℂ] PuiseuxAmbient,
      (∀ x : E, IsPuiseux (ρ x)) ∧
      ∀ b : B, 0 ≤ (ρ (algebraMap B E b)).orderTop ∧ (ρ (algebraMap B E b)).coeff 0 = ψ b := by
  classical
  obtain ⟨g, hinj, hfinite, hgX⟩ := curve_normalization_parameter B hdim ψ
  letI : Algebra (Polynomial ℂ) B := g.toRingHom.toAlgebra
  letI : Module.Finite (Polynomial ℂ) B := hfinite
  letI : Module.IsTorsionFree (Polynomial ℂ) B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  letI : Module.Flat (Polynomial ℂ) B := inferInstance
  letI : IsScalarTower ℂ (Polynomial ℂ) B := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap ℂ B c = g (algebraMap ℂ (Polynomial ℂ) c)
    exact (g.commutes c).symm)
  letI : Algebra (Polynomial ℂ) E := Algebra.compHom E g.toRingHom
  letI : IsScalarTower (Polynomial ℂ) B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ℂ (Polynomial ℂ) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ B E, IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) B]
    rfl)
  have hψ : ψ.toRingHom.comp (algebraMap (Polynomial ℂ) B) = Polynomial.evalRingHom (0 : ℂ) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      change ψ (g (algebraMap ℂ (Polynomial ℂ) c)) = c
      rw [g.commutes, ψ.commutes]
      rfl
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      change ψ (g Polynomial.X) = 0
      exact hgX
  have hφinj : Function.Injective (algebraMap (Polynomial ℂ) E) :=
    (FaithfulSMul.algebraMap_injective B E).comp hinj
  let κ : RatFunc ℂ →+* E := IsFractionRing.lift hφinj
  letI : Algebra (RatFunc ℂ) E := κ.toAlgebra
  have hκ (p : Polynomial ℂ) : κ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = algebraMap (Polynomial ℂ) E p :=
    IsFractionRing.lift_algebraMap hφinj p
  letI : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) E := IsScalarTower.of_algebraMap_eq (fun p => by
    change algebraMap (Polynomial ℂ) E p = κ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
    exact (hκ p).symm)
  letI : IsScalarTower ℂ (RatFunc ℂ) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
    change algebraMap ℂ E c = κ (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))
    rw [hκ]
    change algebraMap ℂ E c = algebraMap (Polynomial ℂ) E (algebraMap ℂ (Polynomial ℂ) c)
    exact IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) E c)
  letI : Algebra.IsAlgebraic (Polynomial ℂ) E := Algebra.IsAlgebraic.trans (Polynomial ℂ) B E
  letI : Algebra.IsAlgebraic (RatFunc ℂ) E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial ℂ) (K := RatFunc ℂ) (C := E)).mp inferInstance
  obtain ⟨ρ, ht, hres⟩ := finite_curve_series_embedding B E ψ.toRingHom hψ
  have ht' : ρ (algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    change ρ (κ _) = _
    rw [hκ]
    exact ht
  exact ⟨ρ, algebraic_image_puiseux ρ ht', hres⟩

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Topology
namespace APSCounting893.Main

-- Adapted from Prove2Me submission f939c467-880d-596a-93cc-5365595436ae (Apache 2.0).
lemma constructible_generic_mem_open {Y : Type} [TopologicalSpace Y]
    (ξ : Y) (hgen : IsGenericPoint ξ Set.univ)
    {s : Set Y} (hs : IsConstructible s) (hξ : ξ ∈ s) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧ V ⊆ s := by
  have hmem : ∀ W : Set Y, IsOpen W → W.Nonempty → ξ ∈ W := fun W hW hne =>
    (hgen.mem_open_set_iff hW).mpr (by simpa using hne)
  revert hξ
  induction s, hs using BooleanSubalgebra.closure_sdiff_sup_induction with
  | isSublattice =>
    exact ⟨fun s hs t ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩,
      fun s hs t ht ↦ ⟨hs.1.inter ht.1, hs.2.inter_isOpen ht.2 ht.1⟩⟩
  | bot_mem => exact ⟨isOpen_empty, .empty⟩
  | top_mem => exact ⟨isOpen_univ, .univ⟩
  | sdiff U hU V hV =>
    intro hξ
    have hV0 : V = ∅ := by
      by_contra hne
      exact hξ.2 (hmem V hV.1 (Set.nonempty_iff_ne_empty.mpr hne))
    refine ⟨U, hU.1, ⟨_, hξ.1⟩, ?_⟩
    rw [hV0, Set.diff_empty]
  | sup s _ t _ hs' ht' =>
    rintro (h | h)
    · obtain ⟨V, hV, hne, hsub⟩ := hs' h
      exact ⟨V, hV, hne, hsub.trans Set.subset_union_left⟩
    · obtain ⟨V, hV, hne, hsub⟩ := ht' h
      exact ⟨V, hV, hne, hsub.trans Set.subset_union_right⟩

lemma exists_principal_open_in_spectrum_image
    {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.FinitePresentation) :
    ∃ b : R, b ≠ 0 ∧ ∀ p : PrimeSpectrum R, b ∉ p.asIdeal →
      ∃ q : PrimeSpectrum S, PrimeSpectrum.comap f q = p := by
  classical
  let ξ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hgen : IsGenericPoint ξ Set.univ := by
    simp only [IsGenericPoint, PrimeSpectrum.closure_singleton, ξ, PrimeSpectrum.zeroLocus_bot]
  have hξ : ξ ∈ Set.range (PrimeSpectrum.comap f) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap f ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot f).mp hf
  obtain ⟨V, hV, hVne, hVrange⟩ := constructible_generic_mem_open ξ hgen
    (PrimeSpectrum.isConstructible_range_comap hfin) hξ
  have hξV : ξ ∈ V := (hgen.mem_open_set_iff hV).mpr (by simpa using hVne)
  obtain ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, hξb, hbV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hξV hV
  refine ⟨b, ?_, ?_⟩
  · change b ∉ (⊥ : Ideal R) at hξb
    simpa only [Ideal.mem_bot] using hξb
  · intro p hp
    exact hVrange (hbV hp)

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace APSCounting893.Main

lemma generic_fiber_point
    (R S K Ω : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.FiniteType R S] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    (hinj : Function.Injective (algebraMap R S)) : Nonempty (S →ₐ[R] Ω) := by
  classical
  let F := FractionRing S
  have hRΩ (r : R) : algebraMap R Ω r = algebraMap K Ω (algebraMap R K r) :=
    IsScalarTower.algebraMap_apply R K Ω r
  letI : IsScalarTower R S F := inferInstance
  let f : R →+* F := (algebraMap S F).comp (algebraMap R S)
  have hf : Function.Injective f := (IsFractionRing.injective S F).comp hinj
  let ρ : K →+* F := IsFractionRing.lift hf
  letI : Algebra K F := ρ.toAlgebra
  letI : IsScalarTower R K F := IsScalarTower.of_algebraMap_eq (fun r => by
    change f r = ρ (algebraMap R K r)
    exact (IsFractionRing.lift_algebraMap hf r).symm)
  let T := K ⊗[R] S
  let e : T →ₐ[K] F := (AlgHom.liftEquiv R K S F)
    (IsScalarTower.toAlgHom R S F)
  letI : Nontrivial T := e.toRingHom.domain_nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal T
  letI : M.IsMaximal := hM
  letI := Ideal.Quotient.field M
  let L := T ⧸ M
  letI : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  let σ : L →ₐ[K] Ω := IsAlgClosed.lift
  let τ : S →ₐ[R] L := (Ideal.Quotient.mkₐ R M).comp Algebra.TensorProduct.includeRight
  have hσR (r : R) : σ (algebraMap R L r) = algebraMap R Ω r := by
    rw [IsScalarTower.algebraMap_apply R K L, σ.commutes]
    exact (hRΩ r).symm
  exact ⟨{ σ.toRingHom.comp τ.toRingHom with
    commutes' := fun r => by
      change σ (τ (algebraMap R S r)) = algebraMap R Ω r
      rw [τ.commutes, hσR] }⟩

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma image_coordinate_kernel {n m : ℕ} (F : PolynomialMap ℂ n m) :
    vanishingIdeal ℂ (imageClosure F) = RingHom.ker (MvPolynomial.aeval F).toRingHom := by
  rw [imageClosure, vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
  rfl

noncomputable def imageCoordinateMap {n m : ℕ} (F : PolynomialMap ℂ n m) :
    CoordinateRing (imageClosure F) →ₐ[ℂ] Polynomials ℂ n :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval F) (fun p hp => by
    rw [image_coordinate_kernel] at hp
    exact hp)

lemma imageCoordinateMap_mk {n m : ℕ} (F : PolynomialMap ℂ n m) (p : Polynomials ℂ m) :
    imageCoordinateMap F (Ideal.Quotient.mk _ p) = MvPolynomial.aeval F p := rfl

lemma imageCoordinateMap_injective {n m : ℕ} (F : PolynomialMap ℂ n m) :
    Function.Injective (imageCoordinateMap F) := by
  apply (RingHom.injective_iff_ker_eq_bot (imageCoordinateMap F).toRingHom).mpr
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change imageCoordinateMap F (Ideal.Quotient.mk _ p) = 0 at ha
  rw [imageCoordinateMap_mk] at ha
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, image_coordinate_kernel]
  exact ha

noncomputable def imagePointHom {n m : ℕ} (F : PolynomialMap ℂ n m)
    (y : Affine ℂ m) (hy : y ∈ imageClosure F) : CoordinateRing (imageClosure F) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval y) (fun p hp => hp y hy)

lemma imagePointHom_mk {n m : ℕ} (F : PolynomialMap ℂ n m)
    (y : Affine ℂ m) (hy : y ∈ imageClosure F) (p : Polynomials ℂ m) :
    imagePointHom F y hy (Ideal.Quotient.mk _ p) = MvPolynomial.eval y p := by
  rfl

lemma complex_algHom_surjective {A : Type} [CommRing A] [Algebra ℂ A] (f : A →ₐ[ℂ] ℂ) :
    Function.Surjective f := by
  intro c
  refine ⟨algebraMap ℂ A c, ?_⟩
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using f.commutes c

lemma exact_zero_approximate {n m : ℕ} (F : PolynomialMap ℂ n m)
    (x : Affine ℂ n) (hx : evaluate F x = 0) : (approximateVanishing F).Nonempty := by
  let z : Fin n → PuiseuxAmbient := fun i => HahnSeries.C (x i)
  refine ⟨z, (fun i => ?_), ?_⟩
  · simpa only [z, HahnSeries.C_apply] using isPuiseux_single (0 : ℚ) (x i)
  · intro j
    have heq : HahnSeries.C.comp (MvPolynomial.eval x) = MvPolynomial.eval₂Hom HahnSeries.C z := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp
      · intro i; simp [z]
    have hj : MvPolynomial.eval x (F j) = 0 := congrFun hx j
    have hh := RingHom.congr_fun heq (F j)
    change HahnSeries.C (MvPolynomial.eval x (F j)) = MvPolynomial.eval₂ HahnSeries.C z (F j) at hh
    rw [← hh, hj, map_zero]
    simp

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def quotientEmbeddingMap {R S : Type} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (f : R →ₐ[ℂ] S) (P : Ideal R) (Q : Ideal S)
    (hQP : Q.comap f.toRingHom = P) : (R ⧸ P) →ₐ[ℂ] (S ⧸ Q) :=
  Ideal.Quotient.liftₐ P ((Ideal.Quotient.mkₐ ℂ Q).comp f) (fun r hr => by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change r ∈ Q.comap f.toRingHom
    rwa [hQP])

lemma quotientEmbeddingMap_mk {R S : Type} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (f : R →ₐ[ℂ] S) (P : Ideal R) (Q : Ideal S)
    (hQP : Q.comap f.toRingHom = P) (r : R) :
    quotientEmbeddingMap f P Q hQP (Ideal.Quotient.mk P r) = Ideal.Quotient.mk Q (f r) := rfl

lemma quotientEmbeddingMap_injective {R S : Type} [CommRing R] [CommRing S]
    [Algebra ℂ R] [Algebra ℂ S] (f : R →ₐ[ℂ] S) (P : Ideal R) (Q : Ideal S)
    (hQP : Q.comap f.toRingHom = P) : Function.Injective (quotientEmbeddingMap f P Q hQP) := by
  apply (RingHom.injective_iff_ker_eq_bot (quotientEmbeddingMap f P Q hQP).toRingHom).mpr
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  change quotientEmbeddingMap f P Q hQP (Ideal.Quotient.mk P r) = 0 at ha
  rw [quotientEmbeddingMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, ← hQP]
  exact ha

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma hasAPS_implies_approximateVanishing {n m : ℕ} (F : PolynomialMap ℂ n m)
    (hAPS : hasAPS F) : (approximateVanishing F).Nonempty := by
  classical
  by_cases hexact : ∃ x : Affine ℂ n, evaluate F x = 0
  · obtain ⟨x, hx⟩ := hexact
    exact exact_zero_approximate F x hx
  let Y := imageClosure F
  let B := CoordinateRing Y
  let A := Polynomials ℂ n
  let φ : B →ₐ[ℂ] A := imageCoordinateMap F
  have hφ : Function.Injective φ := imageCoordinateMap_injective F
  letI : (vanishingIdeal ℂ Y).IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure F)
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ B A := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  letI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ B A
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
  letI : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hφfin : φ.toRingHom.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  let ψ₀ : B →ₐ[ℂ] ℂ := imagePointHom F 0 hAPS
  let m₀ : Ideal B := RingHom.ker ψ₀.toRingHom
  letI : m₀.IsMaximal := RingHom.ker_isMaximal_of_surjective ψ₀ (complex_algHom_surjective ψ₀)
  obtain ⟨b, hb, hopen⟩ := exists_principal_open_in_spectrum_image φ.toRingHom hφ hφfin
  have hb₀ : ψ₀ b = 0 := by
    by_contra hnot
    obtain ⟨q, hq⟩ := hopen ⟨m₀, inferInstance⟩ hnot
    have hqcomp : q.asIdeal.comap φ.toRingHom = m₀ := congrArg PrimeSpectrum.asIdeal hq
    obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
    obtain ⟨x, hxM⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
    apply hexact
    refine ⟨x, ?_⟩
    funext j
    have hr : Ideal.Quotient.mk (vanishingIdeal ℂ Y) (MvPolynomial.X j) ∈ m₀ := by
      change ψ₀ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = 0
      exact (imagePointHom_mk F 0 hAPS (MvPolynomial.X j)).trans (by simp)
    have hF : F j ∈ q.asIdeal := by
      have hh : φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) ∈ q.asIdeal := by
        change Ideal.Quotient.mk _ (MvPolynomial.X j) ∈ q.asIdeal.comap φ.toRingHom
        rw [hqcomp]
        exact hr
      have hm : φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = F j :=
        (imageCoordinateMap_mk F (MvPolynomial.X j)).trans (MvPolynomial.aeval_X F j)
      rwa [hm] at hh
    have hz := hqM hF
    rw [hxM] at hz
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluate, Pi.zero_apply] using hz x (Set.mem_singleton x)
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective b
  have hpoint : ∃ y ∈ Y, MvPolynomial.eval y p ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hpI : p ∈ vanishingIdeal ℂ Y := by
      intro y hy
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hn y hy
    exact hb (hp.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hpI))
  obtain ⟨y₁, hy₁, hpy₁⟩ := hpoint
  let ψ₁ : B →ₐ[ℂ] ℂ := imagePointHom F y₁ hy₁
  let m₁ : Ideal B := RingHom.ker ψ₁.toRingHom
  letI : m₁.IsMaximal := RingHom.ker_isMaximal_of_surjective ψ₁ (complex_algHom_surjective ψ₁)
  have hb₁ : b ∉ m₁ := by
    change ψ₁ b ≠ 0
    rw [← hp]
    exact hpy₁
  have hdimB : 1 ≤ ringKrullDim B := by
    have hnonzero : b ∈ nonZeroDivisors B := mem_nonZeroDivisors_iff_ne_zero.mpr hb
    have hspan : Ideal.span ({b} : Set B) ≤ m₀ := Ideal.span_le.mpr (by
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hb₀)
    have hheight : (1 : ℕ∞) ≤ m₀.height :=
      (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hnonzero).trans
        (Ideal.height_mono hspan)
    exact (show (1 : WithBot ℕ∞) ≤ (m₀.height : WithBot ℕ∞) by exact_mod_cast hheight).trans
      Ideal.height_le_ringKrullDim_of_isPrime
  obtain ⟨P, hPprime, hP₀, hP₁, hdimR⟩ :=
    Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one ℂ hdimB m₀ m₁
  letI : P.IsPrime := hPprime
  have hbP : b ∉ P := fun h => hb₁ (hP₁ h)
  obtain ⟨q, hq⟩ := hopen ⟨P, hPprime⟩ hbP
  let Q := q.asIdeal
  letI : Q.IsPrime := q.isPrime
  have hQP : Q.comap φ.toRingHom = P := congrArg PrimeSpectrum.asIdeal hq
  let R := B ⧸ P
  let S := A ⧸ Q
  let g : R →ₐ[ℂ] S := quotientEmbeddingMap φ P Q hQP
  have hg : Function.Injective g := quotientEmbeddingMap_injective φ P Q hQP
  letI : Algebra R S := g.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R S
  let E := AlgebraicClosure (FractionRing R)
  letI : IsScalarTower R (FractionRing R) E := inferInstance
  letI : IsScalarTower ℂ (FractionRing R) E := inferInstance
  letI : IsScalarTower ℂ R E := inferInstance
  letI : Module.IsTorsionFree R E := Module.isTorsionFree_iff_algebraMap_injective.mpr
    ((algebraMap (FractionRing R) E).injective.comp (IsFractionRing.injective R (FractionRing R)))
  letI : Algebra.IsAlgebraic R E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := FractionRing R) (C := E)).mpr inferInstance
  obtain ⟨σ⟩ := generic_fiber_point R S (FractionRing R) E hg
  let ψ : R →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ P ψ₀ (fun r hr => hP₀ hr)
  obtain ⟨ρ, hρP, hρres⟩ := curve_branch_embedding R E hdimR ψ
  let h : A →ₐ[ℂ] E := (σ.restrictScalars ℂ).comp (Ideal.Quotient.mkₐ ℂ Q)
  let x : Fin n → E := fun i => h (MvPolynomial.X i)
  have heval (p : Polynomials ℂ n) : MvPolynomial.aeval x p = h p := by
    have heq : (MvPolynomial.aeval x).toRingHom = h.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change MvPolynomial.aeval x (MvPolynomial.C c) = h (MvPolynomial.C c)
        rw [MvPolynomial.aeval_C]
        exact (h.commutes c).symm
      · intro i; change MvPolynomial.aeval x (MvPolynomial.X i) = x i; simp
    exact RingHom.congr_fun heq p
  let β : Affine PuiseuxAmbient n := fun i => ρ (x i)
  have hmap (p : Polynomials ℂ n) : MvPolynomial.eval₂ HahnSeries.C β p = ρ (h p) := by
    have heq : MvPolynomial.eval₂Hom HahnSeries.C β = ρ.toRingHom.comp h.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change MvPolynomial.eval₂Hom HahnSeries.C β (MvPolynomial.C c) = ρ (h (MvPolynomial.C c))
        rw [MvPolynomial.eval₂Hom_C]
        change HahnSeries.C c = ρ (h (algebraMap ℂ A c))
        rw [h.commutes, ρ.commutes]
        simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C]
      · intro i; change MvPolynomial.eval₂Hom HahnSeries.C β (MvPolynomial.X i) = β i; simp
    exact RingHom.congr_fun heq p
  refine ⟨β, fun i => hρP (x i), ?_⟩
  intro j
  let r : R := Ideal.Quotient.mk P (Ideal.Quotient.mk (vanishingIdeal ℂ Y) (MvPolynomial.X j))
  have houtput : h (F j) = algebraMap R E r := by
    have hh := σ.commutes r
    change σ (g r) = algebraMap R E r at hh
    have hgmk : g r = Ideal.Quotient.mk Q (φ (Ideal.Quotient.mk _ (MvPolynomial.X j))) :=
      quotientEmbeddingMap_mk φ P Q hQP _
    have hφmk : φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = F j :=
      (imageCoordinateMap_mk F (MvPolynomial.X j)).trans (MvPolynomial.aeval_X F j)
    rw [hgmk, hφmk] at hh
    exact hh
  have hψ : ψ r = 0 := by
    change ψ₀ (Ideal.Quotient.mk (vanishingIdeal ℂ Y) (MvPolynomial.X j)) = 0
    exact (imagePointHom_mk F 0 hAPS (MvPolynomial.X j)).trans (by simp)
  rw [hmap, houtput]
  apply positive_orderTop_of_integral_residue_zero _ (hρres r).1
  exact (hρres r).2.trans hψ

end APSCounting893.Main

end

open APSCounting893.Main

theorem solution (n m : ℕ) (F : PolynomialMap ℂ n m) :
    ((approximateVanishing F).Nonempty ↔ hasAPS F) ∧
      (hasAPS F ↔ ∀ P ∈ annihilator F, MvPolynomial.eval (0 : Affine ℂ m) P = 0) := by
  exact ⟨⟨approximateVanishing_implies_hasAPS F, hasAPS_implies_approximateVanishing F⟩, hasAPS_iff_annihilator F⟩


