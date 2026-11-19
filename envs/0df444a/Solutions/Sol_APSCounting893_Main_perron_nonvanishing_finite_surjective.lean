-- Prove2me | solution 1 for APSCounting893.Main.perron_nonvanishing_finite_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:39:54.146432+00:00
-- url     : https://prove2.me/submissions/1ae86cff-77a4-4648-91a2-082fc40b5e61

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_LineGeometry
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma integral_algHom_lifts_point {K R S : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S] [Algebra.FiniteType K S]
    (f : R →ₐ[K] S) (hf : f.toRingHom.IsIntegral) (chi : R →ₐ[K] K)
    (hker : RingHom.ker f.toRingHom ≤ RingHom.ker chi.toRingHom) :
    ∃ psi : S →ₐ[K] K, psi.comp f = chi := by
  classical
  letI : Algebra R S := f.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨fun x => hf x⟩
  let P := RingHom.ker chi.toRingHom
  have hchisurj : Function.Surjective chi := by
    intro c
    exact ⟨algebraMap K R c, by simpa using chi.commutes c⟩
  haveI : P.IsMaximal := RingHom.ker_isMaximal_of_surjective chi.toRingHom hchisurj
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) P hker
  change Q.comap f.toRingHom = P at hQ
  letI : Q.IsMaximal := hQmax
  letI : Field (S ⧸ Q) := Ideal.Quotient.field Q
  letI : Module.Finite K (S ⧸ Q) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ Q)
  let lift : (S ⧸ Q) →ₐ[K] K := IsAlgClosed.lift
  let psi : S →ₐ[K] K := lift.comp (Ideal.Quotient.mkₐ K Q)
  refine ⟨psi, ?_⟩
  apply AlgHom.ext
  intro r
  have hz : r - algebraMap K R (chi r) ∈ P := by
    change chi (r - algebraMap K R (chi r)) = 0
    simp
  have hzQ : f (r - algebraMap K R (chi r)) ∈ Q := by
    change r - algebraMap K R (chi r) ∈ Q.comap f.toRingHom
    rw [hQ]
    exact hz
  have hzero : psi (f (r - algebraMap K R (chi r))) = 0 := by
    change lift (Ideal.Quotient.mk Q (f (r - algebraMap K R (chi r)))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hzQ, map_zero]
  simpa only [map_sub, f.commutes, psi.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero, AlgHom.comp_apply] using hzero

end APSCounting893.Main
end Component_0

section Component_1

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
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def localizedPolynomialMap {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (b : Polynomials K m) :
    Localization.Away b →ₐ[K] Localization.Away (aeval F b) :=
  IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (aeval F b)) (aeval F) b

lemma localizedPolynomialMap_algebraMap {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (b p : Polynomials K m) :
    localizedPolynomialMap F b (algebraMap (Polynomials K m) (Localization.Away b) p) =
      algebraMap (Polynomials K n) (Localization.Away (aeval F b)) (aeval F p) := by
  change IsLocalization.map (Localization.Away (aeval F b)) (aeval F).toRingHom
    (M := Submonoid.powers b) (T := Submonoid.powers (aeval F b)) (by
      rintro _ ⟨e, rfl⟩
      exact ⟨e, by simp⟩)
    (algebraMap (Polynomials K m) (Localization.Away b) p) = _
  exact IsLocalization.map_eq _ p


lemma localized_integral_polynomial_surjective {K : Type} [Field K] [IsAlgClosed K]
    {n m : ℕ} (F : PolynomialMap K n m) (b : Polynomials K m)
    (hB : aeval F b ≠ 0)
    (hfinite : (localizedPolynomialMap F b).toRingHom.IsIntegral)
    (y : Affine K m) (hy : y ∈ imageClosure F) (hby : eval y b ≠ 0) :
    ∃ x : Affine K n, evaluate F x = y := by
  classical
  let R := Localization.Away b
  let B : Polynomials K n := aeval F b
  let S := Localization.Away B
  let phi : R →ₐ[K] S := localizedPolynomialMap F b
  let chi : R →ₐ[K] K := IsLocalization.Away.liftAlgHom b
    (show IsUnit (aeval y b) from isUnit_iff_ne_zero.mpr hby)
  have hSfinite : Algebra.FiniteType K S := Algebra.FiniteType.trans (R := K) (S := Polynomials K n) (A := S) inferInstance inferInstance
  letI : Algebra.FiniteType K S := hSfinite
  have hSinj : Function.Injective (algebraMap (Polynomials K n) S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hB)
  have hker : RingHom.ker phi.toRingHom ≤ RingHom.ker chi.toRingHom := by
    intro z hz
    obtain ⟨e, p, hp⟩ := IsLocalization.Away.surj b z
    have hzero : aeval F p = 0 := by
      apply hSinj
      have hh := congrArg phi hp
      rw [map_mul, map_pow, localizedPolynomialMap_algebraMap,
        localizedPolynomialMap_algebraMap] at hh
      change phi z = 0 at hz
      rw [hz, zero_mul] at hh
      rw [map_zero]
      exact hh.symm
    have hpY : p ∈ vanishingIdeal K (imageClosure F) := by
      rw [imageClosure, vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
      exact hzero
    have hpy : eval y p = 0 := hpY y hy
    have hh := congrArg chi hp
    simp only [map_mul, map_pow, chi, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq] at hh
    change chi z * eval y b ^ e = eval y p at hh
    rw [hpy] at hh
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero e hby)
  obtain ⟨psi, hpsi⟩ := integral_algHom_lifts_point phi hfinite chi hker
  let x : Affine K n := fun j => psi (algebraMap (Polynomials K n) S (X j))
  have heval (p : Polynomials K n) : psi (algebraMap (Polynomials K n) S p) = eval x p := by
    have hh : psi.toRingHom.comp (algebraMap (Polynomials K n) S) = eval x := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, eval_C]
        change psi (algebraMap (Polynomials K n) S (algebraMap K (Polynomials K n) c)) = c
        rw [← IsScalarTower.algebraMap_apply K (Polynomials K n) S c]
        simpa only [Algebra.algebraMap_self, RingHom.id_apply] using psi.commutes c
      · intro j; simp only [RingHom.comp_apply, eval_X]; rfl
    exact RingHom.congr_fun hh p
  refine ⟨x, ?_⟩
  funext j
  have hh := AlgHom.congr_fun hpsi (algebraMap (Polynomials K m) R (X j))
  change psi (localizedPolynomialMap F b
    (algebraMap (Polynomials K m) (Localization.Away b) (X j))) = _ at hh
  rw [localizedPolynomialMap_algebraMap, aeval_X] at hh
  rw [heval] at hh
  simp only [chi, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq] at hh
  change eval x (F j) = aeval y (X j) at hh
  simpa only [aeval_X, eval_X, evaluate, aeval_def, Algebra.algebraMap_self, eval₂_id] using hh

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def localizationPoint {K : Type} [Field K] {n : ℕ}
    (b : Polynomials K n) (x : Affine K n) (hx : eval x b ≠ 0) :
    Localization.Away b →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom b (show IsUnit (aeval x b) from isUnit_iff_ne_zero.mpr hx)

lemma localizationPoint_algebraMap {K : Type} [Field K] {n : ℕ}
    (b p : Polynomials K n) (x : Affine K n) (hx : eval x b ≠ 0) :
    localizationPoint b x hx (algebraMap (Polynomials K n) (Localization.Away b) p) = eval x p := by
  change IsLocalization.Away.lift b
    (show IsUnit ((aeval x).toRingHom b) from isUnit_iff_ne_zero.mpr hx)
    (algebraMap (Polynomials K n) (Localization.Away b) p) = _
  exact IsLocalization.Away.lift_eq b _ p

lemma localizationPoint_fraction {K : Type} [Field K] {n : ℕ}
    (b p : Polynomials K n) (x : Affine K n) (hx : eval x b ≠ 0)
    (z : Localization.Away b) (e : ℕ)
    (he : z * algebraMap (Polynomials K n) (Localization.Away b) b ^ e =
      algebraMap (Polynomials K n) (Localization.Away b) p) :
    localizationPoint b x hx z = eval x p / eval x b ^ e := by
  apply (eq_div_iff (pow_ne_zero e hx)).mpr
  have hh := congrArg (localizationPoint b x hx) he
  simpa only [map_mul, map_pow, localizationPoint_algebraMap] using hh

lemma localizationPoint_comp_map {K : Type} [Field K] {n m : ℕ}
    (g : PolynomialMap K n m) (b : Polynomials K m) (x : Affine K n)
    (hx : eval x (aeval g b) ≠ 0) (hy : eval (evaluate g x) b ≠ 0) :
    (localizationPoint (aeval g b) x hx).comp (localizedPolynomialMap g b) =
      localizationPoint b (evaluate g x) hy := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (M := Submonoid.powers b)
  apply RingHom.ext
  intro p
  change localizationPoint (aeval g b) x hx
    (localizedPolynomialMap g b (algebraMap (Polynomials K m) (Localization.Away b) p)) = _
  rw [localizedPolynomialMap_algebraMap, localizationPoint_algebraMap]
  change eval x (aeval g p) = localizationPoint b (evaluate g x) hy
    (algebraMap (Polynomials K m) (Localization.Away b) p)
  rw [localizationPoint_algebraMap]
  exact evaluation_substitution g p x

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma polynomial_relation_of_pointwise {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (g : PolynomialMap K n m) (p : Polynomial (Polynomials K m)) (i : Fin n)
    (hroot : ∀ x : Affine K n,
      Polynomial.eval (x i) (p.map (eval (evaluate g x))) = 0) :
    Polynomial.eval₂ (aeval g).toRingHom (X i) p = 0 := by
  apply MvPolynomial.funext
  intro x
  have h := Polynomial.hom_eval₂ p (aeval g).toRingHom (eval x) (X i)
  have hcomp : (eval x).comp (aeval g).toRingHom = eval (evaluate g x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j
      change eval x (aeval g (X j)) = eval (evaluate g x) (X j)
      rw [aeval_X, eval_X]
      simp only [evaluate, aeval_def, Algebra.algebraMap_self, eval₂_id]
  rw [map_zero, h, hcomp, eval_X, Polynomial.eval₂_eq_eval_map]
  exact hroot x

lemma localized_perron_coordinates_integral {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (g : PolynomialMap K n m) (p : Fin n → Polynomial (Polynomials K m))
    (b : Polynomials K m) (hb : b ≠ 0)
    (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine K n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate g x))) = 0) :
    letI : Algebra (Localization.Away b) (Localization.Away (aeval g b)) :=
      (localizedPolynomialMap g b).toRingHom.toAlgebra
    ∀ i : Fin n, IsIntegral (Localization.Away b)
      (algebraMap (Polynomials K n) (Localization.Away (aeval g b)) (X i)) := by
  classical
  let R := Localization.Away b
  let S := Localization.Away (aeval g b)
  letI : Algebra R S := (localizedPolynomialMap g b).toRingHom.toAlgebra
  letI : IsDomain R := IsLocalization.isDomain_of_le_nonZeroDivisors R
    (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  intro i
  have hdiv : (p i).leadingCoeff ∣ b := by
    rw [hprod]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hu : IsUnit (algebraMap (Polynomials K m) R (p i).leadingCoeff) :=
    IsLocalization.Away.isUnit_of_dvd (S := R) b hdiv
  let q : Polynomial R := (p i).map (algebraMap (Polynomials K m) R)
  have hqlead : IsUnit q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero]
    exact hu
  have hcomp : (algebraMap R S).comp (algebraMap (Polynomials K m) R) =
      (algebraMap (Polynomials K n) S).comp (aeval g).toRingHom := by
    apply RingHom.ext
    intro a
    exact localizedPolynomialMap_algebraMap g b a
  have hqzero : Polynomial.eval₂ (algebraMap R S) (algebraMap (Polynomials K n) S (X i)) q = 0 := by
    rw [Polynomial.eval₂_map, hcomp]
    rw [← Polynomial.hom_eval₂]
    rw [polynomial_relation_of_pointwise g (p i) i (hroot i), map_zero]
  refine ⟨hqlead.unit⁻¹.val • q, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hqlead, ?_⟩
  change Polynomial.eval₂ (algebraMap R S) (algebraMap (Polynomials K n) S (X i))
    (hqlead.unit⁻¹.val • q) = 0
  rw [Polynomial.eval₂_smul, hqzero, mul_zero]

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma localized_adjoin_coordinates_top {K : Type} [Field K] {n m : ℕ}
    (g : PolynomialMap K n m) (b : Polynomials K m) :
    letI : Algebra (Localization.Away b) (Localization.Away (aeval g b)) :=
      (localizedPolynomialMap g b).toRingHom.toAlgebra
    Algebra.adjoin (Localization.Away b)
      (Set.range (fun i : Fin n => algebraMap (Polynomials K n) (Localization.Away (aeval g b)) (X i))) = ⊤ := by
  classical
  let R := Localization.Away b
  let B : Polynomials K n := aeval g b
  let S := Localization.Away B
  letI : Algebra R S := (localizedPolynomialMap g b).toRingHom.toAlgebra
  let z : Fin n → S := fun i => algebraMap (Polynomials K n) S (X i)
  let A := Algebra.adjoin R (Set.range z)
  have hz (i : Fin n) : z i ∈ A := Algebra.subset_adjoin ⟨i, rfl⟩
  have hc (c : K) : algebraMap (Polynomials K n) S (C c) ∈ A := by
    have hh := A.algebraMap_mem (algebraMap (Polynomials K m) R (C c))
    change localizedPolynomialMap g b (algebraMap (Polynomials K m) R (C c)) ∈ A at hh
    rw [localizedPolynomialMap_algebraMap, aeval_C] at hh
    exact hh
  have hp (p : Polynomials K n) : algebraMap (Polynomials K n) S p ∈ A := by
    induction p using MvPolynomial.induction_on with
    | C c => exact hc c
    | add p q hp hq => rw [map_add]; exact A.add_mem hp hq
    | mul_X p i hp => rw [map_mul]; exact A.mul_mem hp (hz i)
  let v : S := algebraMap R S (IsLocalization.Away.invSelf b : R)
  have hv : v ∈ A := A.algebraMap_mem _
  have hunit : algebraMap (Polynomials K n) S B * v = 1 := by
    have hh := congrArg (algebraMap R S) (IsLocalization.Away.mul_invSelf (S := R) b)
    rw [map_mul, map_one] at hh
    change localizedPolynomialMap g b (algebraMap (Polynomials K m) R b) * v = 1 at hh
    rw [localizedPolynomialMap_algebraMap] at hh
    exact hh
  apply top_unique
  intro w hw
  clear hw
  obtain ⟨e, p, he⟩ := IsLocalization.Away.surj B w
  have hw : w = algebraMap (Polynomials K n) S p * v ^ e := by
    calc
      w = w * 1 := by ring
      _ = w * (algebraMap (Polynomials K n) S B * v) ^ e := by rw [hunit, one_pow]
      _ = (w * algebraMap (Polynomials K n) S B ^ e) * v ^ e := by rw [mul_pow]; ring
      _ = algebraMap (Polynomials K n) S p * v ^ e := by rw [he]
  rw [hw]
  exact A.mul_mem (hp p) (A.pow_mem hv e)

lemma localized_perron_module_finite {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (g : PolynomialMap K n m) (p : Fin n → Polynomial (Polynomials K m))
    (b : Polynomials K m) (hb : b ≠ 0)
    (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine K n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate g x))) = 0) :
    letI : Algebra (Localization.Away b) (Localization.Away (aeval g b)) :=
      (localizedPolynomialMap g b).toRingHom.toAlgebra
    Module.Finite (Localization.Away b) (Localization.Away (aeval g b)) := by
  classical
  let R := Localization.Away b
  let S := Localization.Away (aeval g b)
  letI : Algebra R S := (localizedPolynomialMap g b).toRingHom.toAlgebra
  let z : Fin n → S := fun i => algebraMap (Polynomials K n) S (X i)
  let A := Algebra.adjoin R (Set.range z)
  have hi := localized_perron_coordinates_integral g p b hb hprod hroot
  letI : Module.Finite R A := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range z)
    (by rintro _ ⟨i, rfl⟩; exact hi i)
  apply Module.Finite.of_surjective A.val.toLinearMap
  intro s
  have hA : A = ⊤ := localized_adjoin_coordinates_top g b
  exact ⟨⟨s, by rw [hA]; trivial⟩, rfl⟩

lemma localized_perron_isIntegral {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (g : PolynomialMap K n m) (p : Fin n → Polynomial (Polynomials K m))
    (b : Polynomials K m) (hb : b ≠ 0)
    (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine K n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate g x))) = 0) :
    (localizedPolynomialMap g b).toRingHom.IsIntegral := by
  let R := Localization.Away b
  let S := Localization.Away (aeval g b)
  letI : Algebra R S := (localizedPolynomialMap g b).toRingHom.toAlgebra
  letI : Module.Finite R S := localized_perron_module_finite g p b hb hprod hroot
  exact Algebra.IsIntegral.isIntegral

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma localized_finite_polynomial_span {K : Type} [Field K] {n m : ℕ}
    (g : PolynomialMap K n m) (b : Polynomials K m)
    (hfinite : letI : Algebra (Localization.Away b) (Localization.Away (aeval g b)) :=
      (localizedPolynomialMap g b).toRingHom.toAlgebra
      Module.Finite (Localization.Away b) (Localization.Away (aeval g b))) :
    ∃ (s : ℕ) (G : Fin s → Polynomials K n),
      ∀ f : Polynomials K n, ∃ (A : Fin s → Polynomials K m) (e : Fin s → ℕ),
        ∀ x : Affine K n, eval (evaluate g x) b ≠ 0 →
          eval x f = ∑ i, (eval (evaluate g x) (A i) / eval (evaluate g x) b ^ e i) * eval x (G i) := by
  classical
  let R := Localization.Away b
  let B : Polynomials K n := aeval g b
  let S := Localization.Away B
  letI : Algebra R S := (localizedPolynomialMap g b).toRingHom.toAlgebra
  letI : Module.Finite R S := hfinite
  obtain ⟨s, v, hgen⟩ := Module.Finite.exists_fin (R := R) (M := S)
  choose d G hG using fun i => IsLocalization.Away.surj B (v i)
  refine ⟨s, G, ?_⟩
  intro f
  have hf : algebraMap (Polynomials K n) S f ∈ Submodule.span R (Set.range v) := by rw [hgen]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  choose e A hA using fun i => IsLocalization.Away.surj b (c i)
  refine ⟨A, fun i => e i + d i, ?_⟩
  intro x hx
  have hBval : eval x B = eval (evaluate g x) b := evaluation_substitution g b x
  have hxB : eval x B ≠ 0 := hBval ▸ hx
  let point : S →ₐ[K] K := localizationPoint B x hxB
  have hcv (i : Fin s) : point (algebraMap R S (c i)) =
      eval (evaluate g x) (A i) / eval (evaluate g x) b ^ e i := by
    have hh := AlgHom.congr_fun (localizationPoint_comp_map g b x hxB hx) (c i)
    change point (algebraMap R S (c i)) = localizationPoint b (evaluate g x) hx (c i) at hh
    rw [hh]
    exact localizationPoint_fraction b (A i) (evaluate g x) hx (c i) (e i) (hA i)
  have hv (i : Fin s) : point (v i) = eval x (G i) / eval (evaluate g x) b ^ d i := by
    rw [show point (v i) = eval x (G i) / eval x B ^ d i from
      localizationPoint_fraction B (G i) x hxB (v i) (d i) (hG i), hBval]
  have hh := congrArg point hc.symm
  simp only [map_sum, Algebra.smul_def, map_mul] at hh
  change point (algebraMap (Polynomials K n) S f) = _ at hh
  rw [localizationPoint_algebraMap] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcv, hv, pow_add]
  field_simp

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
namespace APSCounting893.Main

lemma zeroLocus_prime_nonempty {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (Polynomials K n)) (hI : I.IsPrime) : (zeroLocus K I).Nonempty := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI.ne_top
  obtain ⟨x, hMx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hM
  refine ⟨x, ?_⟩
  intro p hp
  have hpM := hIM hp
  rw [hMx] at hpM
  exact hpM x (Set.mem_singleton x)

lemma irreducibleAffine_zeroLocus_prime {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (Polynomials K n)) (hI : I.IsPrime) : IrreducibleAffine (zeroLocus K I) := by
  letI : I.IsPrime := hI
  apply prime_ideal_irreducibleAffine (zeroLocus_prime_nonempty I hI) (isAlgSet_zeroLocus I)
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  exact hI

lemma affineComponent_ideal_minimal {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C W : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) (hW : AffineComponent C W) :
    (vanishingIdeal K C).IsMinimalPrime (vanishingIdeal K W) := by
  refine ⟨⟨irreducibleAffine_ideal_prime hW.1, vanishingIdeal_anti_mono hW.2.1⟩, ?_⟩
  intro Q hQ hQW
  letI : Q.IsPrime := hQ.1
  have hWQ : W ⊆ zeroLocus K Q := by
    rw [isAlgSet_eq_zeroLocus hW.1.2.1]
    exact zeroLocus_anti_mono hQW
  have hQC : zeroLocus K Q ⊆ C := by
    rw [isAlgSet_eq_zeroLocus hC]
    exact zeroLocus_anti_mono hQ.2
  have heq := hW.2.2 (zeroLocus K Q) (irreducibleAffine_zeroLocus_prime Q hQ.1) hWQ hQC
  rw [← heq, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]

lemma affineComponent_of_minimal {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C)
    (Q : Ideal (Polynomials K n)) (hQ : (vanishingIdeal K C).IsMinimalPrime Q) :
    AffineComponent C (zeroLocus K Q) := by
  letI : Q.IsPrime := hQ.isPrime
  refine ⟨irreducibleAffine_zeroLocus_prime Q hQ.isPrime, ?_, ?_⟩
  · rw [isAlgSet_eq_zeroLocus hC]
    exact zeroLocus_anti_mono hQ.le
  · intro W hW hQW hWC
    have hIWQ : vanishingIdeal K W ≤ Q := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q]
      exact vanishingIdeal_anti_mono hQW
    have hQI : Q ≤ vanishingIdeal K W := hQ.2
      ⟨irreducibleAffine_ideal_prime hW, vanishingIdeal_anti_mono hWC⟩ hIWQ
    rw [isAlgSet_eq_zeroLocus hW.2.1, hIWQ.antisymm hQI]

lemma exists_affineComponent_mem {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) {x : Affine K n} (hx : x ∈ C) :
    ∃ W, AffineComponent C W ∧ x ∈ W := by
  have hI : vanishingIdeal K C ≤ vanishingIdeal K ({x} : Set (Affine K n)) :=
    vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hx)
  obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le hI
  exact ⟨zeroLocus K Q, affineComponent_of_minimal hC Q hQ,
    fun p hp => hQx hp x (Set.mem_singleton x)⟩

lemma isAlgSet_inter {K : Type} [Field K] {n : ℕ} {A B : Set (Affine K n)}
    (hA : RSCapacity.IsAlgSet A) (hB : RSCapacity.IsAlgSet B) : RSCapacity.IsAlgSet (A ∩ B) := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  refine ⟨S ∪ T, ?_⟩
  ext x
  simp only [RSCapacity.zeroSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
  aesop

lemma isAlgSet_preimage_evaluate {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) {A : Set (Affine K m)} (hA : RSCapacity.IsAlgSet A) :
    RSCapacity.IsAlgSet (evaluate F ⁻¹' A) := by
  obtain ⟨S, rfl⟩ := hA
  refine ⟨(eval₂Hom MvPolynomial.C F) '' S, ?_⟩
  ext x
  simp only [Set.mem_preimage, RSCapacity.zeroSet, Set.mem_setOf_eq, Set.forall_mem_image, evaluation_substitution]

lemma isAlgSet_affineLine {K : Type} [Field K] {d : ℕ}
    (base direction : Affine K d) (hdir : direction ≠ 0) : RSCapacity.IsAlgSet (affineLine base direction) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, direction i ≠ 0 := by
    by_contra h
    push Not at h
    exact hdir (funext h)
  let p : Fin d → Polynomials K d := fun j =>
    MvPolynomial.C (direction i) * (MvPolynomial.X j - MvPolynomial.C (base j)) -
      MvPolynomial.C (direction j) * (MvPolynomial.X i - MvPolynomial.C (base i))
  refine ⟨Set.range p, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩ q ⟨j, rfl⟩
    simp only [p, map_sub, map_mul, eval_C, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x hx
    have hj (j : Fin d) : direction i * (x j - base j) - direction j * (x i - base i) = 0 := by
      simpa [p] using hx (p j) (Set.mem_range_self j)
    refine ⟨(x i - base i) / direction i, ?_⟩
    funext j
    have he : x j - base j = direction j * (x i - base i) / direction i :=
      (eq_div_iff hi).mpr (by simpa only [mul_comm] using sub_eq_zero.mp (hj j))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -he

lemma irreducibleAffine_affineLine {K : Type} [Field K] [Infinite K] {d : ℕ}
    (base direction : Affine K d) (hdir : direction ≠ 0) : IrreducibleAffine (affineLine base direction) := by
  let F : PolynomialMap K 1 d := fun j => MvPolynomial.C (base j) +
    MvPolynomial.C (direction j) * MvPolynomial.X 0
  have hrange : Set.range (evaluate F) = affineLine base direction := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x 0, ?_⟩
      funext j
      simp [evaluate, F, mul_comm]
    · rintro ⟨t, rfl⟩
      refine ⟨fun _ => t, ?_⟩
      funext j
      simp [evaluate, F, mul_comm]
  have hcl : imageClosure F = affineLine base direction := by
    unfold imageClosure RSCapacity.zClosure
    rw [hrange, ← isAlgSet_eq_zeroLocus (isAlgSet_affineLine base direction hdir)]
  exact hcl ▸ irreducibleAffine_imageClosure F

lemma finiteMorphism_restrict {K : Type} [Field K] {n m : ℕ}
    {X W : Set (Affine K n)} (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F)
    (hWX : W ⊆ X) : FiniteMorphism W F := by
  obtain ⟨s, g, hg⟩ := hfinite
  refine ⟨s, g, ?_⟩
  intro p
  obtain ⟨c, hc⟩ := hg p
  exact ⟨c, fun x hx => hc x (hWX hx)⟩

lemma finiteMorphism_image {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (W : Set (Affine K n)) (hclosed : RSCapacity.IsAlgSet W)
    (F : PolynomialMap K n m) (hfinite : FiniteMorphism W F) :
    evaluate F '' W = zeroLocus K (RingHom.ker (coordinatePullback W F)) := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing W) := coordinatePullbackAlgebra W F
  letI : Module.Finite (Polynomials K m) (CoordinateRing W) := finiteMorphism_module_finite W F hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing W) = coordinatePullback W F := rfl
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩ p hp
    have hpI : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K W :=
      Ideal.Quotient.eq_zero_iff_mem.mp hp
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hpI x hx
  · intro y hy
    let P := vanishingIdeal K ({y} : Set (Affine K m))
    have hker : RingHom.ker (algebraMap (Polynomials K m) (CoordinateRing W)) ≤ P := by
      intro p hp
      rw [halg] at hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y p).mpr (hy p hp)
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := CoordinateRing W) P hker
    letI : Q.IsMaximal := hQmax
    let N : Ideal (Polynomials K n) := Q.comap (Ideal.Quotient.mk (vanishingIdeal K W))
    have hNmax : N.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hNx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hNmax
    have hxW : x ∈ W := by
      rw [isAlgSet_eq_zeroLocus hclosed]
      intro p hp
      have hpN : p ∈ N := by
        change Ideal.Quotient.mk (vanishingIdeal K W) p ∈ Q
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        exact Q.zero_mem
      rw [hNx] at hpN
      exact hpN x (Set.mem_singleton x)
    refine ⟨x, hxW, ?_⟩
    funext j
    have hpP : MvPolynomial.X j - MvPolynomial.C (y j) ∈ P := by
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    rw [← hQ] at hpP
    have hpN : eval₂Hom MvPolynomial.C F (MvPolynomial.X j - MvPolynomial.C (y j)) ∈ N := hpP
    rw [hNx] at hpN
    have hpval := hpN x (Set.mem_singleton x)
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution,
      map_sub, eval_X, eval_C, sub_eq_zero] at hpval
    exact hpval

lemma finite_dominant_component_surjective {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (X : Set (Affine K n)) (hX : IrreducibleAffine X)
    (F : PolynomialMap K n m) (hfinite : FiniteMorphism X F)
    (hdom : RSCapacity.zClosure (evaluate F '' X) = Set.univ)
    (L : Set (Affine K m)) (hL : IrreducibleAffine L)
    (W : Set (Affine K n)) (hW : AffineComponent {x | x ∈ X ∧ evaluate F x ∈ L} W) :
    evaluate F '' W = L := by
  classical
  letI : (vanishingIdeal K X).IsPrime := irreducibleAffine_ideal_prime hX
  letI : (vanishingIdeal K W).IsPrime := irreducibleAffine_ideal_prime hW.1
  letI : Algebra (Polynomials K m) (CoordinateRing X) := coordinatePullbackAlgebra X F
  letI : Module.Finite (Polynomials K m) (CoordinateRing X) := finiteMorphism_module_finite X F hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing X) = coordinatePullback X F := rfl
  letI : FaithfulSMul (Polynomials K m) (CoordinateRing X) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (coordinatePullback_injective_of_dominant X F hdom)
  have hWX : W ⊆ X := fun x hx => (hW.2.1 hx).1
  let psi : CoordinateRing X →+* CoordinateRing W :=
    Ideal.Quotient.factor (vanishingIdeal_anti_mono hWX)
  let Q : Ideal (CoordinateRing X) := RingHom.ker psi
  letI : Q.IsPrime := RingHom.ker_isPrime psi
  have hraw : Q.comap (Ideal.Quotient.mk (vanishingIdeal K X)) = vanishingIdeal K W := by
    ext p
    simp [Q, psi, Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  let P : Ideal (Polynomials K m) := vanishingIdeal K L
  letI : P.IsPrime := irreducibleAffine_ideal_prime hL
  have hP : P ≤ Q.under (Polynomials K m) := by
    intro p hp
    change (coordinatePullback X F) p ∈ Q
    have hs : eval₂Hom MvPolynomial.C F p ∈ vanishingIdeal K W := by
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using
        hp (evaluate F x) (hW.2.1 hx).2
    rw [← hraw] at hs
    exact hs
  let q : Ideal (Polynomials K m) := Q.under (Polynomials K m)
  letI : Q.LiesOver q := ⟨rfl⟩
  obtain ⟨Q0, hQ0Q, hQ0prime, hQ0over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := q) Q hP
  letI : Q0.IsPrime := hQ0prime
  letI : Q0.LiesOver P := hQ0over
  have hQ0base : Q0.comap (coordinatePullback X F) = P := (Q0.over_def P).symm
  let J : Ideal (Polynomials K n) := Q0.comap (Ideal.Quotient.mk (vanishingIdeal K X))
  letI : J.IsPrime := Ideal.comap_isPrime _ Q0
  have hJW : J ≤ vanishingIdeal K W := (Ideal.comap_mono hQ0Q).trans_eq hraw
  have hWJ : W ⊆ zeroLocus K J := by
    rw [isAlgSet_eq_zeroLocus hW.1.2.1]
    exact zeroLocus_anti_mono hJW
  have hJC : zeroLocus K J ⊆ {x | x ∈ X ∧ evaluate F x ∈ L} := by
    intro x hx
    constructor
    · rw [isAlgSet_eq_zeroLocus hX.2.1]
      intro p hp
      have hpJ : p ∈ J := by
        change Ideal.Quotient.mk (vanishingIdeal K X) p ∈ Q0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
        exact Q0.zero_mem
      exact hx p hpJ
    · rw [isAlgSet_eq_zeroLocus hL.2.1]
      intro p hp
      have hp0 : (coordinatePullback X F) p ∈ Q0 := by
        change p ∈ Q0.comap (coordinatePullback X F)
        rw [hQ0base]
        exact hp
      have hpJ : eval₂Hom MvPolynomial.C F p ∈ J := hp0
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hx _ hpJ
  have hWeq := hW.2.2 (zeroLocus K J) (irreducibleAffine_zeroLocus_prime J inferInstance) hWJ hJC
  have hIW : vanishingIdeal K W = J := by
    rw [← hWeq, MvPolynomial.IsPrime.vanishingIdeal_zeroLocus]
  have hker : RingHom.ker (coordinatePullback W F) = P := by
    ext p
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk (vanishingIdeal K W) (eval₂Hom MvPolynomial.C F p) = 0 ↔ p ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem, hIW]
    change p ∈ Q0.comap (coordinatePullback X F) ↔ p ∈ P
    rw [hQ0base]
  rw [finiteMorphism_image W hW.1.2.1 F (finiteMorphism_restrict F hfinite hWX), hker]
  exact (isAlgSet_eq_zeroLocus hL.2.1).symm

end APSCounting893.Main

end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma evaluate_beta (F : ReducedMap) (c : Affine ℂ F.n) (x : Affine ℂ F.n) :
    evaluate (betaPolynomials F c) x = normalization c (evaluate F.F x) := by
  funext j
  exact evaluation_substitution F.F (normalizationPolynomials c j) x

lemma normalizationOpen_closed_complement (F : ReducedMap) (D : LineData F) :
    RSCapacity.IsAlgSet (normalization D.c '' (imageClosure F.F \ D.U)) := by
  change RSCapacity.IsAlgSet (evaluate (normalizationPolynomials D.c) '' _)
  rw [finiteMorphism_image _ D.goodOpen.1.2 _
    (finiteMorphism_restrict _ D.normalization.1 Set.diff_subset)]
  exact isAlgSet_zeroLocus _

lemma exists_normalizationOpen_polynomial (F : ReducedMap) (D : LineData F) :
    ∃ g : Polynomials ℂ F.n,
      (∀ u ∈ normalization D.c '' (imageClosure F.F \ D.U), eval u g = 0) ∧
      ∃ u ∈ affineLine 0 D.alpha, eval u g ≠ 0 := by
  classical
  obtain ⟨u, hu, hV⟩ := D.meetsOpen
  have hclosed := normalizationOpen_closed_complement F D
  change u ∉ normalization D.c '' (imageClosure F.F \ D.U) at hV
  rw [isAlgSet_eq_zeroLocus hclosed] at hV
  change ¬ u ∈ zeroLocus ℂ (vanishingIdeal ℂ (normalization D.c '' (imageClosure F.F \ D.U))) at hV
  simp only [mem_zeroLocus_iff, not_forall] at hV
  obtain ⟨g, hg, hgu⟩ := hV
  refine ⟨g, ?_, u, hu, ?_⟩
  · intro v hv
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hg v hv
  · simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hgu

lemma vanishes_of_vanishes_principal_open {n : ℕ} (W : Set (Affine ℂ n))
    (hW : IrreducibleAffine W) (p g : Polynomials ℂ n)
    (hg : ∃ x ∈ W, eval x g ≠ 0)
    (hp : ∀ x ∈ W, eval x g ≠ 0 → eval x p = 0) :
    p ∈ vanishingIdeal ℂ W := by
  have hprod : p * g ∈ vanishingIdeal ℂ W := by
    intro x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_mul]
    by_cases h : eval x g = 0
    · simp [h]
    · rw [hp x hx h, zero_mul]
  have hprime := irreducibleAffine_ideal_prime hW
  rcases hprime.mem_or_mem hprod with hp | hgzero
  · exact hp
  · obtain ⟨x, hx, hgx⟩ := hg
    exact (hgx (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hgzero x hx)).elim

lemma closedGraph_image_dense_lineFiber (F : ReducedMap) (D : LineData F) :
    {y | y ∈ imageClosure F.F ∧ normalization D.c y ∈ affineLine 0 D.alpha} ⊆
      RSCapacity.zClosure (evaluate F.F '' closedGraphCurve F D.c D.alpha D.U) := by
  classical
  obtain ⟨g, hg, u, hu, hgu⟩ := exists_normalizationOpen_polynomial F D
  let C : Set (Affine ℂ (F.n + 1)) :=
    {y | y ∈ imageClosure F.F ∧ normalization D.c y ∈ affineLine 0 D.alpha}
  have hC : RSCapacity.IsAlgSet C := isAlgSet_inter
    (isAlgSet_zeroLocus _) (isAlgSet_preimage_evaluate _ (isAlgSet_affineLine _ _ D.nonzero))
  intro y hy p hp
  obtain ⟨W, hW, hyW⟩ := exists_affineComponent_mem hC hy
  have hdom : RSCapacity.zClosure
      (evaluate (normalizationPolynomials D.c) '' imageClosure F.F) = Set.univ := by
    change RSCapacity.zClosure (normalization D.c '' imageClosure F.F) = _
    rw [D.normalization.2.1]
    exact (isAlgSet_eq_zeroLocus (show RSCapacity.IsAlgSet (Set.univ : Set (Affine ℂ F.n)) from
      ⟨∅, by ext; simp [RSCapacity.zeroSet]⟩)).symm
  have hsurj := finite_dominant_component_surjective (imageClosure F.F)
    (irreducibleAffine_imageClosure F.F) (normalizationPolynomials D.c)
    D.normalization.1 hdom (affineLine 0 D.alpha) (irreducibleAffine_affineLine _ _ D.nonzero) W hW
  obtain ⟨w, hw, hwu⟩ := (show u ∈ normalization D.c '' W by change u ∈ evaluate (normalizationPolynomials D.c) '' W; rw [hsurj]; exact hu)
  have hpW : p ∈ vanishingIdeal ℂ W := by
    apply vanishes_of_vanishes_principal_open W hW.1 p
      (eval₂Hom MvPolynomial.C (normalizationPolynomials D.c) g)
    · refine ⟨w, hw, ?_⟩
      rw [evaluation_substitution]
      change eval (normalization D.c w) g ≠ 0
      rw [hwu]
      exact hgu
    · intro v hv hgv
      rw [evaluation_substitution] at hgv
      have hvC := hW.2.1 hv
      have hvU : v ∈ D.U := by
        by_contra hnot
        exact hgv (hg (normalization D.c v) ⟨v, ⟨hvC.1, hnot⟩, rfl⟩)
      obtain ⟨x, hfx⟩ := D.goodOpen.2.2.1 hvU
      have hxD : x ∈ closedGraphCurve F D.c D.alpha D.U := by
        apply zeroLocus_vanishingIdeal_le
        constructor
        · rw [evaluate_beta, hfx]
          exact hvC.2
        · rw [evaluate_beta, hfx]
          intro hbad
          exact hgv (hg _ hbad)
      have := hp v ⟨x, hxD, hfx⟩
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using this
  exact hpW y hyW

lemma exists_component_imageClosure_mem {K : Type} [Field K] [IsAlgClosed K] {n m : ℕ}
    (C : Set (Affine K n)) (hC : RSCapacity.IsAlgSet C)
    (F : PolynomialMap K n m) (y : Affine K m)
    (hy : y ∈ RSCapacity.zClosure (evaluate F '' C)) :
    ∃ W, AffineComponent C W ∧ y ∈ RSCapacity.zClosure (evaluate F '' W) := by
  classical
  by_contra h
  let I := vanishingIdeal K C
  let Q := I.minimalPrimes
  have hQfinite : Q.Finite := I.finite_minimalPrimes_of_isNoetherianRing
  letI : Fintype Q := hQfinite.fintype
  have hfail (q : Q) : ∃ p : Polynomials K m,
      p ∈ vanishingIdeal K (evaluate F '' zeroLocus K q.val) ∧ eval y p ≠ 0 := by
    have hn : y ∉ RSCapacity.zClosure (evaluate F '' zeroLocus K q.val) := by
      intro hyq
      exact h ⟨zeroLocus K q.val, affineComponent_of_minimal hC q.val q.property, hyq⟩
    simp only [RSCapacity.zClosure, mem_zeroLocus_iff, not_forall] at hn
    obtain ⟨p, hp, hpy⟩ := hn
    exact ⟨p, hp, by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hpy⟩
  choose p hp hpy using hfail
  let P : Polynomials K m := ∏ q : Q, p q
  have hP : P ∈ vanishingIdeal K (evaluate F '' C) := by
    rintro v ⟨x, hx, rfl⟩
    have hI : I ≤ vanishingIdeal K ({x} : Set (Affine K n)) :=
      vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hx)
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le hI
    have hxq : x ∈ zeroLocus K q := fun a ha => hqx ha x (Set.mem_singleton x)
    have hz := hp ⟨q, hq⟩ (evaluate F x) ⟨x, hxq, rfl⟩
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id] at hz ⊢
    change eval (evaluate F x) P = 0
    simp only [P, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨q, hq⟩ : Q))
    exact hz
  have hz := hy P hP
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, P, map_prod] at hz
  exact (Finset.prod_ne_zero_iff.mpr (fun q _ => hpy q)) hz

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma perron_finiteOverOpen (F : ReducedMap) (c : Affine ℂ F.n)
    (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n)
    (hb : b ≠ 0) (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine ℂ F.n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) :
    FiniteOverOpen Set.univ F.F {y ∈ imageClosure F.F | eval (normalization c y) b ≠ 0} := by
  classical
  obtain ⟨s, G, hG⟩ := localized_finite_polynomial_span (betaPolynomials F c) b
    (localized_perron_module_finite (betaPolynomials F c) p b hb hprod hroot)
  let norm := normalizationPolynomials c
  let B : Polynomials ℂ (F.n + 1) := eval₂Hom C norm b
  intro y hy
  refine ⟨B, ?_, ?_, s, G, ?_⟩
  · change eval y B ≠ 0
    rw [evaluation_substitution]
    exact hy.2
  · rintro y' ⟨x, hx, rfl⟩ hB
    refine ⟨zeroLocus_vanishingIdeal_le _ (Set.mem_range_self x), ?_⟩
    change eval (evaluate F.F x) B ≠ 0 at hB
    rw [evaluation_substitution] at hB
    exact hB
  · intro f
    obtain ⟨A, e, hA⟩ := hG f
    refine ⟨fun i => eval₂Hom C norm (A i), e, ?_⟩
    intro x hx hxB
    have hxb : eval (evaluate (betaPolynomials F c) x) b ≠ 0 := by
      rw [evaluate_beta]
      change eval (normalization c (evaluate F.F x)) b ≠ 0
      exact (evaluation_substitution norm b (evaluate F.F x)) ▸ hxB
    have hh := hA x hxb
    simpa only [B, norm, evaluation_substitution, evaluate_beta, normalization] using hh

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma localized_integral_of_projection {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (pi : PolynomialMap K m r) (b : Polynomials K r)
    (hInt : (localizedPolynomialMap (fun j => aeval F (pi j)) b).toRingHom.IsIntegral) :
    (localizedPolynomialMap F (aeval pi b)).toRingHom.IsIntegral := by
  classical
  let g : PolynomialMap K n r := fun j => aeval F (pi j)
  let R := Localization.Away b
  let T := Localization.Away (aeval pi b)
  let S := Localization.Away (aeval F (aeval pi b))
  have hB : aeval g b = aeval F (aeval pi b) := by
    exact (comp_aeval_apply pi (aeval F) b).symm
  haveI : IsLocalization.Away (aeval g b) S := by rw [hB]; infer_instance
  let beta : R →ₐ[K] S := IsLocalization.Away.mapₐ R S (aeval g) b
  let proj : R →ₐ[K] T := localizedPolynomialMap pi b
  let out : T →ₐ[K] S := localizedPolynomialMap F (aeval pi b)
  have hbetaMap (p : Polynomials K r) :
      beta (algebraMap (Polynomials K r) R p) = algebraMap (Polynomials K n) S (aeval g p) := by
    change IsLocalization.map S (aeval g).toRingHom
      (M := Submonoid.powers b) (T := Submonoid.powers (aeval g b)) (by
        rintro _ ⟨e, rfl⟩; exact ⟨e, by simp⟩)
      (algebraMap (Polynomials K r) R p) = _
    exact IsLocalization.map_eq _ p
  let S0 := Localization.Away (aeval g b)
  let e : S0 ≃ₐ[Polynomials K n] S := IsLocalization.algEquiv (Submonoid.powers (aeval g b)) S0 S
  let ek : S0 ≃ₐ[K] S := e.restrictScalars K
  have hecomp : ek.toAlgHom.comp (localizedPolynomialMap g b) = beta := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (M := Submonoid.powers b)
    apply RingHom.ext
    intro p
    change ek (localizedPolynomialMap g b (algebraMap (Polynomials K r) R p)) =
      beta (algebraMap (Polynomials K r) R p)
    rw [localizedPolynomialMap_algebraMap, hbetaMap]
    exact e.commutes (aeval g p)
  have hbeta : beta.toRingHom.IsIntegral := by
    rw [← hecomp]
    intro x
    obtain ⟨z, rfl⟩ := ek.surjective x
    exact (hInt z).map ek.toRingEquiv.toRingHom
  have hcomp : out.comp proj = beta := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (M := Submonoid.powers b)
    apply RingHom.ext
    intro p
    change out (proj (algebraMap (Polynomials K r) R p)) = beta (algebraMap (Polynomials K r) R p)
    rw [show proj (algebraMap (Polynomials K r) R p) =
      algebraMap (Polynomials K m) T (aeval pi p) from localizedPolynomialMap_algebraMap pi b p]
    rw [show out (algebraMap (Polynomials K m) T (aeval pi p)) =
      algebraMap (Polynomials K n) S (aeval F (aeval pi p)) from localizedPolynomialMap_algebraMap F (aeval pi b) (aeval pi p)]
    rw [hbetaMap]
    apply congrArg (algebraMap (Polynomials K n) S)
    exact comp_aeval_apply pi (aeval F) p
  intro x
  apply RingHom.IsIntegralElem.of_comp (f := proj.toRingHom)
  change (out.comp proj).toRingHom.IsIntegralElem x
  rw [hcomp]
  exact hbeta x

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma betaPolynomials_algebraicIndependent (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    AlgebraicIndependent ℂ (betaPolynomials F c) := by
  apply algebraicIndependent_iff.mpr
  intro p hp
  let q : Polynomials ℂ (F.n + 1) := aeval (normalizationPolynomials c) p
  have hsub : aeval F.F q = aeval (betaPolynomials F c) p := by
    dsimp only [q]
    rw [comp_aeval_apply]
    rfl
  have hqimage : q ∈ vanishingIdeal ℂ (imageClosure F.F) := by
    rw [imageClosure, vanishingIdeal_zClosure, image_vanishingIdeal_eq_kernel]
    exact hsub.trans hp
  have hqzero : ∀ y ∈ imageClosure F.F, eval (normalization c y) p = 0 := by
    intro y hy
    have h := hqimage y hy
    change aeval y q = 0 at h
    have he : eval y q = eval (normalization c y) p :=
      evaluation_substitution (normalizationPolynomials c) p y
    exact he ▸ h
  apply MvPolynomial.funext
  intro y
  exact hc.2.2.1 p hqzero y (Set.mem_univ y)


end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma perron_nonvanishing_goodOpen (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c)
    (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n)
    (hb : b ≠ 0) (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine ℂ F.n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) :
    GoodOpen F {y ∈ imageClosure F.F | eval (normalization c y) b ≠ 0} := by
  classical
  let Y := imageClosure F.F
  let U : Set (Affine ℂ (F.n + 1)) := {y ∈ Y | eval (normalization c y) b ≠ 0}
  let norm := normalizationPolynomials c
  let B : Polynomials ℂ (F.n + 1) := aeval norm b
  have hY : IrreducibleAffine Y := irreducibleAffine_imageClosure F.F
  have heval (y : Affine ℂ (F.n + 1)) : aeval y B = eval (normalization c y) b := by
    change eval y (eval₂Hom C norm b) = _
    exact evaluation_substitution norm b y
  have hcomplement : Y \ U = Y ∩ zeroLocus ℂ (Ideal.span {B}) := by
    ext y
    simp only [U, Set.mem_diff, Set.mem_setOf_eq, Set.mem_inter_iff, zeroLocus_span,
      Set.mem_singleton_iff, forall_eq]
    rw [heval]
    tauto
  have hopen : RelativeOpen Y U := ⟨fun _ hy => hy.1, by
    rw [hcomplement]
    exact isAlgSet_inter hY.2.1 (isAlgSet_zeroLocus _)⟩
  have hnonempty : U.Nonempty := by
    have hex : ∃ u : Affine ℂ F.n, eval u b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hb (MvPolynomial.funext h)
    obtain ⟨u, hu⟩ := hex
    have huY : u ∈ normalization c '' Y := by rw [hc.2.1]; trivial
    obtain ⟨y, hy, hpy⟩ := huY
    exact ⟨y, hy, by rw [hpy]; exact hu⟩
  have hcomp : (fun j => aeval F.F (norm j)) = betaPolynomials F c := by
    funext j
    rfl
  have hintBeta : (localizedPolynomialMap (fun j => aeval F.F (norm j)) b).toRingHom.IsIntegral := by
    rw [hcomp]
    exact localized_perron_isIntegral (betaPolynomials F c) p b hb hprod hroot
  have hintF : (localizedPolynomialMap F.F B).toRingHom.IsIntegral :=
    localized_integral_of_projection F.F norm b hintBeta
  have hB : aeval F.F B ≠ 0 := by
    change aeval F.F (aeval norm b) ≠ 0
    rw [comp_aeval_apply, hcomp]
    intro hz
    exact hb ((betaPolynomials_algebraicIndependent F c hc).eq_zero_of_aeval_eq_zero b hz)
  have hsubset : U ⊆ Set.range (evaluate F.F) := by
    intro y hy
    have hyB : eval y B ≠ 0 := by
      have he : eval y B = eval (normalization c y) b := heval y
      rw [he]
      exact hy.2
    exact localized_integral_polynomial_surjective F.F B hB hintF y hy.1 hyB
  exact ⟨hopen, hnonempty, hsubset, perron_finiteOverOpen F c p b hb hprod hroot⟩

end APSCounting893.Main
end Component_12

open APSCounting893.Main MvPolynomial
theorem solution (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c)
    (p : Fin F.n → Polynomial (Polynomials ℂ F.n)) (b : Polynomials ℂ F.n)
    (hb : b ≠ 0) (hprod : b = ∏ i, (p i).leadingCoeff)
    (hroot : ∀ i (x : Affine ℂ F.n),
      Polynomial.eval (x i) ((p i).map (eval (evaluate (betaPolynomials F c) x))) = 0) :
    GoodOpen F {y ∈ imageClosure F.F | eval (normalization c y) b ≠ 0} := by
  exact APSCounting893.Main.perron_nonvanishing_goodOpen F c hc p b hb hprod hroot
