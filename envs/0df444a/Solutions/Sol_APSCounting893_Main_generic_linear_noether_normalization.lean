-- Prove2me | solution 1 for APSCounting893.Main.generic_linear_noether_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:23:55.333324+00:00
-- url     : https://prove2.me/submissions/691548c0-2230-4b31-acdf-9631b064fbf8

import Definitions.Def_APSCounting893_Main_Geometry
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral

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



lemma top_homogeneousComponent_ne_zero {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K n) (hp : p ≠ 0) : homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨e, he, hmax⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.mpr hp)
    (fun e => e.sum (fun _ a => a))
  have hd : e.degree = p.totalDegree := by simpa [Finsupp.degree, Finsupp.sum, totalDegree] using hmax.symm
  intro h
  have hc := congrArg (MvPolynomial.coeff e) h
  rw [coeff_homogeneousComponent, if_pos hd, coeff_zero] at hc
  exact (mem_support_iff.mp he) hc

lemma homogeneous_eval_scale {K : Type} [Field K] {n D : ℕ}
    (p : Polynomials K n) (hp : p.IsHomogeneous D) (a : K) (x : Affine K n) :
    eval (fun i => a * x i) p = a ^ D * eval x p := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hd : ∑ i : Fin n, e i = D := by
    have hs : (∑ i ∈ e.support, e i) = ∑ i : Fin n, e i := by
      exact e.sum_fintype (fun _ b => b) (fun _ => rfl)
    exact hs.symm.trans (hp.degree_eq_sum_deg_support he).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

noncomputable def normalizationParameter {K : Type} [Field K] {n : ℕ}
    (p : Polynomials K (n + 1)) : Polynomials K n :=
  eval₂Hom MvPolynomial.C (Fin.lastCases 1 MvPolynomial.X) (homogeneousComponent p.totalDegree p)

lemma normalizationParameter_ne_zero {K : Type} [Field K] [Infinite K] {n : ℕ}
    (p : Polynomials K (n + 1)) (hp : p ≠ 0) : normalizationParameter p ≠ 0 := by
  classical
  let H := homogeneousComponent p.totalDegree p
  have hH : H ≠ 0 := top_homogeneousComponent_ne_zero p hp
  have hprod : H * MvPolynomial.X (Fin.last n) ≠ 0 := mul_ne_zero hH (X_ne_zero _)
  obtain ⟨w, hw⟩ : ∃ w : Affine K (n + 1), eval w (H * MvPolynomial.X (Fin.last n)) ≠ 0 := by
    by_contra h
    push Not at h
    apply hprod
    apply MvPolynomial.funext
    intro w
    simpa only [map_zero] using h w
  rw [map_mul, eval_X] at hw
  have hwH := left_ne_zero_of_mul hw
  have hwl := right_ne_zero_of_mul hw
  let c : Affine K n := fun i => w i.castSucc / w (Fin.last n)
  have hv : evaluate (Fin.lastCases (1 : Polynomials K n) MvPolynomial.X) c =
      fun i => (w (Fin.last n))⁻¹ * w i := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [evaluate, hwl]
    · simp [evaluate, c, div_eq_mul_inv, mul_comm]
  have hval : eval c (normalizationParameter p) ≠ 0 := by
    unfold normalizationParameter
    rw [evaluation_substitution, hv, homogeneous_eval_scale _ (homogeneousComponent_isHomogeneous _ _)]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwl)) hwH
  intro h
  exact hval (by rw [h, map_zero])

lemma coeff_prod_sum_of_natDegree_le {A ι : Type} [CommRing A]
    (s : Finset ι) (f : ι → Polynomial A) (d : ι → ℕ)
    (hd : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hd j (Finset.mem_insert_of_mem hj))]
    · exact (Polynomial.natDegree_prod_le s f).trans (Finset.sum_le_sum (fun j hj => hd j (Finset.mem_insert_of_mem hj)))

lemma natDegree_eval₂_of_linear {K A : Type} [CommRing K] [CommRing A] {N : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (p : Polynomials K N) :
    (eval₂Hom (Polynomial.C.comp f) g p).natDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [eval₂Hom_monomial, Finsupp.prod_pow]
  apply Polynomial.natDegree_mul_le.trans
  simp only [RingHom.comp_apply, Polynomial.natDegree_C, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))))
  have he' : e.degree ≤ p.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using (le_totalDegree he)
  simpa only [mul_one, ← Finsupp.degree_eq_sum] using he' 

lemma coeff_eval₂_monomial_of_linear {K A : Type} [CommRing K] [CommRing A] {N D : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (e : Fin N →₀ ℕ) (c : K) (he : e.degree ≤ D) :
    (eval₂Hom (Polynomial.C.comp f) g (MvPolynomial.monomial e c)).coeff D =
      if e.degree = D then f c * ∏ i : Fin N, (g i).coeff 1 ^ e i else 0 := by
  classical
  rw [eval₂Hom_monomial, Finsupp.prod_pow]
  simp only [RingHom.comp_apply, Polynomial.coeff_C_mul]
  have hbound : (∏ i : Fin N, g i ^ e i).natDegree ≤ e.degree := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    apply le_trans (Finset.sum_le_sum (fun i _ =>
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hg i))))
    simp [Finsupp.degree_eq_sum]
  split_ifs with heq
  · have hcoeff := coeff_prod_sum_of_natDegree_le Finset.univ (fun i : Fin N => g i ^ e i)
      (fun i => e i) (fun i _ => Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left (e i) (hg i)))
    have hpows (i : Fin N) : (g i ^ e i).coeff (e i) = (g i).coeff 1 ^ e i := by
      simpa using (Polynomial.coeff_pow_of_natDegree_le (m := e i) (hg i))
    rw [← heq, Finsupp.degree_eq_sum, hcoeff]
    simp only [hpows]
  · have hlt : (∏ i : Fin N, g i ^ e i).natDegree < D := hbound.trans_lt (lt_of_le_of_ne he heq)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]

lemma coeff_eval₂_linear_top {K A : Type} [CommRing K] [CommRing A] {N D : ℕ}
    (f : K →+* A) (g : Fin N → Polynomial A) (hg : ∀ i, (g i).natDegree ≤ 1)
    (p : Polynomials K N) (hp : p.totalDegree ≤ D) :
    (eval₂Hom (Polynomial.C.comp f) g p).coeff D =
      eval₂Hom f (fun i => (g i).coeff 1) (homogeneousComponent D p) := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have hd0 : e.degree ≤ p.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree he
  have hd : e.degree ≤ D := hd0.trans hp
  rw [coeff_eval₂_monomial_of_linear f g hg e _ hd]
  split_ifs
  · rw [eval₂Hom_monomial, Finsupp.prod_pow]
  · rfl

noncomputable def normalizationLinearForms {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) : Fin (n + 1) → Polynomial (Polynomials K n) :=
  Fin.lastCases Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i) +
    Polynomial.C (MvPolynomial.C (c i)) * Polynomial.X)

lemma normalizationLinearForms_degree {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (i : Fin (n + 1)) : (normalizationLinearForms c i).natDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [normalizationLinearForms]
  · simp only [normalizationLinearForms, Fin.lastCases_castSucc]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    exact Polynomial.natDegree_mul_le.trans (by simp)

noncomputable def normalizationShear {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1)) : Polynomial (Polynomials K n) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c) p

lemma normalizationShear_top_coeff {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1)) :
    (normalizationShear c p).coeff p.totalDegree = MvPolynomial.C (eval c (normalizationParameter p)) := by
  rw [normalizationShear, coeff_eval₂_linear_top MvPolynomial.C _ (normalizationLinearForms_degree c) _ le_rfl]
  have heq : eval₂Hom MvPolynomial.C (fun i => (normalizationLinearForms c i).coeff 1) =
      MvPolynomial.C.comp (eval (Fin.lastCases 1 c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [normalizationLinearForms]
      · simp [normalizationLinearForms]
  rw [heq, RingHom.comp_apply]
  have hv : evaluate (Fin.lastCases (1 : Polynomials K n) MvPolynomial.X) c = Fin.lastCases 1 c := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [evaluate]
  rw [normalizationParameter, evaluation_substitution, hv]

lemma normalizationShear_unit_leadingCoeff {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) (p : Polynomials K (n + 1))
    (hc : eval c (normalizationParameter p) ≠ 0) :
    IsUnit (normalizationShear c p).leadingCoeff := by
  have hcoef : (normalizationShear c p).coeff p.totalDegree ≠ 0 := by
    rw [normalizationShear_top_coeff]
    simpa only [map_zero] using (MvPolynomial.C_injective (Fin n) K).ne hc
  have hdegree : (normalizationShear c p).natDegree = p.totalDegree :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_eval₂_of_linear MvPolynomial.C _ (normalizationLinearForms_degree c) p) hcoef
  rw [Polynomial.leadingCoeff, hdegree, normalizationShear_top_coeff]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

lemma normalizationShear_eval {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) :
    (normalizationShear c p).eval₂ (coordinatePullback Y (normalizationPolynomials c))
      (coordinate Y (Fin.last n)) = Ideal.Quotient.mk (vanishingIdeal ℂ Y) p := by
  let phi := Polynomial.eval₂RingHom (coordinatePullback Y (normalizationPolynomials c))
    (coordinate Y (Fin.last n))
  have heq : phi.comp (eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c)) =
      Ideal.Quotient.mk (vanishingIdeal ℂ Y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [phi, coordinatePullback]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [phi, normalizationLinearForms, coordinate]
      · simp [phi, normalizationLinearForms, coordinatePullback, normalizationPolynomials, coordinate]
  exact RingHom.congr_fun heq p

lemma normalization_last_integral {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) (hp : p ∈ vanishingIdeal ℂ Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    IsIntegral (Polynomials ℂ n) (coordinate Y (Fin.last n)) := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  let q := normalizationShear c p
  have hu : IsUnit q.leadingCoeff := normalizationShear_unit_leadingCoeff c p hc
  have hzero : q.eval₂ (coordinatePullback Y (normalizationPolynomials c))
      (coordinate Y (Fin.last n)) = 0 :=
    (normalizationShear_eval Y c p).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  refine ⟨hu.unit⁻¹.val • q, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu, ?_⟩
  change Polynomial.eval₂ (coordinatePullback Y (normalizationPolynomials c))
    (coordinate Y (Fin.last n)) (hu.unit⁻¹.val • q) = 0
  rw [Polynomial.eval₂_smul, hzero, mul_zero]

lemma normalization_adjoin_last_eq_top {n : ℕ} (Y : Set (Affine ℂ (n + 1))) (c : Affine ℂ n) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y)) = ⊤ := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  have halg : algebraMap (Polynomials ℂ n) (CoordinateRing Y) = coordinatePullback Y (normalizationPolynomials c) := rfl
  let S := Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  have hz : coordinate Y (Fin.last n) ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  have hvar (i : Fin (n + 1)) : coordinate Y i ∈ S := by
    refine Fin.lastCases hz (fun j => ?_) i
    have h := S.add_mem (S.algebraMap_mem (MvPolynomial.X j))
      (S.mul_mem (S.algebraMap_mem (MvPolynomial.C (c j))) hz)
    simpa [halg, coordinatePullback, coordinate, normalizationPolynomials] using h
  apply top_unique
  intro b hb
  clear hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [halg, coordinatePullback] using S.algebraMap_mem (MvPolynomial.C a)
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul, coordinate, S] using S.mul_mem hp (hvar i)

lemma normalization_module_finite {n : ℕ} (Y : Set (Affine ℂ (n + 1)))
    (c : Affine ℂ n) (p : Polynomials ℂ (n + 1)) (hp : p ∈ vanishingIdeal ℂ Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
    Module.Finite (Polynomials ℂ n) (CoordinateRing Y) := by
  classical
  letI : Algebra (Polynomials ℂ n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (normalizationPolynomials c)
  let S := Algebra.adjoin (Polynomials ℂ n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  letI : Module.Finite (Polynomials ℂ n) S :=
    Algebra.finite_adjoin_simple_of_isIntegral (normalization_last_integral Y c p hp hc)
  apply Module.Finite.of_surjective S.val.toLinearMap
  intro b
  have hS : S = ⊤ := normalization_adjoin_last_eq_top Y c
  have hb : b ∈ S := by rw [hS]; trivial
  exact ⟨⟨b, hb⟩, rfl⟩

lemma module_finite_finiteMorphism {K : Type} [Field K] {n m : ℕ}
    (Y : Set (Affine K n)) (F : PolynomialMap K n m) :
    letI : Algebra (Polynomials K m) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
    Module.Finite (Polynomials K m) (CoordinateRing Y) → FiniteMorphism Y F := by
  classical
  letI : Algebra (Polynomials K m) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  intro hfinite
  letI := hfinite
  have halg : algebraMap (Polynomials K m) (CoordinateRing Y) = coordinatePullback Y F := rfl
  obtain ⟨s, g, hgen⟩ := Module.Finite.exists_fin (R := Polynomials K m) (M := CoordinateRing Y)
  choose representatives hrep using fun i => Ideal.Quotient.mk_surjective (g i)
  refine ⟨s, representatives, ?_⟩
  intro p
  have hp : Ideal.Quotient.mk (vanishingIdeal K Y) p ∈ Submodule.span (Polynomials K m) (Set.range g) := by
    rw [hgen]; trivial
  obtain ⟨coefficients, hcoeff⟩ := (Submodule.mem_span_range_iff_exists_fun (Polynomials K m)).mp hp
  refine ⟨coefficients, ?_⟩
  have hz : p - ∑ i : Fin s, eval₂Hom MvPolynomial.C F (coefficients i) * representatives i ∈
      vanishingIdeal K Y := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_sum]
    apply sub_eq_zero.mpr
    have h := hcoeff.symm
    simpa only [Algebra.smul_def, halg, coordinatePullback, RingHom.comp_apply, map_mul, hrep] using h
  intro x hx
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
    evaluation_substitution, sub_eq_zero] using hz x hx

lemma coordinatePullback_injective_of_finite_dimension {K : Type} [Field K] {a n : ℕ}
    (Y : Set (Affine K a)) (F : PolynomialMap K a n)
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞))
    (hfinite : letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
      Module.Finite (Polynomials K n) (CoordinateRing Y)) :
    Function.Injective (coordinatePullback Y F) := by
  classical
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  letI : Module.Finite (Polynomials K n) (CoordinateRing Y) := hfinite
  let f : Polynomials K n →+* CoordinateRing Y := algebraMap (Polynomials K n) (CoordinateRing Y)
  have hf : f.IsIntegral := Algebra.IsIntegral.isIntegral
  have hdimBound := ringKrullDim_le_of_ringHom_isIntegral f.kerLift hf.kerLift
  have hdimBase : ringKrullDim (Polynomials K n) = ((n : ℕ∞) : WithBot ℕ∞) := by simp [Polynomials]
  change ringKrullDim (CoordinateRing Y) = ((n : ℕ∞) : WithBot ℕ∞) at hdim
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨r, hr, hrne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hquot := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk (RingHom.ker f))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hrne)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  have hbad := (add_le_add hdimBound le_rfl).trans hquot
  rw [hdim, hdimBase] at hbad
  have hn : n + 1 ≤ n := by exact_mod_cast hbad
  omega

lemma vanishingIdeal_ne_bot_of_codimension_one {K : Type} [Field K] {n : ℕ}
    (Y : Set (Affine K (n + 1)))
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞)) : vanishingIdeal K Y ≠ ⊥ := by
  intro h
  change ringKrullDim (Polynomials K (n + 1) ⧸ vanishingIdeal K Y) = ((n : ℕ∞) : WithBot ℕ∞) at hdim
  rw [h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdim
  have hn : n + 1 = n := by exact_mod_cast (by simpa [Polynomials] using hdim :
    (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞))
  omega

lemma module_finite_coordinatesIntegral {K : Type} [Field K] {a n : ℕ}
    (Y : Set (Affine K a)) (hY : IrreducibleAffine Y) (F : PolynomialMap K a n)
    (hfinite : letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
      Module.Finite (Polynomials K n) (CoordinateRing Y)) : CoordinatesIntegral Y F := by
  classical
  letI : (vanishingIdeal K Y).IsPrime := irreducibleAffine_ideal_prime hY
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y F
  letI : Module.Finite (Polynomials K n) (CoordinateRing Y) := hfinite
  have halg : algebraMap (Polynomials K n) (CoordinateRing Y) = coordinatePullback Y F := rfl
  intro j
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := Polynomials K n) (coordinate Y j)
  have hd : 0 < p.natDegree := by
    by_contra h
    have hp1 := Polynomial.eq_one_of_monic_natDegree_zero hp (Nat.eq_zero_of_not_pos h)
    simpa [hp1] using hroot
  refine ⟨p.natDegree, hd, fun i => p.coeff i.val, ?_⟩
  intro x hx
  let ex : CoordinateRing Y →+* K := Ideal.Quotient.lift (vanishingIdeal K Y)
    (MvPolynomial.eval x) (fun q hq => by
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hq x hx)
  have hcomp : ex.comp (algebraMap (Polynomials K n) (CoordinateRing Y)) = eval (evaluate F x) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [ex, halg, coordinatePullback]
    · intro i; simp [ex, halg, coordinatePullback, evaluate]
  have hz : ex (coordinate Y j) = x j := by simp [ex, coordinate]
  have hpoint : Polynomial.eval₂ (eval (evaluate F x)) (x j) p = 0 := by
    have h := congrArg ex hroot
    rw [Polynomial.hom_eval₂, hcomp, hz, map_zero] at h
    exact h
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpoint
  rw [← Fin.sum_univ_eq_sum_range] at hpoint
  simpa only [add_comm] using hpoint

end APSCounting893.Main

open APSCounting893.Main

theorem solution (n : ℕ) (hn : 0 < n) (Y : Set (Affine ℂ (n + 1)))
    (hirr : IrreducibleAffine Y)
    (hdim : RSCapacity.algDim Y = ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ O : Set (Affine ℂ n), O.Nonempty ∧ RelativeOpen Set.univ O ∧
      ∀ c ∈ O, IsNormalization Y c := by
  classical
  obtain ⟨p, hp, hpne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (vanishingIdeal_ne_bot_of_codimension_one Y hdim)
  let P := normalizationParameter p
  have hP : P ≠ 0 := normalizationParameter_ne_zero p hpne
  let O : Set (Affine ℂ n) := {c | eval c P ≠ 0}
  have hO : O.Nonempty := by
    by_contra h
    apply hP
    apply MvPolynomial.funext
    intro c
    have hc : eval c P = 0 := by
      by_contra hc
      exact h ⟨c, hc⟩
    simpa only [map_zero] using hc
  refine ⟨O, hO, ?_, ?_⟩
  · refine ⟨Set.subset_univ _, ⟨{P}, ?_⟩⟩
    ext c
    simp [O, RSCapacity.zeroSet]
  · intro c hc
    have hc' : eval c (normalizationParameter p) ≠ 0 := hc
    have hmodule := normalization_module_finite Y c p hp hc'
    have hfin := module_finite_finiteMorphism Y (normalizationPolynomials c) hmodule
    have hinj := coordinatePullback_injective_of_finite_dimension Y (normalizationPolynomials c) hdim hmodule
    have hsurj : normalization c '' Y = Set.univ := by
      change evaluate (normalizationPolynomials c) '' Y = Set.univ
      rw [finiteMorphism_image Y hirr.2.1 _ hfin,
        (RingHom.injective_iff_ker_eq_bot _).mp hinj, zeroLocus_bot]
      rfl
    refine ⟨hfin, hsurj, ?_, module_finite_coordinatesIntegral Y hirr (normalizationPolynomials c) hmodule⟩
    intro f hf y hy
    obtain ⟨x, hx, hxy⟩ := (Set.ext_iff.mp hsurj y).mpr (Set.mem_univ y)
    exact hxy ▸ hf x hx
