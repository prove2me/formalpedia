-- Prove2me | solution 1 for APSCounting893.Main.dominant_graph_components
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:23:22.773718+00:00
-- url     : https://prove2.me/submissions/fe2a696a-29aa-4199-9610-ce3a0b783a1a

import Definitions.Def_APSCounting893_Main_LineGeometry
import Theorems.Thm_DiazModulus_card_le_height_add_of_ringKrullDim_quotient_le

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

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


end APSCounting893.Main

end


section

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


end APSCounting893.Main

end


section

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


end APSCounting893.Main

end


section
open MvPolynomial
namespace APSCounting893.Main
lemma monic_from_relation {A : Type} [CommRing A] [Nontrivial A] {d : ℕ} (a : Fin d → A) :
    (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ i.val).Monic := by
  classical
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le (by simp)
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact Polynomial.natDegree_mul_le.trans (by simpa using i.isLt.le)
  · have hcoeff (i : Fin d) : (Polynomial.C (a i) * Polynomial.X ^ i.val).coeff d = 0 := by
      simp [ne_of_gt i.isLt, Ne.symm (ne_of_gt i.isLt)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_self, Polynomial.finsetSum_coeff,
      hcoeff, Finset.sum_const_zero, add_zero]


end APSCounting893.Main

end


section
open MvPolynomial
namespace APSCounting893.Main
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


end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma zClosure_minimal {K : Type} [Field K] {n : ℕ}
    {S C : Set (Affine K n)} (hC : RSCapacity.IsAlgSet C) (hSC : S ⊆ C) :
    RSCapacity.zClosure S ⊆ C := by
  rw [isAlgSet_eq_zeroLocus hC]
  exact zeroLocus_anti_mono (vanishingIdeal_anti_mono hSC)

lemma isAlgSet_empty {K : Type} [Field K] {n : ℕ} :
    RSCapacity.IsAlgSet (∅ : Set (Affine K n)) := by
  refine ⟨{1}, ?_⟩
  ext x
  simp [RSCapacity.zeroSet]

lemma isAlgSet_union {K : Type} [Field K] {n : ℕ} {A B : Set (Affine K n)}
    (hA : RSCapacity.IsAlgSet A) (hB : RSCapacity.IsAlgSet B) :
    RSCapacity.IsAlgSet (A ∪ B) := by
  classical
  let S : Set (Polynomials K n) := {p | ∃ a ∈ vanishingIdeal K A,
    ∃ b ∈ vanishingIdeal K B, p = a * b}
  refine ⟨S, ?_⟩
  ext x
  constructor
  · intro hx p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := hp
    rw [map_mul]
    rcases hx with hx | hx
    · have hz := ha x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, zero_mul] using congrArg (fun c => c * eval x b) hz
    · have hz := hb x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, mul_zero] using congrArg (fun c => eval x a * c) hz
  · intro hx
    by_contra hn
    have hxA : x ∉ zeroLocus K (vanishingIdeal K A) := by
      rw [← isAlgSet_eq_zeroLocus hA]
      exact fun h => hn (Or.inl h)
    have hxB : x ∉ zeroLocus K (vanishingIdeal K B) := by
      rw [← isAlgSet_eq_zeroLocus hB]
      exact fun h => hn (Or.inr h)
    simp only [mem_zeroLocus_iff, not_forall] at hxA hxB
    obtain ⟨a, ha, hax⟩ := hxA
    obtain ⟨b, hb, hbx⟩ := hxB
    have hz := hx (a * b) ⟨a, ha, b, hb, rfl⟩
    simp only [map_mul] at hz
    exact (mul_ne_zero (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hax)
      (by simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hbx)) hz

lemma isAlgSet_finset_union {K ι : Type} [Field K] {n : ℕ}
    (s : Finset ι) (Z : ι → Set (Affine K n)) (hZ : ∀ q ∈ s, RSCapacity.IsAlgSet (Z q)) :
    RSCapacity.IsAlgSet (⋃ q ∈ s, Z q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isAlgSet_empty (K := K) (n := n))
  | @insert q s hq ih =>
      rw [Finset.set_biUnion_insert]
      exact isAlgSet_union (hZ q (Finset.mem_insert_self _ _))
        (ih (fun r hr => hZ r (Finset.mem_insert_of_mem hr)))

lemma irreducibleAffine_finset_cover {K ι : Type} [Field K] {n : ℕ}
    (W : Set (Affine K n)) (hW : IrreducibleAffine W)
    (s : Finset ι) (Z : ι → Set (Affine K n)) (hZ : ∀ q ∈ s, RSCapacity.IsAlgSet (Z q))
    (hcover : W ⊆ ⋃ q ∈ s, Z q) : ∃ q ∈ s, W ⊆ Z q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hW.1
      simpa using hcover hx
  | @insert q s hq ih =>
      rw [Finset.set_biUnion_insert] at hcover
      have hZs : ∀ r ∈ s, RSCapacity.IsAlgSet (Z r) :=
        fun r hr => hZ r (Finset.mem_insert_of_mem hr)
      rcases hW.2.2 (Z q) (⋃ r ∈ s, Z r) (hZ q (Finset.mem_insert_self _ _))
          (isAlgSet_finset_union s Z hZs) hcover with hqW | hsW
      · exact ⟨q, Finset.mem_insert_self _ _, hqW⟩
      · obtain ⟨r, hr, hWr⟩ := ih hZs hsW
        exact ⟨r, Finset.mem_insert_of_mem hr, hWr⟩

lemma affineComponent_closure_relativeOpen {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (A S W : Set (Affine K n)) (hA : RSCapacity.IsAlgSet A) (hS : RelativeOpen A S)
    (hW : AffineComponent (RSCapacity.zClosure S) W) :
    AffineComponent A W ∧ (W ∩ S).Nonempty := by
  classical
  let I := vanishingIdeal K A
  let s := I.finite_minimalPrimes_of_isNoetherianRing.toFinset
  let Z : Ideal (Polynomials K n) → Set (Affine K n) := fun q => zeroLocus K q
  let t := s.filter (fun q => ¬ Z q ⊆ A \ S)
  let B : Set (Affine K n) := ⋃ q ∈ t, Z q
  have hcomp (q : Ideal (Polynomials K n)) (hq : q ∈ s) : AffineComponent A (Z q) :=
    affineComponent_of_minimal hA q (by simpa only [s, I, Set.Finite.mem_toFinset, Ideal.minimalPrimes, Set.mem_setOf_eq] using hq)
  have hB : RSCapacity.IsAlgSet B := isAlgSet_finset_union t Z (fun q _ => isAlgSet_zeroLocus q)
  have hSB : S ⊆ B := by
    intro x hx
    have hI : I ≤ vanishingIdeal K ({x} : Set (Affine K n)) :=
      vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr (hS.1 hx))
    obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le hI
    have hxq : x ∈ Z q := fun p hp => hqx hp x (Set.mem_singleton x)
    have hqt : q ∈ t := Finset.mem_filter.mpr ⟨by simpa [s] using hq, fun he => (he hxq).2 hx⟩
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqt, hxq⟩⟩
  have hDB : RSCapacity.zClosure S ⊆ B := zClosure_minimal hB hSB
  obtain ⟨q, hqt, hWq⟩ := irreducibleAffine_finset_cover W hW.1 t Z
    (fun q _ => isAlgSet_zeroLocus q) (hW.2.1.trans hDB)
  have hqcomp := hcomp q (Finset.mem_filter.mp hqt).1
  have hqnot := (Finset.mem_filter.mp hqt).2
  have hAcover : A ⊆ RSCapacity.zClosure S ∪ (A \ S) := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl (zeroLocus_vanishingIdeal_le S h)
    · exact Or.inr ⟨hx, h⟩
  have hqD : Z q ⊆ RSCapacity.zClosure S := by
    exact (hqcomp.1.2.2 _ _ (isAlgSet_zeroLocus _) hS.2 (hqcomp.2.1.trans hAcover)).resolve_right hqnot
  have hWeq : Z q = W := hW.2.2 (Z q) hqcomp.1 hWq hqD
  constructor
  · simpa only [hWeq] using hqcomp
  · have hn : ∃ x ∈ Z q, x ∉ A \ S := Set.not_subset.mp hqnot
    obtain ⟨x, hx, hxnot⟩ := hn
    refine ⟨x, ?_, ?_⟩
    · rwa [← hWeq]
    · by_contra hxs
      exact hxnot ⟨hqcomp.2.1 hx, hxs⟩

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma graph_component_linePreimage (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    AffineComponent {x | evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha} W ∧
      ∃ x ∈ W, evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha ∩ normalizationOpen F D.c D.U := by
  let A : Set (Affine ℂ F.n) := {x | evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha}
  let S : Set (Affine ℂ F.n) := {x | evaluate (betaPolynomials F D.c) x ∈
    affineLine 0 D.alpha ∩ normalizationOpen F D.c D.U}
  have hA : RSCapacity.IsAlgSet A := isAlgSet_preimage_evaluate _ (isAlgSet_affineLine _ _ D.nonzero)
  have hrel : RelativeOpen A S := by
    refine ⟨fun _ h => h.1, ?_⟩
    have heq : A \ S = A ∩ (evaluate (betaPolynomials F D.c) ⁻¹'
        (normalization D.c '' (imageClosure F.F \ D.U))) := by
      ext x
      simp only [A, S, Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_preimage, normalizationOpen, Set.mem_compl_iff]
      tauto
    rw [heq]
    exact isAlgSet_inter hA (isAlgSet_preimage_evaluate _ (normalizationOpen_closed_complement F D))
  obtain ⟨hcomp, x, hxW, hxS⟩ := affineComponent_closure_relativeOpen A S W hA hrel hW
  exact ⟨hcomp, x, hxW, hxS⟩

lemma linePreimage_eq_zeroLocus_span (F : ReducedMap) (D : LineData F)
    (k : Fin F.n) (hk : D.alpha k ≠ 0) :
    let p : Fin F.n → Polynomials ℂ F.n := fun j =>
      MvPolynomial.C (D.alpha k) * betaPolynomials F D.c j -
        MvPolynomial.C (D.alpha j) * betaPolynomials F D.c k
    {x | evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha} =
      zeroLocus ℂ (Ideal.span (↑((Finset.univ.erase k).image p) : Set (Polynomials ℂ F.n))) := by
  classical
  intro p
  rw [MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · rintro ⟨t, ht⟩ q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have heq : evaluate (betaPolynomials F D.c) x = t • D.alpha := by simpa using ht.symm
    have hxj := congrFun heq j
    have hxk := congrFun heq k
    simp only [p, aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_mul, eval_C]
    change D.alpha k * evaluate (betaPolynomials F D.c) x j -
      D.alpha j * evaluate (betaPolynomials F D.c) x k = 0
    rw [hxj, hxk]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro hx
    have hcross (j : Fin F.n) : D.alpha k * evaluate (betaPolynomials F D.c) x j -
        D.alpha j * evaluate (betaPolynomials F D.c) x k = 0 := by
      by_cases hj : j = k
      · subst j; ring
      · have hh := hx (p j) (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩, rfl⟩)
        simpa only [p, aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_mul, eval_C, evaluate] using hh
    refine ⟨evaluate (betaPolynomials F D.c) x k / D.alpha k, ?_⟩
    funext j
    have he : evaluate (betaPolynomials F D.c) x j =
        D.alpha j * evaluate (betaPolynomials F D.c) x k / D.alpha k :=
      (eq_div_iff hk).mpr (by simpa only [mul_comm] using sub_eq_zero.mp (hcross j))
    simp only [Pi.zero_apply, zero_add, Pi.smul_apply, smul_eq_mul]
    rw [he]
    ring

lemma graph_component_height_bound (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    (vanishingIdeal ℂ W).height ≤ (F.n - 1 : ℕ) := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp D.nonzero
  let p : Fin F.n → Polynomials ℂ F.n := fun j =>
    MvPolynomial.C (D.alpha k) * betaPolynomials F D.c j -
      MvPolynomial.C (D.alpha j) * betaPolynomials F D.c k
  let s := (Finset.univ.erase k).image p
  have hmin := affineComponent_ideal_minimal
    (isAlgSet_preimage_evaluate (betaPolynomials F D.c) (isAlgSet_affineLine _ _ D.nonzero))
    (graph_component_linePreimage F D W hW).1
  change (vanishingIdeal ℂ {x | evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha}).IsMinimalPrime (vanishingIdeal ℂ W) at hmin
  rw [linePreimage_eq_zeroLocus_span F D k hk,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmin
  have hm : vanishingIdeal ℂ W ∈ (Ideal.span (s : Set (Polynomials ℂ F.n))).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes]
    exact hmin
  have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hm
  have hcard : s.card ≤ F.n - 1 := by
    apply Finset.card_image_le.trans
    simp
  exact hheight.trans (by exact_mod_cast hcard)

lemma graph_component_dimension_positive (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    ¬ ringKrullDim (CoordinateRing W) ≤ 0 := by
  intro hdim
  have hcard := DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le
    (vanishingIdeal ℂ W) (irreducibleAffine_ideal_prime hW.1) 0 hdim
  have hheight := graph_component_height_bound F D W hW
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_zero, add_zero] at hcard
  have hh : (F.n : ℕ∞) ≤ (F.n - 1 : ℕ) := hcard.trans hheight
  have hh' : F.n ≤ F.n - 1 := by exact_mod_cast hh
  have hn := F.positive
  omega

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finiteOverOpen_constant_moduleFinite {K : Type} [Field K] {n m : ℕ}
    (F : PolynomialMap K n m) (U : Set (Affine K m)) (hF : FiniteOverOpen Set.univ F U)
    (W : Set (Affine K n)) (y : Affine K m) (hy : y ∈ U)
    (hconstant : ∀ x ∈ W, evaluate F x = y) : Module.Finite K (CoordinateRing W) := by
  classical
  obtain ⟨b, hb, hbU, s, generators, hgen⟩ := hF y hy
  let g : Fin s → CoordinateRing W := fun i => Ideal.Quotient.mk _ (generators i)
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [Submodule.eq_top_iff']
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨coefficients, exponents, hcoeff⟩ := hgen p
  let c : Fin s → K := fun i => eval y (coefficients i) / eval y b ^ exponents i
  have hz : p - ∑ i : Fin s, MvPolynomial.C (c i) * generators i ∈ vanishingIdeal K W := by
    intro x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_sum, map_mul,
      eval_C, sub_eq_zero]
    have h := hcoeff x (Set.mem_univ x) (by rwa [hconstant x hx])
    simpa only [hconstant x hx] using h
  have heq : Ideal.Quotient.mk (vanishingIdeal K W) p = ∑ i : Fin s, c i • g i := by
    apply sub_eq_zero.mp
    have hmem : p - ∑ i : Fin s, c i • generators i ∈ vanishingIdeal K W := by
      simpa only [MvPolynomial.smul_eq_C_mul] using hz
    have h := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    change (Ideal.Quotient.mkₐ K (vanishingIdeal K W)) (p - ∑ i : Fin s, c i • generators i) = 0 at h
    simpa only [map_sub, map_sum, map_smul, g, Ideal.Quotient.mkₐ_eq_mk] using h

  rw [heq]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

lemma integral_eq_complex_constant {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    (x : A) (hx : IsIntegral ℂ x) : ∃ c : ℂ, algebraMap ℂ A c = x := by
  let p := minpoly ℂ x
  have hmonic : p.leadingCoeff = 1 := minpoly.monic hx
  have hdeg : p.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hx)
  have hroot : Polynomial.aeval x p = 0 := minpoly.aeval ℂ x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg, hmonic, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hroot
  exact ⟨-p.coeff 0, by rw [map_neg]; exact hroot.symm⟩

lemma normalization_constant_outputs (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : IrreducibleAffine W)
    (u : Affine ℂ F.n) (hu : ∀ x ∈ W, evaluate (betaPolynomials F D.c) x = u) :
    ∃ y : Affine ℂ (F.n + 1), ∀ x ∈ W, evaluate F.F x = y := by
  classical
  letI : (vanishingIdeal ℂ W).IsPrime := irreducibleAffine_ideal_prime hW
  let q := Ideal.Quotient.mk (vanishingIdeal ℂ W)
  have hC (c : ℂ) : q (MvPolynomial.C c) = algebraMap ℂ (CoordinateRing W) c := rfl
  have hint (j : Fin (F.n + 1)) : IsIntegral ℂ (q (F.F j)) := by
    obtain ⟨d, hd, A, hA⟩ := D.normalization.2.2.2 j
    let c : Fin d → ℂ := fun i => eval u (A i)
    have hpoly : F.F j ^ d + ∑ i : Fin d, MvPolynomial.C (c i) * F.F j ^ i.val ∈ vanishingIdeal ℂ W := by
      intro x hx
      have hwY : evaluate F.F x ∈ imageClosure F.F :=
        zeroLocus_vanishingIdeal_le (Set.range (evaluate F.F)) (Set.mem_range_self x)
      have hnorm : normalization D.c (evaluate F.F x) = u := by rw [← evaluate_beta]; exact hu x hx
      have hh := hA (evaluate F.F x) hwY
      change evaluate F.F x j ^ d + ∑ i : Fin d,
        eval (normalization D.c (evaluate F.F x)) (A i) * evaluate F.F x j ^ i.val = 0 at hh
      rw [hnorm] at hh
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_add, map_sum, map_mul,
        map_pow, eval_C, c, evaluate] using hh

    refine ⟨Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (c i) * Polynomial.X ^ i.val,
      monic_from_relation c, ?_⟩
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hpoly
    simpa only [map_add, map_sum, map_mul, map_pow, ← hC, q, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] using hzero
  choose y hy using fun j => integral_eq_complex_constant _ (hint j)
  refine ⟨y, ?_⟩
  intro x hx
  funext j
  have hq : q (MvPolynomial.C (y j) - F.F j) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (hy j)
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hq
  have h := hmem x hx
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, eval_C, sub_eq_zero] at h
  exact h.symm

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma graph_component_not_constant (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    ¬ ∃ u : Affine ℂ F.n, ∀ x ∈ W, evaluate (betaPolynomials F D.c) x = u := by
  rintro ⟨u, hu⟩
  obtain ⟨y, hy⟩ := normalization_constant_outputs F D W hW.1 u hu
  obtain ⟨x, hx, hgood⟩ := (graph_component_linePreimage F D W hW).2
  have hyY : y ∈ imageClosure F.F := by
    rw [← hy x hx]
    exact zeroLocus_vanishingIdeal_le (Set.range (evaluate F.F)) (Set.mem_range_self x)
  have hyU : y ∈ D.U := by
    by_contra hnot
    apply hgood.2
    refine ⟨y, ⟨hyY, hnot⟩, ?_⟩
    rw [← hy x hx, ← evaluate_beta]
  letI : (vanishingIdeal ℂ W).IsPrime := irreducibleAffine_ideal_prime hW.1
  letI : Module.Finite ℂ (CoordinateRing W) :=
    finiteOverOpen_constant_moduleFinite F.F D.U D.goodOpen.2.2.2 W y hyU hy
  have hfield : IsField (CoordinateRing W) :=
    isField_of_isIntegral_of_isField' (R := ℂ) (Field.toIsField ℂ)
  exact graph_component_dimension_positive F D W hW
    (le_of_eq (ringKrullDim_eq_zero_of_isField hfield))

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def lineParameterPolynomial (F : ReducedMap) (D : LineData F) (k : Fin F.n) :
    Polynomials ℂ F.n := MvPolynomial.C ((D.alpha k)⁻¹) * betaPolynomials F D.c k

lemma lineParameter_beta_values (F : ReducedMap) (D : LineData F) (k : Fin F.n) (hk : D.alpha k ≠ 0)
    (x : Affine ℂ F.n) (hx : evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha) :
    ∀ j, evaluate (betaPolynomials F D.c) x j = D.alpha j * eval x (lineParameterPolynomial F D k) := by
  obtain ⟨t, ht⟩ := hx
  have heq : evaluate (betaPolynomials F D.c) x = t • D.alpha := by simpa using ht.symm
  intro j
  have hj := congrFun heq j
  have hkx := congrFun heq k
  simp only [lineParameterPolynomial, map_mul, eval_C]
  change evaluate (betaPolynomials F D.c) x j = D.alpha j * ((D.alpha k)⁻¹ * evaluate (betaPolynomials F D.c) x k)
  rw [hj, hkx]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

lemma graph_parameter_beta_quotient (F : ReducedMap) (D : LineData F) (k : Fin F.n) (hk : D.alpha k ≠ 0)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    ∀ j, Ideal.Quotient.mk (vanishingIdeal ℂ W) (betaPolynomials F D.c j) =
      algebraMap ℂ (CoordinateRing W) (D.alpha j) *
        Ideal.Quotient.mk (vanishingIdeal ℂ W) (lineParameterPolynomial F D k) := by
  intro j
  have hrel : betaPolynomials F D.c j - MvPolynomial.C (D.alpha j) * lineParameterPolynomial F D k ∈
      vanishingIdeal ℂ W := by
    intro x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, map_mul, eval_C, sub_eq_zero]
    exact lineParameter_beta_values F D k hk x ((graph_component_linePreimage F D W hW).1.2.1 hx) j
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr hrel
  rw [map_sub, map_mul, sub_eq_zero] at h
  exact h

lemma graph_parameter_transcendental (F : ReducedMap) (D : LineData F) (k : Fin F.n) (hk : D.alpha k ≠ 0)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    Transcendental ℂ (Ideal.Quotient.mk (vanishingIdeal ℂ W) (lineParameterPolynomial F D k)) := by
  classical
  letI : (vanishingIdeal ℂ W).IsPrime := irreducibleAffine_ideal_prime hW.1
  intro hAlg
  obtain ⟨c, hc⟩ := integral_eq_complex_constant _ hAlg.isIntegral
  have hrel : MvPolynomial.C c - lineParameterPolynomial F D k ∈ vanishingIdeal ℂ W := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hc
  apply graph_component_not_constant F D W hW
  refine ⟨c • D.alpha, ?_⟩
  intro x hx
  funext j
  have hp : eval x (lineParameterPolynomial F D k) = c := by
    have h := hrel x hx
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, map_sub, eval_C, sub_eq_zero] at h
    exact h.symm
  rw [lineParameter_beta_values F D k hk x ((graph_component_linePreimage F D W hW).1.2.1 hx) j, hp]
  simp [mul_comm]

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma graph_component_dominant (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    RSCapacity.zClosure (evaluate (betaPolynomials F D.c) '' W) = affineLine 0 D.alpha := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp D.nonzero
  let T := Ideal.Quotient.mk (vanishingIdeal ℂ W) (lineParameterPolynomial F D k)
  have hT : Transcendental ℂ T := graph_parameter_transcendental F D k hk W hW
  let lift : Polynomials ℂ F.n →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C
    (fun j => Polynomial.C (D.alpha j) * Polynomial.X)
  let a : Polynomial ℂ →+* CoordinateRing W := (Polynomial.aeval T).toRingHom
  have ha (p : Polynomials ℂ F.n) : a (lift p) = coordinatePullback W (betaPolynomials F D.c) p := by
    have heq : a.comp lift = coordinatePullback W (betaPolynomials F D.c) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change (Polynomial.aeval T) ((MvPolynomial.eval₂Hom Polynomial.C
          (fun j => Polynomial.C (D.alpha j) * Polynomial.X)) (MvPolynomial.C c)) = _
        rw [MvPolynomial.eval₂Hom_C, Polynomial.aeval_C]
        simp only [coordinatePullback, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        rfl
      · intro j
        change (Polynomial.aeval T) ((MvPolynomial.eval₂Hom Polynomial.C
          (fun j => Polynomial.C (D.alpha j) * Polynomial.X)) (MvPolynomial.X j)) = _
        rw [MvPolynomial.eval₂Hom_X', map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
        simp only [coordinatePullback, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        exact (graph_parameter_beta_quotient F D k hk W hW j).symm
    exact RingHom.congr_fun heq p
  apply Set.Subset.antisymm
  · exact zClosure_minimal (isAlgSet_affineLine _ _ D.nonzero) (by
      rintro u ⟨x, hx, rfl⟩
      exact (graph_component_linePreimage F D W hW).1.2.1 hx)
  · rintro u ⟨t, rfl⟩ p hp
    have hrel : coordinatePullback W (betaPolynomials F D.c) p = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      intro x hx
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using
        hp (evaluate (betaPolynomials F D.c) x) ⟨x, hx, rfl⟩
    have hpoly : lift p = 0 := (transcendental_iff_injective.mp hT) (by
      change a (lift p) = a 0
      rw [ha, hrel, map_zero])
    have hcomp : (Polynomial.evalRingHom t).comp lift =
        MvPolynomial.eval (t • D.alpha) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, lift, eval₂Hom_C, Polynomial.coe_evalRingHom, Polynomial.eval_C, MvPolynomial.eval_C]
      · intro j
        simp only [RingHom.comp_apply, lift, eval₂Hom_X', Polynomial.coe_evalRingHom, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, MvPolynomial.eval_X, Pi.smul_apply, smul_eq_mul]
        exact mul_comm _ _
    have hh := congrArg (Polynomial.evalRingHom t) hpoly
    rw [map_zero] at hh
    change ((Polynomial.evalRingHom t).comp lift) p = 0 at hh
    rw [hcomp] at hh
    simpa only [zero_add, aeval_def, Algebra.algebraMap_self, eval₂_id] using hh

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma aeval_substitution {E : Type} [CommRing E] [Algebra ℂ E] {n m : ℕ}
    (F : PolynomialMap ℂ n m) (p : Polynomials ℂ m) (x : Fin n → E) :
    (MvPolynomial.aeval x) (eval₂Hom MvPolynomial.C F p) =
      (MvPolynomial.aeval (fun j => (MvPolynomial.aeval x) (F j))) p := by
  have heq : (MvPolynomial.aeval x).toRingHom.comp (eval₂Hom MvPolynomial.C F) =
      (MvPolynomial.aeval (fun j => (MvPolynomial.aeval x) (F j))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  exact RingHom.congr_fun heq p

lemma coordinate_aeval_eq {n : ℕ} (W : Set (Affine ℂ n))
    (E : Type) [Field E] [Algebra (CoordinateRing W) E] [Algebra ℂ E]
    [IsScalarTower ℂ (CoordinateRing W) E] (p : Polynomials ℂ n) :
    (MvPolynomial.aeval (fun j => algebraMap (CoordinateRing W) E (coordinate W j))) p =
      algebraMap (CoordinateRing W) E (Ideal.Quotient.mk _ p) := by
  have heq : (MvPolynomial.aeval (fun j => algebraMap (CoordinateRing W) E (coordinate W j))).toRingHom =
      (algebraMap (CoordinateRing W) E).comp (Ideal.Quotient.mk (vanishingIdeal ℂ W)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change (MvPolynomial.aeval (fun j => algebraMap (CoordinateRing W) E (coordinate W j))) (MvPolynomial.C c) = _
      rw [MvPolynomial.aeval_C]
      simp only [RingHom.comp_apply]
      change algebraMap ℂ E c = algebraMap (CoordinateRing W) E (algebraMap ℂ (CoordinateRing W) c)
      exact IsScalarTower.algebraMap_apply ℂ (CoordinateRing W) E c
    · intro j
      change (MvPolynomial.aeval (fun j => algebraMap (CoordinateRing W) E (coordinate W j))) (MvPolynomial.X j) = _
      rw [MvPolynomial.aeval_X]
      rfl
  exact RingHom.congr_fun heq p

lemma output_coordinates_integral (F : ReducedMap) (D : LineData F)
    (E : Type) [Field E] [Algebra ℂ E] [Algebra (Polynomial ℂ) E]
    [IsScalarTower ℂ (Polynomial ℂ) E]
    (x : Fin F.n → E)
    (hbeta : ∀ j, MvPolynomial.aeval x (betaPolynomials F D.c j) =
      algebraMap ℂ E (D.alpha j) * algebraMap (Polynomial ℂ) E Polynomial.X) :
    ∀ j, IsIntegral (Polynomial ℂ) ((MvPolynomial.aeval x) (F.F j)) := by
  classical
  let y : Fin (F.n + 1) → E := fun j => (MvPolynomial.aeval x) (F.F j)
  let v : Fin F.n → E := fun j => algebraMap ℂ E (D.alpha j) * algebraMap (Polynomial ℂ) E Polynomial.X
  have hnorm (j : Fin F.n) : MvPolynomial.aeval y (normalizationPolynomials D.c j) = v j := by
    rw [← aeval_substitution]
    exact hbeta j
  let vpoly : Fin F.n → Polynomial ℂ := fun j => Polynomial.C (D.alpha j) * Polynomial.X
  let polyLift : Polynomials ℂ F.n →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C vpoly
  have hlift (p : Polynomials ℂ F.n) : algebraMap (Polynomial ℂ) E (polyLift p) = MvPolynomial.aeval v p := by
    have heq : (algebraMap (Polynomial ℂ) E).comp polyLift = (MvPolynomial.aeval v).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change algebraMap (Polynomial ℂ) E ((MvPolynomial.eval₂Hom Polynomial.C vpoly) (MvPolynomial.C c)) = (MvPolynomial.aeval v) (MvPolynomial.C c)
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
        change algebraMap (Polynomial ℂ) E (algebraMap ℂ (Polynomial ℂ) c) = _
        exact (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) E c).symm
      · intro j
        change algebraMap (Polynomial ℂ) E ((MvPolynomial.eval₂Hom Polynomial.C vpoly) (MvPolynomial.X j)) = (MvPolynomial.aeval v) (MvPolynomial.X j)
        rw [MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]
        change algebraMap (Polynomial ℂ) E (Polynomial.C (D.alpha j) * Polynomial.X) = v j
        simp only [map_mul]
        change algebraMap (Polynomial ℂ) E (algebraMap ℂ (Polynomial ℂ) (D.alpha j)) * _ = _
        rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) E]
    exact RingHom.congr_fun heq p
  intro j
  obtain ⟨d, hd, A, hA⟩ := D.normalization.2.2.2 j
  let Q : Polynomials ℂ (F.n + 1) := MvPolynomial.X j ^ d + ∑ i : Fin d,
    eval₂Hom MvPolynomial.C (normalizationPolynomials D.c) (A i) * MvPolynomial.X j ^ i.val
  have hQker : eval₂Hom MvPolynomial.C F.F Q = 0 := by
    rw [← RingHom.mem_ker, ← image_vanishingIdeal_eq_kernel]
    intro w hw
    obtain ⟨a, rfl⟩ := hw
    have hwY : evaluate F.F a ∈ imageClosure F.F := zeroLocus_vanishingIdeal_le (Set.range (evaluate F.F)) (Set.mem_range_self a)
    simpa only [Q, aeval_def, Algebra.algebraMap_self, eval₂_id, map_add, map_sum, map_mul,
      map_pow, eval_X, evaluation_substitution] using hA (evaluate F.F a) hwY
  have hrel := congrArg (MvPolynomial.aeval x) hQker
  rw [map_zero, aeval_substitution] at hrel
  have hcoeff (i : Fin d) : MvPolynomial.aeval y
      (eval₂Hom MvPolynomial.C (normalizationPolynomials D.c) (A i)) = MvPolynomial.aeval v (A i) := by
    rw [aeval_substitution, funext hnorm]
  change (MvPolynomial.aeval y) Q = 0 at hrel
  have hroot : y j ^ d + ∑ i : Fin d, algebraMap (Polynomial ℂ) E (polyLift (A i)) * y j ^ i.val = 0 := by
    simpa only [Q, map_add, map_sum, map_mul, map_pow, aeval_X, hcoeff, hlift] using hrel
  refine ⟨Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (polyLift (A i)) * Polynomial.X ^ i.val,
    monic_from_relation _, ?_⟩
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] using hroot


end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finite_adjoin_of_complex_polynomial_span
    {K E : Type} [Field K] [Field E] [Algebra K E] [Algebra ℂ E]
    [Algebra ℂ K] [IsScalarTower ℂ K E]
    {n s : ℕ} (x : Fin n → E) (generators : Fin s → Polynomials ℂ n)
    (hspan : ∀ p : Polynomials ℂ n, ∃ c : Fin s → K,
      MvPolynomial.aeval x p = ∑ i : Fin s, algebraMap K E (c i) * MvPolynomial.aeval x (generators i)) :
    Module.Finite K (Algebra.adjoin K (Set.range x)) := by
  classical
  let A := Algebra.adjoin K (Set.range x)
  let g : Fin s → E := fun i => MvPolynomial.aeval x (generators i)
  let V : Submodule K E := Submodule.span K (Set.range g)
  have hpV (p : Polynomials ℂ n) : MvPolynomial.aeval x p ∈ V := by
    obtain ⟨c, hc⟩ := hspan p
    rw [hc]
    apply Submodule.sum_mem
    intro i _
    rw [← Algebra.smul_def]
    change c i • g i ∈ V
    exact V.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have hmono (e : Fin n →₀ ℕ) : e.prod (fun i k => x i ^ k) ∈ V := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial, map_one, one_mul] using
      hpV (MvPolynomial.monomial e (1 : ℂ))
  have hAV : A.toSubmodule ≤ V := by
    intro a ha
    change a ∈ Algebra.adjoin K (Set.range x) at ha
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    change MvPolynomial.eval₂ (algebraMap K E) x p ∈ V
    rw [MvPolynomial.eval₂_eq]
    apply Submodule.sum_mem
    intro e he
    rw [← Algebra.smul_def]
    change p.coeff e • e.prod (fun i k => x i ^ k) ∈ V
    exact V.smul_mem _ (hmono e)
  have hgA (i : Fin s) : g i ∈ A := by
    have hh (p : Polynomials ℂ n) : MvPolynomial.aeval x p ∈ A := by
      induction p using MvPolynomial.induction_on with
      | C c =>
          rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply ℂ K E]
          exact A.algebraMap_mem _
      | add p q hp hq => simpa only [map_add] using A.add_mem hp hq
      | mul_X p j hp =>
          simpa only [map_mul, MvPolynomial.aeval_X] using A.mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)
    exact hh _
  have hVA : V ≤ A.toSubmodule := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgA i)
  have hfg : A.toSubmodule.FG := by
    rw [hAV.antisymm hVA]
    exact Submodule.fg_span (Set.finite_range g)
  letI : Module.Finite K A.toSubmodule := Module.Finite.of_fg hfg
  exact Module.Finite.of_surjective A.toSubmoduleEquiv.toLinearMap A.toSubmoduleEquiv.surjective


lemma finite_fractionRing_of_finite_adjoin {n : ℕ} (W : Set (Affine ℂ n))
    [IsDomain (CoordinateRing W)] (K : Type) [Field K]
    [Algebra K (FractionRing (CoordinateRing W))] [Algebra ℂ K]
    [IsScalarTower ℂ K (FractionRing (CoordinateRing W))]
    (hfin : Module.Finite K (Algebra.adjoin K (Set.range
      (fun j => algebraMap (CoordinateRing W) (FractionRing (CoordinateRing W)) (coordinate W j))))) :
    Module.Finite K (FractionRing (CoordinateRing W)) := by
  classical
  let E := FractionRing (CoordinateRing W)
  let x : Fin n → E := fun j => algebraMap (CoordinateRing W) E (coordinate W j)
  let A := Algebra.adjoin K (Set.range x)
  letI : Module.Finite K A := hfin
  have hfield : IsField A := isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)
  let B := A.toIntermediateField' hfield
  have hCW (a : CoordinateRing W) : algebraMap (CoordinateRing W) E a ∈ B := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← coordinate_aeval_eq]
    change MvPolynomial.aeval x p ∈ A
    induction p using MvPolynomial.induction_on with
    | C c =>
        rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply ℂ K E]
        exact A.algebraMap_mem _
    | add p q hp hq => simpa only [map_add] using A.add_mem hp hq
    | mul_X p j hp =>
        simpa only [map_mul, MvPolynomial.aeval_X] using A.mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)
  have htop : B = ⊤ := by
    apply top_unique
    intro e _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (CoordinateRing W) e
    exact B.div_mem (hCW a) (hCW b)
  have hAeq : A = ⊤ := by
    apply SetLike.ext
    intro e
    change e ∈ B ↔ e ∈ (⊤ : Subalgebra K E)
    rw [htop]
    simp
  change Module.Finite K A at hfin
  rw [hAeq] at hfin
  letI := hfin
  exact Module.Finite.of_surjective
    (Subalgebra.topEquiv.toLinearMap : (⊤ : Subalgebra K E) →ₗ[K] E)
    Subalgebra.topEquiv.surjective

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma clear_power_denominator {K : Type} [Field K] (a c : K) (ha : a ≠ 0) (N e : ℕ) (he : e ≤ N) :
    a ^ N * (c / a ^ e) = c * a ^ (N - e) := by
  apply (mul_right_cancel₀ (pow_ne_zero e ha))
  rw [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero e ha)]
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel he]
  ring

lemma finiteOverOpen_polynomial_span {n m : ℕ} (F : PolynomialMap ℂ n m)
    (U : Set (Affine ℂ m)) (hF : FiniteOverOpen Set.univ F U)
    (W : Set (Affine ℂ n)) (hW : IrreducibleAffine W)
    (x₀ : Affine ℂ n) (hx₀ : x₀ ∈ W) (hy₀ : evaluate F x₀ ∈ U)
    [IsDomain (CoordinateRing W)]
    (K : Type) [Field K] [Algebra K (FractionRing (CoordinateRing W))]
    [Algebra ℂ K] [IsScalarTower ℂ K (FractionRing (CoordinateRing W))]
    (hv : ∀ j, ∃ c : K, algebraMap K (FractionRing (CoordinateRing W)) c =
      algebraMap (CoordinateRing W) (FractionRing (CoordinateRing W)) (Ideal.Quotient.mk _ (F j))) :
    Module.Finite K (FractionRing (CoordinateRing W)) := by
  classical
  let E := FractionRing (CoordinateRing W)
  let x : Fin n → E := fun j => algebraMap (CoordinateRing W) E (coordinate W j)
  let y : Fin m → E := fun j => MvPolynomial.aeval x (F j)
  let V : Subfield E := (algebraMap K E).fieldRange
  have hyV (j : Fin m) : y j ∈ V := by
    obtain ⟨c, hc⟩ := hv j
    refine ⟨c, ?_⟩
    rw [← coordinate_aeval_eq] at hc
    exact hc
  have hcV (c : ℂ) : algebraMap ℂ E c ∈ V := by
    exact ⟨algebraMap ℂ K c, (IsScalarTower.algebraMap_apply ℂ K E c).symm⟩
  have hpV (p : Polynomials ℂ m) : MvPolynomial.aeval y p ∈ V := by
    exact MvPolynomial.eval₂_mem (fun e _ => hcV (p.coeff e)) hyV
  obtain ⟨b, hb, hbU, s, generators, hgen⟩ := hF (evaluate F x₀) hy₀
  let bs := eval₂Hom MvPolynomial.C F b
  let bE : E := MvPolynomial.aeval y b
  have hbE : bE ≠ 0 := by
    intro hz
    have hzq : Ideal.Quotient.mk (vanishingIdeal ℂ W) bs = 0 := by
      apply IsFractionRing.injective (CoordinateRing W) E
      rw [map_zero, ← coordinate_aeval_eq, aeval_substitution]
      exact hz
    have hzero := (Ideal.Quotient.eq_zero_iff_mem.mp hzq) x₀ hx₀
    apply hb
    simpa only [bs, aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hzero
  apply finite_fractionRing_of_finite_adjoin W K
  apply finite_adjoin_of_complex_polynomial_span x generators
  intro p
  obtain ⟨coefficients, exponents, hcoeff⟩ := hgen p
  let N := Finset.univ.sup exponents
  have hN (i : Fin s) : exponents i ≤ N := Finset.le_sup (Finset.mem_univ i)
  let cs : Fin s → Polynomials ℂ n := fun i => eval₂Hom MvPolynomial.C F (coefficients i)
  let Q := bs ^ N * p - ∑ i : Fin s, cs i * bs ^ (N - exponents i) * generators i
  have hQ : Q ∈ vanishingIdeal ℂ W := by
    apply vanishes_of_vanishes_principal_open W hW Q bs
    · refine ⟨x₀, hx₀, ?_⟩
      simpa only [bs, evaluation_substitution] using hb
    · intro z hzW hzb
      have hzb' : eval (evaluate F z) b ≠ 0 := by simpa only [bs, evaluation_substitution] using hzb
      have hh := hcoeff z (Set.mem_univ z) hzb'
      simp only [Q, map_sub, map_mul, map_pow, map_sum, bs, cs, evaluation_substitution, sub_eq_zero]
      rw [hh, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, clear_power_denominator _ _ hzb' _ _ (hN i)]
  have hQE : bE ^ N * MvPolynomial.aeval x p =
      ∑ i : Fin s, MvPolynomial.aeval y (coefficients i) * bE ^ (N - exponents i) * MvPolynomial.aeval x (generators i) := by
    have hh := congrArg (algebraMap (CoordinateRing W) E) (Ideal.Quotient.eq_zero_iff_mem.mpr hQ)
    rw [map_zero, ← coordinate_aeval_eq] at hh
    simpa only [Q, map_sub, map_mul, map_pow, map_sum, cs, bs, aeval_substitution, sub_eq_zero] using hh
  have hcoef (i : Fin s) : ∃ c : K, algebraMap K E c = MvPolynomial.aeval y (coefficients i) / bE ^ exponents i :=
    V.div_mem (hpV _) (V.pow_mem (hpV b) _)
  choose c hc using hcoef
  refine ⟨c, ?_⟩
  apply (mul_left_cancel₀ (pow_ne_zero N hbE))
  rw [hQE, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc, ← mul_assoc, clear_power_denominator _ _ hbE _ _ (hN i)]

end APSCounting893.Main

end


section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped RatFunc
namespace APSCounting893.Main

lemma graph_component_functionField (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    FiniteLineFunctionField F D W := by
  classical
  letI : (vanishingIdeal ℂ W).IsPrime := irreducibleAffine_ideal_prime hW.1
  refine ⟨inferInstance, ?_⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.mp D.nonzero
  let E := FractionRing (CoordinateRing W)
  let T₀ := Ideal.Quotient.mk (vanishingIdeal ℂ W) (lineParameterPolynomial F D k)
  let T : E := algebraMap (CoordinateRing W) E T₀
  have hT₀ : Transcendental ℂ T₀ := graph_parameter_transcendental F D k hk W hW
  have hT : Transcendental ℂ T := by
    intro h
    exact hT₀ ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℂ (CoordinateRing W) E)
      (IsFractionRing.injective (CoordinateRing W) E)).mp h)
  let φ : Polynomial ℂ →+* E := (Polynomial.aeval T).toRingHom
  have hφ : Function.Injective φ := transcendental_iff_injective.mp hT
  let σ : RatFunc ℂ →+* E := IsFractionRing.lift hφ
  let a : Algebra (RatFunc ℂ) E := σ.toAlgebra
  refine ⟨a, ?_⟩
  letI : Algebra (RatFunc ℂ) E := a
  have hσ (p : Polynomial ℂ) : σ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = Polynomial.aeval T p :=
    IsFractionRing.lift_algebraMap hφ p
  letI : IsScalarTower ℂ (RatFunc ℂ) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
    change algebraMap ℂ E c = σ (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))
    rw [hσ, Polynomial.aeval_C])
  letI : Algebra (Polynomial ℂ) E := Algebra.compHom E (algebraMap (Polynomial ℂ) (RatFunc ℂ))
  letI : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ℂ (Polynomial ℂ) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) E,
      IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
    rfl)
  have hparam : algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) = T := by
    change σ _ = _
    rw [hσ, Polynomial.aeval_X]
  have hβ (j : Fin F.n) : algebraMap (CoordinateRing W) E (Ideal.Quotient.mk _ (betaPolynomials F D.c j)) =
      algebraMap ℂ E (D.alpha j) * algebraMap (RatFunc ℂ) E
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) := by
    rw [hparam]
    have h := congrArg (algebraMap (CoordinateRing W) E) (graph_parameter_beta_quotient F D k hk W hW j)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply ℂ (CoordinateRing W) E] using h
  let x : Fin F.n → E := fun j => algebraMap (CoordinateRing W) E (coordinate W j)
  let v : Fin (F.n + 1) → E := fun j => MvPolynomial.aeval x (F.F j)
  have hb (j : Fin F.n) : MvPolynomial.aeval x (betaPolynomials F D.c j) =
      algebraMap ℂ E (D.alpha j) * algebraMap (Polynomial ℂ) E Polynomial.X := by
    rw [coordinate_aeval_eq]
    exact hβ j
  have hvPoly := output_coordinates_integral F D E x hb
  have hvRat (j : Fin (F.n + 1)) : IsIntegral (RatFunc ℂ) (v j) := (hvPoly j).tower_top
  let K := IntermediateField.adjoin (RatFunc ℂ) (Set.range v)
  letI : Fintype (Set.range v) := (Set.finite_range v).fintype
  letI : Module.Finite (RatFunc ℂ) K := IntermediateField.finiteDimensional_adjoin
    (by rintro z ⟨j, rfl⟩; exact hvRat j)
  letI : Algebra ℂ K := Algebra.compHom K (algebraMap ℂ (RatFunc ℂ))
  letI : IsScalarTower ℂ (RatFunc ℂ) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ℂ K E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) E,
      IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) K,
      IsScalarTower.algebraMap_apply (RatFunc ℂ) K E])
  obtain ⟨x₀, hx₀, hgood⟩ := (graph_component_linePreimage F D W hW).2
  have hy₀ : evaluate F.F x₀ ∈ D.U := by
    by_contra hnot
    apply hgood.2
    refine ⟨evaluate F.F x₀, ⟨zeroLocus_vanishingIdeal_le (Set.range (evaluate F.F)) (Set.mem_range_self x₀), hnot⟩, ?_⟩
    exact (evaluate_beta F D.c x₀).symm
  letI : Module.Finite K E := finiteOverOpen_polynomial_span F.F D.U D.goodOpen.2.2.2 W hW.1 x₀ hx₀ hy₀ K (by
    intro j
    refine ⟨⟨v j, IntermediateField.subset_adjoin (RatFunc ℂ) (Set.range v) ⟨j, rfl⟩⟩, ?_⟩
    change v j = _
    exact coordinate_aeval_eq W E (F.F j))
  exact ⟨inferInstance, Module.Finite.trans K E, hβ⟩

end APSCounting893.Main

end

open APSCounting893.Main

theorem solution (F : ReducedMap) (D : LineData F) (W : Set (Affine ℂ F.n))
    (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    RSCapacity.zClosure (evaluate (betaPolynomials F D.c) '' W) = affineLine 0 D.alpha ∧
      FiniteLineFunctionField F D W := by
  exact ⟨graph_component_dominant F D W hW, graph_component_functionField F D W hW⟩


