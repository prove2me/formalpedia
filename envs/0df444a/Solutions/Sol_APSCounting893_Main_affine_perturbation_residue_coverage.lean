-- Prove2me | solution 1 for APSCounting893.Main.affine_perturbation_residue_coverage
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:08:36.446857+00:00
-- url     : https://prove2.me/submissions/15cd0095-f3e2-4daf-96de-728b8fa8eaed

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_LineGeometry
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Valuation.LocalSubring
import Theorems.Thm_APSCounting893_Main_dominant_graph_components
import Theorems.Thm_APSCounting893_Main_zero_fiber_residues
import Theorems.Thm_DiazModulus_card_le_height_add_of_ringKrullDim_quotient_le
import Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
import Theorems.Thm_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

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
end Component_0

section Component_1

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

end Component_1

section Component_2

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
end Component_2

section Component_3

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
end Component_3

section Component_4

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
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def lineSubstitution {n : ℕ} (alpha : Affine ℂ n) :
    Polynomials ℂ n →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => Polynomial.C (alpha j) * Polynomial.X)

lemma eval_lineSubstitution {n : ℕ} (alpha : Affine ℂ n) (p : Polynomials ℂ n) (s : ℂ) :
    (lineSubstitution alpha p).eval s = eval (s • alpha) p := by
  have hh : (Polynomial.evalRingHom s).comp (lineSubstitution alpha) = eval (s • alpha) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lineSubstitution]
    · intro j
      simp only [RingHom.comp_apply, lineSubstitution, MvPolynomial.eval₂Hom_X',
        Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        MvPolynomial.eval_X, Pi.smul_apply, smul_eq_mul]
      exact mul_comm _ _
  exact RingHom.congr_fun hh p

lemma aeval_lineSubstitution {L : Type} [Field L] [Algebra ℂ L] {n : ℕ}
    (alpha : Affine ℂ n) (p : Polynomials ℂ n) (t : L) :
    Polynomial.aeval t (lineSubstitution alpha p) =
      MvPolynomial.eval₂ (algebraMap ℂ L) (fun j => algebraMap ℂ L (alpha j) * t) p := by
  have hh : (Polynomial.aeval t).toRingHom.comp (lineSubstitution alpha) =
      MvPolynomial.eval₂Hom (algebraMap ℂ L) (fun j => algebraMap ℂ L (alpha j) * t) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lineSubstitution]
    · intro j
      simp [lineSubstitution]
  exact RingHom.congr_fun hh p

lemma raw_point_graph_component
    (F : ReducedMap) (D : LineData F)
    {L : Type} [Field L] [Algebra ℂ L] (t : L) (ht : Transcendental ℂ t)
    (x : Affine L F.n)
    (hbeta : ∀ j, MvPolynomial.eval₂ (algebraMap ℂ L) x (betaPolynomials F D.c j) =
      algebraMap ℂ L (D.alpha j) * t) :
    ∃ W, AffineComponent (closedGraphCurve F D.c D.alpha D.U) W ∧
      ∀ p ∈ vanishingIdeal ℂ W, MvPolynomial.eval₂ (algebraMap ℂ L) x p = 0 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp D.nonzero
  let C : Set (Affine ℂ F.n) := {x | evaluate (betaPolynomials F D.c) x ∈ affineLine 0 D.alpha}
  let phi : Polynomials ℂ F.n →+* L := MvPolynomial.eval₂Hom (algebraMap ℂ L) x
  let I := RingHom.ker phi
  letI : I.IsPrime := RingHom.ker_isPrime phi
  let ps : Fin F.n → Polynomials ℂ F.n := fun j =>
    MvPolynomial.C (D.alpha k) * betaPolynomials F D.c j -
      MvPolynomial.C (D.alpha j) * betaPolynomials F D.c k
  have hspan : Ideal.span (↑((Finset.univ.erase k).image ps) : Set (Polynomials ℂ F.n)) ≤ I := by
    apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    change MvPolynomial.eval₂ (algebraMap ℂ L) x (ps j) = 0
    simp only [ps, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hbeta]
    ring
  have hCI : vanishingIdeal ℂ C ≤ I := by
    rw [show C = _ from linePreimage_eq_zeroLocus_span F D k hk,
      MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
    exact (Ideal.radical_mono hspan).trans_eq (show I.IsPrime from inferInstance).radical
  obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_minimalPrimes_le hCI
  letI : Q.IsPrime := hQ.isPrime
  let W := zeroLocus ℂ Q
  have hW : AffineComponent C W := affineComponent_of_minimal
    (isAlgSet_preimage_evaluate _ (isAlgSet_affineLine _ _ D.nonzero)) Q hQ
  have hWQ : vanishingIdeal ℂ W = Q := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus Q
  have hpull : ∀ p ∈ vanishingIdeal ℂ W, MvPolynomial.eval₂ (algebraMap ℂ L) x p = 0 := by
    intro p hp
    rw [hWQ] at hp
    exact hQI hp
  obtain ⟨g, hg, u, hu, hgu⟩ := exists_normalizationOpen_polynomial F D
  let b := MvPolynomial.eval₂ MvPolynomial.C (betaPolynomials F D.c) g
  have hbraw : MvPolynomial.eval₂ (algebraMap ℂ L) x b ≠ 0 := by
    have hnonzero : lineSubstitution D.alpha g ≠ 0 := by
      intro heq
      obtain ⟨s, hs⟩ := hu
      have hu' : u = s • D.alpha := by simpa using hs.symm
      apply hgu
      rw [hu', ← eval_lineSubstitution, heq, Polynomial.eval_zero]
    have heval : MvPolynomial.eval₂ (algebraMap ℂ L) x b =
        Polynomial.aeval t (lineSubstitution D.alpha g) := by
      rw [aeval_lineSubstitution]
      dsimp only [b]
      rw [← MvPolynomial.eval₂_assoc]
      congr 1
      funext j
      exact hbeta j
    rw [heval]
    exact fun heq => hnonzero ((transcendental_iff_injective.mp ht) (by simpa using heq))
  have hnonzero : ∃ a ∈ W, eval a b ≠ 0 := by
    by_contra h
    push Not at h
    have hbW : b ∈ vanishingIdeal ℂ W := by
      intro a ha
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using h a ha
    exact hbraw (hpull b hbW)
  have hopen : ∀ a ∈ W, eval a b ≠ 0 →
      evaluate (betaPolynomials F D.c) a ∈ affineLine 0 D.alpha ∩ normalizationOpen F D.c D.U := by
    intro a ha hab
    refine ⟨hW.2.1 ha, ?_⟩
    intro hbad
    apply hab
    have hb := hg _ hbad
    change eval a (MvPolynomial.eval₂ MvPolynomial.C (betaPolynomials F D.c) g) = 0
    change eval (evaluate (betaPolynomials F D.c) a) g = 0 at hb
    exact (evaluation_substitution (betaPolynomials F D.c) g a).trans hb
  have hWgraph : W ⊆ closedGraphCurve F D.c D.alpha D.U := by
    intro a ha p hp
    have hpW := vanishes_of_vanishes_principal_open W hW.1 p b hnonzero (by
      intro a ha hab
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hp a (hopen a ha hab))
    exact hpW a ha
  have hgraphC : closedGraphCurve F D.c D.alpha D.U ⊆ C := by
    exact zClosure_minimal (isAlgSet_preimage_evaluate _ (isAlgSet_affineLine _ _ D.nonzero))
      (fun a ha => ha.1)
  refine ⟨W, ⟨hW.1, hWgraph, ?_⟩, hpull⟩
  intro Z hZ hWZ hZG
  exact hW.2.2 Z hZ hWZ (hZG.trans hgraphC)

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma ringHom_injective_of_algebraic_base
    {R A B : Type} [CommRing R] [CommRing A] [IsDomain A] [CommRing B]
    [Algebra R A] [Algebra.IsAlgebraic R A]
    (phi : A →+* B) (hinj : Function.Injective (phi.comp (algebraMap R A))) :
    Function.Injective phi := by
  apply (injective_iff_map_eq_zero phi).mpr
  intro a ha
  by_contra hne
  obtain ⟨r, hr, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
  have hh : (phi.comp (algebraMap R A)) r = (phi.comp (algebraMap R A)) 0 := by
    simp only [RingHom.comp_apply, map_zero]
    rw [hb, map_mul, ha, zero_mul]
  exact hr (hinj hh)

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def nonnegativeHahnRing (K : Type) [Field K] : ValuationSubring (HahnSeries ℚ K) :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ K)).valuationSubring

lemma hahn_coeff_zero_mul_nonnegative {K : Type} [Field K] (x y : HahnSeries ℚ K)
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

noncomputable def hahnResidueHom (K : Type) [Field K] : nonnegativeHahnRing K →+* K where
  toFun x := x.val.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := hahn_coeff_zero_mul_nonnegative x.val y.val x.property y.property

noncomputable def hahnConstantLift (K : Type) [Field K] : K →+* nonnegativeHahnRing K where
  toFun c := ⟨HahnSeries.C c, by
    change 0 ≤ (HahnSeries.C c : HahnSeries ℚ K).orderTop
    rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.order_C]⟩
  map_zero' := Subtype.ext HahnSeries.C.map_zero
  map_one' := Subtype.ext HahnSeries.C.map_one
  map_add' a b := Subtype.ext (HahnSeries.C.map_add a b)
  map_mul' a b := Subtype.ext (HahnSeries.C.map_mul a b)

lemma hahnResidue_constant {K : Type} [Field K] (c : K) :
    hahnResidueHom K (hahnConstantLift K c) = c := by simp [hahnResidueHom, hahnConstantLift]

lemma hahnResidue_single_one {K : Type} [Field K] :
    ∃ x : nonnegativeHahnRing K, x.val = HahnSeries.single (1 : ℚ) (1 : K) ∧ hahnResidueHom K x = 0 := by
  refine ⟨⟨HahnSeries.single (1 : ℚ) (1 : K), ?_⟩, rfl, ?_⟩
  · change 0 ≤ (HahnSeries.single (1 : ℚ) (1 : K)).orderTop
    rw [HahnSeries.orderTop_single]
    · norm_num
    · exact one_ne_zero
  · simp [hahnResidueHom, HahnSeries.coeff_single_of_ne]

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial HahnSeries
open scoped LaurentSeries RatFunc
namespace APSCounting893.Main.GenericSeries

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]

def IsPuiseuxOver (s : HahnSeries ℚ K) : Prop :=
  ∃ (e : ℕ) (he : 0 < e), s ∈ HahnSeries.puiseuxRamSubfield K he

noncomputable def ramOneAlgHom : LaurentSeries K →ₐ[K] (HahnSeries ℚ K) where
  toRingHom := HahnSeries.puiseuxRamEmb (by decide : 0 < 1)
  commutes' c := by
    simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    exact HahnSeries.embDomainRingHom_C (R := K)

noncomputable def rationalSeriesHom : RatFunc K →ₐ[K] (HahnSeries ℚ K) where
  toRingHom := ramOneAlgHom.toRingHom.comp (algebraMap (RatFunc K) (LaurentSeries K))
  commutes' c := by
    change ramOneAlgHom (algebraMap (RatFunc K) (LaurentSeries K) (algebraMap K (RatFunc K) c)) = _
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
    have hL : algebraMap (Polynomial K) (LaurentSeries K) (algebraMap K (Polynomial K) c) =
        algebraMap K (LaurentSeries K) c := by
      rw [HahnSeries.algebraMap_apply',
        ← IsScalarTower.algebraMap_apply K (Polynomial K) (PowerSeries K)]
      simp [HahnSeries.algebraMap_apply', HahnSeries.ofPowerSeries_C]
    rw [hL]
    exact ramOneAlgHom.commutes c

lemma rationalSeriesHom_X :
    rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
      HahnSeries.single (1 : ℚ) (1 : K) := by
  change ramOneAlgHom (algebraMap (RatFunc K) (LaurentSeries K) RatFunc.X) = _
  rw [RatFunc.coe_X]
  change HahnSeries.embDomain _ (HahnSeries.single (1 : ℤ) (1 : K)) = _
  rw [HahnSeries.embDomain_single]
  simp [HahnSeries.ramScale]

lemma rationalSeriesHom_puiseux (r : RatFunc K) :
    HahnSeries.HasRamBound 1 (rationalSeriesHom r) := by
  apply (HahnSeries.mem_puiseuxRamSubfield_iff (by decide : 0 < 1)).mp
  exact ⟨algebraMap (RatFunc K) (LaurentSeries K) r, rfl⟩

lemma rationalSeriesHom_unique {M : Type} [Field M] [Algebra K M] [Algebra (RatFunc K) M]
    [IsScalarTower K (RatFunc K) M] (rho : M →ₐ[K] (HahnSeries ℚ K))
    (ht : rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : K)) :
    rho.toRingHom.comp (algebraMap (RatFunc K) M) = rationalSeriesHom.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Polynomial K)
  have hpoly : (rho.toRingHom.comp (algebraMap (RatFunc K) M)).comp
        (algebraMap (Polynomial K) (RatFunc K)) =
      rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      change rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K)
        (algebraMap K (Polynomial K) c))) =
        rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c))
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
        ← IsScalarTower.algebraMap_apply K (RatFunc K) M]
      exact (rho.commutes c).trans (rationalSeriesHom.commutes c).symm
    · change rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) X)) =
        rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) X)
      rw [rationalSeriesHom_X]
      exact ht
  exact fun p => RingHom.congr_fun hpoly p

lemma algebraic_image_puiseux {M : Type} [Field M] [Algebra K M] [Algebra (RatFunc K) M]
    [IsScalarTower K (RatFunc K) M] [Algebra.IsAlgebraic (RatFunc K) M]
    (rho : M →ₐ[K] (HahnSeries ℚ K))
    (ht : rho (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : K)) (z : M) : IsPuiseuxOver (rho z) := by
  classical
  have hz : IsIntegral (RatFunc K) z := (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  let q := (minpoly (RatFunc K) z).map rationalSeriesHom.toRingHom
  have hq : q ≠ 0 := (minpoly.monic hz).map rationalSeriesHom.toRingHom |>.ne_zero
  have hcoeff : ∀ i, HahnSeries.HasRamBound 1 (q.coeff i) := by
    intro i
    simpa [q] using rationalSeriesHom_puiseux ((minpoly (RatFunc K) z).coeff i)
  have hroot : q.IsRoot (rho z) := by
    have heq := rationalSeriesHom_unique rho ht
    change q.eval (rho z) = 0
    dsimp only [q]
    rw [Polynomial.eval_map]
    rw [← heq]
    rw [← Polynomial.eval₂_map]
    change Polynomial.eval₂ rho.toRingHom (rho.toRingHom z)
      ((minpoly (RatFunc K) z).map (algebraMap (RatFunc K) M)) = 0
    rw [Polynomial.eval₂_at_apply]
    simpa using congrArg rho (minpoly.aeval (RatFunc K) z)
  exact ⟨q.natDegree.factorial, Nat.factorial_pos _,
    (HahnSeries.mem_puiseuxRamSubfield_iff (Nat.factorial_pos _)).mpr
      (HahnSeries.hasRamBound_natDegree_factorial_of_isRoot hq hcoeff hroot)⟩


end APSCounting893.Main.GenericSeries
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc
namespace APSCounting893.Main

lemma finite_curve_point_embedding
    {K A E L : Type} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Field E] [Algebra A E] [IsFractionRing A E] [Algebra K E] [IsScalarTower K A E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Field L] [Algebra K L]
    (T : A) (hT : algebraMap A E T =
      algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
    (phi : A →ₐ[K] L) (t : L) (ht : Transcendental K t) (hphiT : phi T = t) :
    ∃ rho : E →ₐ[K] L,
      (∀ a : A, rho (algebraMap A E a) = phi a) ∧
      rho (algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) = t := by
  classical
  let g : Polynomial K →+* A := (Polynomial.aeval T).toRingHom
  letI : Algebra (Polynomial K) A := g.toAlgebra
  letI : Algebra (Polynomial K) E := Algebra.compHom E (algebraMap (Polynomial K) (RatFunc K))
  letI : IsScalarTower (Polynomial K) (RatFunc K) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower K (Polynomial K) A := IsScalarTower.of_algebraMap_eq (fun c =>
    ((Polynomial.aeval T).commutes c).symm)
  letI : IsScalarTower (Polynomial K) A E := IsScalarTower.of_algebraMap_eq' (by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      change algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c)) =
        algebraMap A E (Polynomial.aeval T (algebraMap K (Polynomial K) c))
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K),
        ← IsScalarTower.algebraMap_apply K (RatFunc K) E, (Polynomial.aeval T).commutes,
        ← IsScalarTower.algebraMap_apply K A E]
    · change algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
        algebraMap A E (Polynomial.aeval T Polynomial.X)
      rw [Polynomial.aeval_X]
      exact hT.symm)
  letI : Algebra.IsAlgebraic (Polynomial K) E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial K) (K := RatFunc K) (C := E)).mpr inferInstance
  letI : Algebra.IsAlgebraic (Polynomial K) A := ⟨fun a =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom (Polynomial K) A E)
      (IsFractionRing.injective A E)).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩
  have hbase : phi.toRingHom.comp g = (Polynomial.aeval t).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [g]
    · simp [g, hphiT]
  have hinj : Function.Injective phi := ringHom_injective_of_algebraic_base phi.toRingHom (by
    change Function.Injective (phi.toRingHom.comp g)
    rw [hbase]
    exact transcendental_iff_injective.mp ht)
  let f : E →+* L := IsFractionRing.lift hinj
  have hf (a : A) : f (algebraMap A E a) = phi a := IsFractionRing.lift_algebraMap hinj a
  let rho : E →ₐ[K] L :=
    { toRingHom := f
      commutes' := fun c => by
        change f (algebraMap K E c) = algebraMap K L c
        rw [IsScalarTower.algebraMap_apply K A E, hf, phi.commutes] }
  refine ⟨rho, hf, ?_⟩
  rw [← hT]
  exact (hf T).trans hphiT

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped RatFunc
namespace APSCounting893.Main

lemma component_point_embedding_of_data
    (F : ReducedMap) (D : LineData F) (W : Set (Affine ℂ F.n))
    [IsDomain (CoordinateRing W)]
    [Algebra (RatFunc ℂ) (FractionRing (CoordinateRing W))]
    [IsScalarTower ℂ (RatFunc ℂ) (FractionRing (CoordinateRing W))]
    [Module.Finite (RatFunc ℂ) (FractionRing (CoordinateRing W))]
    (hb : ∀ j, algebraMap (CoordinateRing W) (FractionRing (CoordinateRing W))
      (Ideal.Quotient.mk _ (betaPolynomials F D.c j)) =
      algebraMap ℂ (FractionRing (CoordinateRing W)) (D.alpha j) *
        algebraMap (RatFunc ℂ) (FractionRing (CoordinateRing W))
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X))
    {L : Type} [Field L] [Algebra ℂ L] (t : L) (ht : Transcendental ℂ t)
    (x : Affine L F.n)
    (hbeta : ∀ j, MvPolynomial.eval₂ (algebraMap ℂ L) x (betaPolynomials F D.c j) =
      algebraMap ℂ L (D.alpha j) * t)
    (hpoint : ∀ p ∈ vanishingIdeal ℂ W, MvPolynomial.eval₂ (algebraMap ℂ L) x p = 0) :
    ∃ rho : FractionRing (CoordinateRing W) →ₐ[ℂ] L,
      rho (algebraMap (RatFunc ℂ) (FractionRing (CoordinateRing W))
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) = t ∧
      ∀ j, rho (algebraMap (CoordinateRing W) (FractionRing (CoordinateRing W)) (coordinate W j)) = x j := by
  classical
  let E := FractionRing (CoordinateRing W)
  let phi : CoordinateRing W →ₐ[ℂ] L :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) hpoint
  obtain ⟨k, hk⟩ := Function.ne_iff.mp D.nonzero
  let T : CoordinateRing W := algebraMap ℂ (CoordinateRing W) ((D.alpha k)⁻¹) *
    Ideal.Quotient.mk _ (betaPolynomials F D.c k)
  have hT : algebraMap (CoordinateRing W) E T =
      algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) := by
    dsimp only [T]
    rw [map_mul, ← IsScalarTower.algebraMap_apply ℂ (CoordinateRing W) E, hb]
    rw [map_inv₀, inv_mul_cancel_left₀ ((map_ne_zero (algebraMap ℂ E)).mpr hk)]
  have hphiT : phi T = t := by
    dsimp only [T]
    rw [map_mul, phi.commutes]
    change algebraMap ℂ L ((D.alpha k)⁻¹) * MvPolynomial.eval₂ (algebraMap ℂ L) x (betaPolynomials F D.c k) = t
    rw [hbeta, map_inv₀, inv_mul_cancel_left₀ ((map_ne_zero (algebraMap ℂ L)).mpr hk)]
  obtain ⟨rho, hrho, hrhot⟩ := finite_curve_point_embedding T hT phi t ht hphiT
  refine ⟨rho, hrhot, ?_⟩
  intro j
  rw [hrho]
  change MvPolynomial.aeval x (MvPolynomial.X j) = x j
  exact MvPolynomial.aeval_X x j


lemma component_point_field_embedding
    (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n))
    (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W)
    {L : Type} [Field L] [Algebra ℂ L] (t : L) (ht : Transcendental ℂ t)
    (x : Affine L F.n)
    (hbeta : ∀ j, MvPolynomial.eval₂ (algebraMap ℂ L) x (betaPolynomials F D.c j) =
      algebraMap ℂ L (D.alpha j) * t)
    (hpoint : ∀ p ∈ vanishingIdeal ℂ W, MvPolynomial.eval₂ (algebraMap ℂ L) x p = 0) :
    ∃ (hdom : IsDomain (CoordinateRing W)),
      letI := hdom
      ∃ (a : Algebra (RatFunc ℂ) (FractionRing (CoordinateRing W))),
        letI := a
        IsScalarTower ℂ (RatFunc ℂ) (FractionRing (CoordinateRing W)) ∧
        Module.Finite (RatFunc ℂ) (FractionRing (CoordinateRing W)) ∧
        ∃ rho : FractionRing (CoordinateRing W) →ₐ[ℂ] L,
          rho (algebraMap (RatFunc ℂ) (FractionRing (CoordinateRing W))
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) = t ∧
          ∀ j, rho (algebraMap (CoordinateRing W) (FractionRing (CoordinateRing W)) (coordinate W j)) = x j := by
  classical
  obtain ⟨hdom, a, htower, hfinite, hb⟩ := (dominant_graph_components F D W hW).2
  letI := hdom
  letI := a
  letI := htower
  letI := hfinite
  obtain ⟨rho, ht, hcoord⟩ := component_point_embedding_of_data F D W hb t ht x hbeta hpoint
  exact ⟨hdom, a, htower, hfinite, rho, ht, hcoord⟩

end APSCounting893.Main
end Component_10

section Component_11

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



end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def tCoefficientHom : Polynomial ℂ →+* PuiseuxAmbient :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ))

noncomputable def tAuxHom : Aux →+* PuiseuxAmbient :=
  MvPolynomial.eval₂Hom HahnSeries.C
    (fun v : Fin 4 => if v = 2 then HahnSeries.single (1 : ℚ) (1 : ℂ) else 0)

lemma tCoefficient_C (c : ℂ) : tCoefficientHom (Polynomial.C c) = HahnSeries.C c := by
  simp [tCoefficientHom]

lemma tAux_polynomial_coefficients (p : Polynomial ℂ) :
    tAuxHom ((Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) p) =
      tCoefficientHom p := by
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [tAuxHom, tCoefficientHom]
    · simp [tAuxHom, tCoefficientHom]
  exact RingHom.congr_fun heq p

lemma equationWithAux_specializes (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) (x : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    MvPolynomial.eval₂ tAuxHom x (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ tCoefficientHom x
        (affineLineEquations F c alpha (Fin.cast (Nat.add_comm _ _) i)) := by
  rw [equationWithAux, MvPolynomial.eval₂_map]
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    exact RingHom.ext tAux_polynomial_coefficients
  rw [heq]

lemma affineLineEquations_iff (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    (∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0) ↔
      (∀ j : Fin (F.n + 1), z (j.natAdd F.n) =
        MvPolynomial.eval₂ HahnSeries.C (fun i => z (i.castAdd (F.n + 1))) (F.F j)) ∧
      (∀ j : Fin F.n, z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) := by
  have hcomp : tCoefficientHom.comp Polynomial.C = HahnSeries.C := by
    exact RingHom.ext tCoefficient_C
  have hout (j : Fin (F.n + 1)) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.castAdd F.n)) =
      z (j.natAdd F.n) - MvPolynomial.eval₂ HahnSeries.C
        (fun i => z (i.castAdd (F.n + 1))) (F.F j) := by
    simp only [affineLineEquations, Fin.addCases_left, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map, hcomp]
    rfl
  have hline (j : Fin F.n) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.natAdd (F.n + 1))) =
      z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) -
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    simp [affineLineEquations, tCoefficientHom]
  constructor
  · intro h
    exact ⟨fun j => sub_eq_zero.mp ((hout j).symm.trans (h _)),
      fun j => sub_eq_zero.mp ((hline j).symm.trans (h _))⟩
  · rintro ⟨ho, hl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hout, ho, sub_self]
    · rw [hline, hl, sub_self]

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma series_parameter_transcendental :
    Transcendental ℂ (HahnSeries.single (1 : ℚ) (1 : ℂ) : PuiseuxAmbient) := by
  apply transcendental_iff_injective.mpr
  have heq : (Polynomial.aeval (HahnSeries.single (1 : ℚ) (1 : ℂ) : PuiseuxAmbient)).toRingHom =
      rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro c
      change Polynomial.aeval (HahnSeries.single (1 : ℚ) (1 : ℂ) : PuiseuxAmbient) (Polynomial.C c) =
        rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))
      rw [Polynomial.aeval_C]
      change algebraMap ℂ PuiseuxAmbient c = rationalSeriesHom
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
      rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), rationalSeriesHom.commutes]
    · change Polynomial.aeval (HahnSeries.single (1 : ℚ) (1 : ℂ) : PuiseuxAmbient) Polynomial.X =
        rationalSeriesHom (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
      rw [Polynomial.aeval_X]
      exact rationalSeriesHom_X.symm
  change Function.Injective (Polynomial.aeval (HahnSeries.single (1 : ℚ) (1 : ℂ) : PuiseuxAmbient)).toRingHom
  rw [heq]
  exact rationalSeriesHom.injective.comp (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))

lemma raw_beta_point_puiseux (F : ReducedMap) (D : LineData F)
    (x : Affine PuiseuxAmbient F.n)
    (hbeta : ∀ j, MvPolynomial.eval₂ HahnSeries.C x (betaPolynomials F D.c j) =
      HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) :
    ∀ j, IsPuiseux (x j) := by
  have halg : (algebraMap ℂ PuiseuxAmbient) = (HahnSeries.C : ℂ →+* PuiseuxAmbient) := by
    ext c
    simp [HahnSeries.algebraMap_apply']
  have hb : ∀ j, MvPolynomial.eval₂ (algebraMap ℂ PuiseuxAmbient) x (betaPolynomials F D.c j) =
      algebraMap ℂ PuiseuxAmbient (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    simpa only [halg] using hbeta
  obtain ⟨W, hW, hpoint⟩ := raw_point_graph_component F D _ series_parameter_transcendental x hb
  obtain ⟨hdom, a, htower, hfinite, rho, ht, hcoord⟩ :=
    component_point_field_embedding F D W hW _ series_parameter_transcendental x hb hpoint
  letI := hdom
  letI := a
  letI := htower
  letI := hfinite
  intro j
  rw [← hcoord j]
  exact algebraic_image_puiseux rho ht _

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
open scoped RatFunc
namespace APSCounting893.Main

lemma component_raw_beta_points_finite (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n))
    (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    {x : Affine PuiseuxAmbient F.n |
      (∀ j, MvPolynomial.eval₂ HahnSeries.C x (betaPolynomials F D.c j) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) ∧
      (∀ p ∈ vanishingIdeal ℂ W, MvPolynomial.eval₂ HahnSeries.C x p = 0)}.Finite := by
  classical
  obtain ⟨hdom, a, htower, hfinite, hb⟩ := (dominant_graph_components F D W hW).2
  letI := hdom
  letI := a
  letI := htower
  letI := hfinite
  let E := FractionRing (CoordinateRing W)
  letI : Algebra (RatFunc ℂ) PuiseuxAmbient := rationalSeriesHom.toRingHom.toAlgebra
  let f : (E →ₐ[RatFunc ℂ] PuiseuxAmbient) → Affine PuiseuxAmbient F.n :=
    fun rho j => rho (algebraMap (CoordinateRing W) E (coordinate W j))
  apply (Set.finite_range f).subset
  rintro x ⟨hbeta, hpoint⟩
  have halg : algebraMap ℂ PuiseuxAmbient = (HahnSeries.C : ℂ →+* PuiseuxAmbient) := by
    ext c
    simp [HahnSeries.algebraMap_apply']
  obtain ⟨rho, ht, hcoord⟩ := component_point_embedding_of_data F D W hb _
    series_parameter_transcendental x (by simpa only [halg] using hbeta)
    (by simpa only [halg] using hpoint)
  have heq := rationalSeriesHom_unique rho ht
  let sigma : E →ₐ[RatFunc ℂ] PuiseuxAmbient :=
    { toRingHom := rho.toRingHom
      commutes' := fun r => by
        change rho (algebraMap (RatFunc ℂ) E r) = rationalSeriesHom r
        exact RingHom.congr_fun heq r }
  refine ⟨sigma, ?_⟩
  funext j
  exact hcoord j

lemma affineComponents_finite {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (C : Set (Affine K n)) (hC : RSCapacity.IsAlgSet C) :
    {W | AffineComponent C W}.Finite := by
  classical
  apply ((vanishingIdeal K C).finite_minimalPrimes_of_isNoetherianRing.image
    (fun Q => zeroLocus K Q)).subset
  intro W hW
  refine ⟨vanishingIdeal K W, affineComponent_ideal_minimal hC hW, ?_⟩
  exact (isAlgSet_eq_zeroLocus hW.1.2.1).symm

lemma raw_beta_points_finite (F : ReducedMap) (D : LineData F) :
    {x : Affine PuiseuxAmbient F.n |
      ∀ j, MvPolynomial.eval₂ HahnSeries.C x (betaPolynomials F D.c j) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)}.Finite := by
  classical
  let C := closedGraphCurve F D.c D.alpha D.U
  have hc : RSCapacity.IsAlgSet C := isAlgSet_zeroLocus _
  let T := {W | AffineComponent C W}
  let Z := fun W : Set (Affine ℂ F.n) => {x : Affine PuiseuxAmbient F.n |
      (∀ j, MvPolynomial.eval₂ HahnSeries.C x (betaPolynomials F D.c j) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) ∧
      (∀ p ∈ vanishingIdeal ℂ W, MvPolynomial.eval₂ HahnSeries.C x p = 0)}
  have hfinite : (⋃ W ∈ T, Z W).Finite :=
    (affineComponents_finite C hc).biUnion (fun W hW => component_raw_beta_points_finite F D W hW)
  apply hfinite.subset
  intro x hx
  change ∀ j, MvPolynomial.eval₂ HahnSeries.C x (betaPolynomials F D.c j) =
    HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) at hx
  have halg : algebraMap ℂ PuiseuxAmbient = (HahnSeries.C : ℂ →+* PuiseuxAmbient) := by
    ext c
    simp [HahnSeries.algebraMap_apply']
  obtain ⟨W, hW, hpoint⟩ := raw_point_graph_component F D _ series_parameter_transcendental x
    (by simpa only [halg] using hx)
  exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hW, hx, by simpa only [halg] using hpoint⟩⟩

end APSCounting893.Main
end Component_14

section Component_15

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
end Component_15

section Component_16

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma isPuiseux_add {s t : PuiseuxAmbient} (hs : IsPuiseux s) (ht : IsPuiseux t) :
    IsPuiseux (s+t) := by
  obtain ⟨e, he, hs⟩ := hs
  obtain ⟨f, hf, ht⟩ := ht
  refine ⟨e*f, Nat.mul_pos he hf, ?_⟩
  have hs' := ramBound_mul_right he hf ((HahnSeries.mem_puiseuxRamSubfield_iff he).mp hs)
  have ht' := ramBound_mul_right hf he ((HahnSeries.mem_puiseuxRamSubfield_iff hf).mp ht)
  rw [Nat.mul_comm f e] at ht'
  exact (HahnSeries.puiseuxRamSubfield ℂ (Nat.mul_pos he hf)).add_mem
    ((HahnSeries.mem_puiseuxRamSubfield_iff (Nat.mul_pos he hf)).mpr hs')
    ((HahnSeries.mem_puiseuxRamSubfield_iff (Nat.mul_pos he hf)).mpr ht')

lemma isPuiseux_eval {n : ℕ} (p : Polynomials ℂ n) (x : Affine PuiseuxAmbient n)
    (hx : ∀ j, IsPuiseux (x j)) : IsPuiseux (MvPolynomial.eval₂ HahnSeries.C x p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.eval₂_C]
      change IsPuiseux (HahnSeries.single (0 : ℚ) c)
      exact isPuiseux_single _ c
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using isPuiseux_add hp hq
  | mul_X p j hp =>
      simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using isPuiseux_mul hp (hx j)

lemma raw_line_input_beta (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n+1)))
    (hz : ∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0) :
    ∀ j, MvPolynomial.eval₂ HahnSeries.C (fun i => z (i.castAdd (F.n+1))) (betaPolynomials F D.c j) =
      HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) := by
  obtain ⟨ho, hl⟩ := (affineLineEquations_iff F D z).mp hz
  intro j
  simp only [betaPolynomials, normalizationPolynomials, map_sub,
    MvPolynomial.eval₂Hom_X', map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  rw [← ho j.castSucc, ← ho (Fin.last F.n)]
  exact hl j

lemma raw_line_point_puiseux (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n+1)))
    (hz : ∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0) :
    z ∈ lineSolutions F D := by
  obtain ⟨ho, hl⟩ := (affineLineEquations_iff F D z).mp hz
  have hx := raw_beta_point_puiseux F D _ (raw_line_input_beta F D z hz)
  refine ⟨?_, ho, hl⟩
  intro j
  refine Fin.addCases (fun i => hx i) (fun i => ?_) j
  rw [ho]
  exact isPuiseux_eval (F.F i) _ hx

lemma raw_line_points_finite (F : ReducedMap) (D : LineData F) :
    {z : Affine PuiseuxAmbient (F.n + (F.n+1)) |
      ∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0}.Finite := by
  let fill : Affine PuiseuxAmbient F.n → Affine PuiseuxAmbient (F.n + (F.n+1)) :=
    fun x => Fin.addCases x (fun j => MvPolynomial.eval₂ HahnSeries.C x (F.F j))
  apply ((raw_beta_points_finite F D).image fill).subset
  intro z hz
  have hb := raw_line_input_beta F D z hz
  refine ⟨(fun i => z (i.castAdd (F.n+1))), hb, ?_⟩
  obtain ⟨ho, hl⟩ := (affineLineEquations_iff F D z).mp hz
  funext j
  refine Fin.addCases (fun i => by simp [fill]) (fun i => ?_) j
  simpa only [fill, Fin.addCases_right] using (ho i).symm

end APSCounting893.Main
end Component_16

section Component_17

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
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main.GenericSeries
variable {K : Type} [Field K]

lemma curve_normalization_parameter (B : Type) [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (hdim : ringKrullDim B = 1) (ψ : B →ₐ[K] K) :
    ∃ g : Polynomial K →ₐ[K] B, Function.Injective g ∧ g.Finite ∧ ψ (g Polynomial.X) = 0 := by
  classical
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  have hs : s = 1 := by
    letI : Algebra (MvPolynomial (Fin s) K) B := g.toRingHom.toAlgebra
    letI : Module.Finite (MvPolynomial (Fin s) K) B := hfin
    have hd := integral_dimension_eq (R := MvPolynomial (Fin s) K) (S := B) hinj
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      zero_add, Nat.card_eq_fintype_card, Fintype.card_fin, hdim] at hd
    exact_mod_cast hd
  subst s
  let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  let g₀ : Polynomial K →ₐ[K] B := g.comp e.symm.toAlgHom
  let c : K := ψ (g₀ Polynomial.X)
  let shift := Polynomial.algEquivAevalXAddC (-c)
  let g₁ : Polynomial K →ₐ[K] B := g₀.comp shift.toAlgHom
  have hg₀ : g₀.Finite := hfin.comp (RingHom.Finite.of_surjective _ e.symm.surjective)
  have hg₁ : g₁.Finite := hg₀.comp (RingHom.Finite.of_surjective _ shift.surjective)
  refine ⟨g₁, (hinj.comp e.symm.injective).comp shift.injective, hg₁, ?_⟩
  change ψ (g₀ (shift Polynomial.X)) = 0
  have hconst (z : K) : ψ (g₀ (Polynomial.C z)) = z := by
    change ψ (g₀ (algebraMap K (Polynomial K) z)) = z
    rw [g₀.commutes, ψ.commutes]
    rfl
  simp [shift, Polynomial.algEquivAevalXAddC, hconst, c]


end APSCounting893.Main.GenericSeries
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
open scoped LaurentSeries RatFunc
namespace APSCounting893.Main.GenericSeries

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]

noncomputable abbrev seriesValuationRing : ValuationSubring (HahnSeries ℚ K) := nonnegativeHahnRing K
noncomputable abbrev seriesResidueHom : seriesValuationRing (K := K) →+* K := hahnResidueHom K
noncomputable abbrev constantSeriesHom : K →+* seriesValuationRing (K := K) := hahnConstantLift K
lemma seriesResidue_constant (c : K) : seriesResidueHom (constantSeriesHom c) = c := hahnResidue_constant c

lemma seriesResidue_surjective : Function.Surjective (seriesResidueHom (K := K)) := by
  intro c
  exact ⟨(constantSeriesHom (K := K)) c, seriesResidue_constant c⟩

noncomputable def polynomialSeriesHom : Polynomial K →+* (seriesValuationRing (K := K)) :=
  Polynomial.eval₂RingHom (constantSeriesHom (K := K))
    ⟨HahnSeries.single (1 : ℚ) (1 : K), by
      exact (show (0 : WithTop ℚ) ≤ 1 by norm_num).trans HahnSeries.orderTop_single_le⟩

lemma polynomialSeriesHom_residue (p : Polynomial K) :
    (seriesResidueHom (K := K)) (polynomialSeriesHom p) = p.eval 0 := by
  change ((seriesResidueHom (K := K)).comp polynomialSeriesHom) p = _
  have h : (seriesResidueHom (K := K)).comp polynomialSeriesHom = Polynomial.evalRingHom (0 : K) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [polynomialSeriesHom, seriesResidue_constant]
    · simp [polynomialSeriesHom, seriesResidueHom, hahnResidueHom]
  rw [h]
  rfl

lemma finite_flat_series_lift
    (B : Type) [CommRing B] [Algebra (Polynomial K) B]
    [Module.Finite (Polynomial K) B] [Module.Flat (Polynomial K) B]
    (φ₀ : B →+* K)
    (hcomp : φ₀.comp (algebraMap (Polynomial K) B) = Polynomial.evalRingHom (0 : K)) :
    ∃ φ : B →+* (seriesValuationRing (K := K)),
      φ.comp (algebraMap (Polynomial K) B) = polynomialSeriesHom ∧
      (seriesResidueHom (K := K)).comp φ = φ₀ := by
  letI : IsAlgClosed (HahnSeries ℚ K) := HahnSeries.isAlgClosed_rat
  letI : Algebra (Polynomial K) (seriesValuationRing (K := K)) := polynomialSeriesHom.toAlgebra
  apply ValuationSubring.exists_ringHom_comp_eq_of_moduleFinite_of_flat
      (seriesValuationRing (K := K)) (seriesResidueHom (K := K)) seriesResidue_surjective φ₀
  rw [hcomp]
  apply DFunLike.ext
  intro p
  exact (polynomialSeriesHom_residue p).symm

lemma polynomialSeriesHom_injective : Function.Injective (polynomialSeriesHom (K := K)) := by
  have heq : (seriesValuationRing (K := K)).subtype.comp polynomialSeriesHom =
      rationalSeriesHom.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change HahnSeries.C c = rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c))
      change HahnSeries.C c = rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c))
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using (rationalSeriesHom.commutes c).symm
    · simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      change HahnSeries.single (1 : ℚ) (1 : K) =
        rationalSeriesHom (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
      exact rationalSeriesHom_X.symm
  have h : Function.Injective ((seriesValuationRing (K := K)).subtype.comp polynomialSeriesHom) := by
    rw [heq]
    exact (rationalSeriesHom (K := K)).injective.comp (IsFractionRing.injective (Polynomial K) (RatFunc K))
  exact fun x y hxy => h (congrArg (seriesValuationRing (K := K)).subtype hxy)

lemma finite_series_lift_injective
    (B : Type) [CommRing B] [IsDomain B] [Algebra (Polynomial K) B]
    [Module.Finite (Polynomial K) B] (φ : B →+* (seriesValuationRing (K := K)))
    (hφ : φ.comp (algebraMap (Polynomial K) B) = polynomialSeriesHom) :
    Function.Injective φ := by
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := Polynomial K)
  change RingHom.ker (φ.comp (algebraMap (Polynomial K) B)) = ⊥
  rw [hφ]
  exact (RingHom.injective_iff_ker_eq_bot _).mp polynomialSeriesHom_injective

lemma finite_curve_series_embedding
    (B E : Type) [CommRing B] [IsDomain B] [Field E]
    [Algebra K B] [Algebra (Polynomial K) B] [IsScalarTower K (Polynomial K) B]
    [Module.Finite (Polynomial K) B] [Module.Flat (Polynomial K) B]
    [Algebra B E] [Algebra K E] [IsScalarTower K B E]
    [Module.IsTorsionFree B E] [Algebra.IsAlgebraic B E]
    (φ₀ : B →+* K)
    (hcomp : φ₀.comp (algebraMap (Polynomial K) B) = Polynomial.evalRingHom (0 : K)) :
    ∃ ρ : E →ₐ[K] (HahnSeries ℚ K),
      ρ (algebraMap B E (algebraMap (Polynomial K) B Polynomial.X)) =
        HahnSeries.single (1 : ℚ) (1 : K) ∧
      ∀ b : B, 0 ≤ (ρ (algebraMap B E b)).orderTop ∧
        (ρ (algebraMap B E b)).coeff 0 = φ₀ b := by
  obtain ⟨φ, hφ, hφres⟩ := finite_flat_series_lift B φ₀ hcomp
  let f : B →+* (HahnSeries ℚ K) := (seriesValuationRing (K := K)).subtype.comp φ
  have hf : Function.Injective f := Subtype.val_injective.comp (finite_series_lift_injective B φ hφ)
  letI : Algebra B (HahnSeries ℚ K) := f.toAlgebra
  letI : Module.IsTorsionFree B (HahnSeries ℚ K) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hf
  letI : IsAlgClosed (HahnSeries ℚ K) := HahnSeries.isAlgClosed_rat
  let σ : E →ₐ[B] (HahnSeries ℚ K) := IsAlgClosed.lift
  have hσ (b : B) : σ (algebraMap B E b) = f b := σ.commutes b
  have hc (c : K) : σ (algebraMap K E c) = HahnSeries.C c := by
    rw [IsScalarTower.algebraMap_apply K B E, hσ,
      IsScalarTower.algebraMap_apply K (Polynomial K) B]
    have hh := RingHom.congr_fun hφ (Polynomial.C c)
    simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] at hh
    change (φ (algebraMap (Polynomial K) B (Polynomial.C c))).val = _
    rw [hh]
    rfl
  let ρ : E →ₐ[K] (HahnSeries ℚ K) :=
    { σ.toRingHom with
      commutes' := fun c => by
        change σ (algebraMap K E c) = algebraMap K (HahnSeries ℚ K) c
        simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using hc c }
  refine ⟨ρ, ?_, ?_⟩
  · change σ _ = _
    rw [hσ]
    have hh := RingHom.congr_fun hφ Polynomial.X
    simp only [RingHom.comp_apply, polynomialSeriesHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at hh
    change (φ (algebraMap (Polynomial K) B Polynomial.X)).val = _
    rw [hh]
  · intro b
    change 0 ≤ (σ (algebraMap B E b)).orderTop ∧ (σ (algebraMap B E b)).coeff 0 = φ₀ b
    rw [hσ]
    exact ⟨(φ b).property, RingHom.congr_fun hφres b⟩


end APSCounting893.Main.GenericSeries
end Component_19

section Component_20

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
open scoped LaurentSeries RatFunc
namespace APSCounting893.Main.GenericSeries
variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K]

lemma curve_branch_embedding (B E : Type) [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (hdim : ringKrullDim B = 1)
    [Field E] [Algebra K E] [Algebra B E] [IsScalarTower K B E]
    [Module.IsTorsionFree B E] [Algebra.IsAlgebraic B E] (ψ : B →ₐ[K] K) :
    ∃ ρ : E →ₐ[K] (HahnSeries ℚ K),
      (∀ x : E, IsPuiseuxOver (ρ x)) ∧
      ∀ b : B, 0 ≤ (ρ (algebraMap B E b)).orderTop ∧ (ρ (algebraMap B E b)).coeff 0 = ψ b := by
  classical
  obtain ⟨g, hinj, hfinite, hgX⟩ := curve_normalization_parameter B hdim ψ
  letI : Algebra (Polynomial K) B := g.toRingHom.toAlgebra
  letI : Module.Finite (Polynomial K) B := hfinite
  letI : Module.IsTorsionFree (Polynomial K) B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  letI : Module.Flat (Polynomial K) B := inferInstance
  letI : IsScalarTower K (Polynomial K) B := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap K B c = g (algebraMap K (Polynomial K) c)
    exact (g.commutes c).symm)
  letI : Algebra (Polynomial K) E := Algebra.compHom E g.toRingHom
  letI : IsScalarTower (Polynomial K) B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower K (Polynomial K) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K B E, IsScalarTower.algebraMap_apply K (Polynomial K) B]
    rfl)
  have hψ : ψ.toRingHom.comp (algebraMap (Polynomial K) B) = Polynomial.evalRingHom (0 : K) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      change ψ (g (algebraMap K (Polynomial K) c)) = c
      rw [g.commutes, ψ.commutes]
      rfl
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      change ψ (g Polynomial.X) = 0
      exact hgX
  have hφinj : Function.Injective (algebraMap (Polynomial K) E) :=
    (FaithfulSMul.algebraMap_injective B E).comp hinj
  let κ : RatFunc K →+* E := IsFractionRing.lift hφinj
  letI : Algebra (RatFunc K) E := κ.toAlgebra
  have hκ (p : Polynomial K) : κ (algebraMap (Polynomial K) (RatFunc K) p) = algebraMap (Polynomial K) E p :=
    IsFractionRing.lift_algebraMap hφinj p
  letI : IsScalarTower (Polynomial K) (RatFunc K) E := IsScalarTower.of_algebraMap_eq (fun p => by
    change algebraMap (Polynomial K) E p = κ (algebraMap (Polynomial K) (RatFunc K) p)
    exact (hκ p).symm)
  letI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
    change algebraMap K E c = κ (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C c))
    rw [hκ]
    change algebraMap K E c = algebraMap (Polynomial K) E (algebraMap K (Polynomial K) c)
    exact IsScalarTower.algebraMap_apply K (Polynomial K) E c)
  letI : Algebra.IsAlgebraic (Polynomial K) E := Algebra.IsAlgebraic.trans (Polynomial K) B E
  letI : Algebra.IsAlgebraic (RatFunc K) E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial K) (K := RatFunc K) (C := E)).mp inferInstance
  obtain ⟨ρ, ht, hres⟩ := finite_curve_series_embedding B E ψ.toRingHom hψ
  have ht' : ρ (algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : K) := by
    change ρ (κ _) = _
    rw [hκ]
    exact ht
  exact ⟨ρ, algebraic_image_puiseux ρ ht', hres⟩


end APSCounting893.Main.GenericSeries
end Component_20

section Component_21

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc
namespace APSCounting893.Main.GenericSeries

lemma curve_function_field_trdeg
    {K B E : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (hdim : ringKrullDim B = 1) (psi : B →ₐ[K] K)
    [Field E] [Algebra B E] [IsFractionRing B E] [Algebra K E] [IsScalarTower K B E] :
    Algebra.trdeg K E = 1 := by
  obtain ⟨g, hinj, hfin, hg⟩ := curve_normalization_parameter B hdim psi
  letI : Algebra (Polynomial K) B := g.toRingHom.toAlgebra
  letI : Module.Finite (Polynomial K) B := hfin
  letI : FaithfulSMul (Polynomial K) B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : IsScalarTower K (Polynomial K) B := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  have hb := trdeg_add_eq K (Polynomial K) (A := B)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at hb
  letI : Algebra.IsAlgebraic B E := IsLocalization.isAlgebraic E (nonZeroDivisors B)
  have he := trdeg_add_eq K B (A := E)
  rw [trdeg_eq_zero (R := B) (A := E), add_zero, ← hb] at he
  exact he.symm

lemma curve_finite_over_parameter
    {K B E : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (hdim : ringKrullDim B = 1) (psi : B →ₐ[K] K)
    [Field E] [Algebra B E] [IsFractionRing B E] [Algebra K E] [IsScalarTower K B E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] :
    FiniteDimensional (RatFunc K) E := by
  have he := curve_function_field_trdeg (E := E) hdim psi
  have hr : Algebra.trdeg K (RatFunc K) = 1 := by
    letI : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
      IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors (Polynomial K))
    have hh := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
    rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at hh
    exact hh.symm
  have hh := trdeg_add_eq K (RatFunc K) (A := E)
  rw [hr, he] at hh
  have hzero : Algebra.trdeg (RatFunc K) E = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hh with h | h
    · exact False.elim ((not_le_of_gt Cardinal.one_lt_aleph0) (le_max_left _ _ |>.trans h))
    · exact h
  letI : Algebra.IsAlgebraic (RatFunc K) E := trdeg_eq_zero_iff.mp hzero
  letI : Algebra.EssFiniteType B E := Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors B)
  letI : Algebra.EssFiniteType K E := Algebra.EssFiniteType.comp K B E
  letI : Algebra.EssFiniteType (RatFunc K) E := Algebra.EssFiniteType.of_comp K (RatFunc K) E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end APSCounting893.Main.GenericSeries
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main.GenericSeries
open IsDedekindDomain

lemma valuation_eq_at_dedekind_place
    {R E : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field E] [Algebra R E] [IsFractionRing R E]
    (v : HeightOneSpectrum R) (V : ValuationSubring E)
    (hR : ∀ r : R, algebraMap R E r ∈ V)
    (hcenter : ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R E r ∈ V.nonunits)
    (hproper : V ≠ ⊤) : v.valuationSubringAtPrime E = V := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hproper
  rintro x ⟨a, s, hs, rfl⟩
  apply V.toSubring.mul_mem (hR a)
  by_contra h
  have hn : algebraMap R E s ∈ V.nonunits :=
    V.mem_nonunits_iff_or.mpr (Or.inr h)
  exact hs ((hcenter s).mpr hn)

lemma valuation_eq_of_same_dedekind_center
    {R E : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field E] [Algebra R E] [IsFractionRing R E]
    (v : HeightOneSpectrum R) (V W : ValuationSubring E)
    (hRV : ∀ r : R, algebraMap R E r ∈ V)
    (hRW : ∀ r : R, algebraMap R E r ∈ W)
    (hV : ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R E r ∈ V.nonunits)
    (hW : ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R E r ∈ W.nonunits)
    (hVp : V ≠ ⊤) (hWp : W ≠ ⊤) : V = W := by
  exact (valuation_eq_at_dedekind_place v V hRV hV hVp).symm.trans
    (valuation_eq_at_dedekind_place v W hRW hW hWp)

end APSCounting893.Main.GenericSeries
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main.GenericSeries
open IsDedekindDomain

lemma hahn_nonunit_iff_residue_zero {K : Type} [Field K]
    (x : nonnegativeHahnRing K) :
    x.val ∈ (nonnegativeHahnRing K).nonunits ↔ hahnResidueHom K x = 0 := by
  have hs : Function.Surjective (hahnResidueHom K) :=
    fun c => ⟨hahnConstantLift K c, hahnResidue_constant c⟩
  have hm : (RingHom.ker (hahnResidueHom K)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hs
  rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.eq_maximalIdeal hm]
  rfl

lemma comap_nonunits {E H : Type} [Field E] [Field H]
    (V : ValuationSubring H) (f : E →+* H) (x : E) :
    x ∈ (V.comap f).nonunits ↔ f x ∈ V.nonunits := by
  simp only [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

lemma hahn_residue_comparison
    {R E K : Type} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field E] [Algebra R E] [IsFractionRing R E] [Field K]
    (rho sigma : E →+* HahnSeries ℚ K)
    (hRrho : ∀ r : R, 0 ≤ (rho (algebraMap R E r)).orderTop)
    (hRsigma : ∀ r : R, 0 ≤ (sigma (algebraMap R E r)).orderTop)
    (phi : R →+* K) (hphi : Function.Surjective phi) (hker : RingHom.ker phi ≠ ⊥)
    (hrho : ∀ r : R, (rho (algebraMap R E r)).coeff 0 = phi r)
    (hsigma : ∀ r : R, (sigma (algebraMap R E r)).coeff 0 = phi r)
    (hproperrho : (nonnegativeHahnRing K).comap rho ≠ ⊤)
    (hpropersigma : (nonnegativeHahnRing K).comap sigma ≠ ⊤) :
    ∀ x : E, 0 ≤ (rho x).orderTop →
      0 ≤ (sigma x).orderTop ∧ (sigma x).coeff 0 = (rho x).coeff 0 := by
  classical
  let v : HeightOneSpectrum R :=
    ⟨RingHom.ker phi, (RingHom.ker_isMaximal_of_surjective phi hphi).isPrime, hker⟩
  let V := (nonnegativeHahnRing K).comap rho
  let W := (nonnegativeHahnRing K).comap sigma
  have hcV (r : R) : r ∈ v.asIdeal ↔ algebraMap R E r ∈ V.nonunits := by
    rw [comap_nonunits]
    have hh := hahn_nonunit_iff_residue_zero ⟨_, hRrho r⟩
    change rho (algebraMap R E r) ∈ (nonnegativeHahnRing K).nonunits ↔
      (rho (algebraMap R E r)).coeff 0 = 0 at hh
    exact (hh.trans (by rw [hrho]; rfl)).symm
  have hcW (r : R) : r ∈ v.asIdeal ↔ algebraMap R E r ∈ W.nonunits := by
    rw [comap_nonunits]
    have hh := hahn_nonunit_iff_residue_zero ⟨_, hRsigma r⟩
    change sigma (algebraMap R E r) ∈ (nonnegativeHahnRing K).nonunits ↔
      (sigma (algebraMap R E r)).coeff 0 = 0 at hh
    exact (hh.trans (by rw [hsigma]; rfl)).symm
  have hV := valuation_eq_at_dedekind_place v V hRrho hcV hproperrho
  have hW := valuation_eq_at_dedekind_place v W hRsigma hcW hpropersigma
  intro x hx
  have hxV : x ∈ v.valuationSubringAtPrime E := hV ▸ hx
  rcases hxV with ⟨a, s, hs, rfl⟩
  have hsV : (rho (algebraMap R E s))⁻¹ ∈ nonnegativeHahnRing K := by
    by_contra hn
    have hnu := (nonnegativeHahnRing K).mem_nonunits_iff_or.mpr (Or.inr hn)
    exact hs ((hcV s).mpr ((comap_nonunits _ _ _).mpr hnu))
  have hsW : (sigma (algebraMap R E s))⁻¹ ∈ nonnegativeHahnRing K := by
    by_contra hn
    have hnu := (nonnegativeHahnRing K).mem_nonunits_iff_or.mpr (Or.inr hn)
    exact hs ((hcW s).mpr ((comap_nonunits _ _ _).mpr hnu))
  have hsinv : ((sigma (algebraMap R E s))⁻¹).coeff 0 =
      ((rho (algebraMap R E s))⁻¹).coeff 0 := by
    have hsn : phi s ≠ 0 := hs
    have h1 := hahn_coeff_zero_mul_nonnegative (sigma (algebraMap R E s))
      ((sigma (algebraMap R E s))⁻¹) (hRsigma s) hsW
    have h2 := hahn_coeff_zero_mul_nonnegative (rho (algebraMap R E s))
      ((rho (algebraMap R E s))⁻¹) (hRrho s) hsV
    have hsnS : sigma (algebraMap R E s) ≠ 0 := fun hz => hsn (by rw [← hsigma s, hz]; simp)
    have hsnR : rho (algebraMap R E s) ≠ 0 := fun hz => hsn (by rw [← hrho s, hz]; simp)
    rw [mul_inv_cancel₀ hsnS, HahnSeries.coeff_one, if_pos rfl, hsigma] at h1
    rw [mul_inv_cancel₀ hsnR, HahnSeries.coeff_one, if_pos rfl, hrho] at h2
    exact mul_left_cancel₀ hsn (h1.symm.trans h2)
  constructor
  · change sigma ((algebraMap R E) a * ((algebraMap R E) s)⁻¹) ∈ nonnegativeHahnRing K
    rw [map_mul, map_inv₀]
    exact (nonnegativeHahnRing K).toSubring.mul_mem (hRsigma a) hsW
  · simp only [map_mul, map_inv₀]
    rw [hahn_coeff_zero_mul_nonnegative _ _ (hRsigma a) hsW,
      hahn_coeff_zero_mul_nonnegative _ _ (hRrho a) hsV, hsigma, hrho, hsinv]

end APSCounting893.Main.GenericSeries
end Component_23

section Component_24

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc
namespace APSCounting893.Main.GenericSeries

lemma hahn_comap_ne_top_of_zero_residue {K E : Type} [Field K] [Field E]
    (rho : E →+* HahnSeries ℚ K) (t : E) (ht : t ≠ 0)
    (hr : 0 ≤ (rho t).orderTop) (hz : (rho t).coeff 0 = 0) :
    (nonnegativeHahnRing K).comap rho ≠ ⊤ := by
  intro heq
  have hi : 0 ≤ (rho t⁻¹).orderTop := by
    change t⁻¹ ∈ (nonnegativeHahnRing K).comap rho
    rw [heq]
    trivial
  have hh := hahn_coeff_zero_mul_nonnegative (rho t) (rho t⁻¹) hr hi
  rw [← map_mul, mul_inv_cancel₀ ht, map_one, hz, zero_mul] at hh
  simpa using hh

lemma prescribe_series_parameter
    {K E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field E] [Algebra K E] [Algebra (Polynomial K) E] [Algebra (RatFunc K) E]
    [IsScalarTower K (Polynomial K) E] [IsScalarTower K (RatFunc K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (rho : E →ₐ[K] HahnSeries ℚ K)
    (htr : 0 ≤ (rho (algebraMap (Polynomial K) E Polynomial.X)).orderTop)
    (htz : (rho (algebraMap (Polynomial K) E Polynomial.X)).coeff 0 = 0) :
    ∃ sigma : E →ₐ[K] HahnSeries ℚ K,
      sigma (algebraMap (Polynomial K) E Polynomial.X) = HahnSeries.single (1 : ℚ) (1 : K) ∧
      (∀ x : E, IsPuiseuxOver (sigma x)) ∧
      (∀ x : E, 0 ≤ (rho x).orderTop →
        0 ≤ (sigma x).orderTop ∧ (sigma x).coeff 0 = (rho x).coeff 0) := by
  classical
  let A := integralClosure (Polynomial K) E
  let V := (nonnegativeHahnRing K).comap rho.toRingHom
  letI : IsFractionRing V.toSubring E := inferInstanceAs (IsFractionRing V E)
  letI : Module.IsTorsionFree (Polynomial K) E :=
    .trans_faithfulSMul (Polynomial K) (RatFunc K) E
  have hpoly : ∀ p : Polynomial K, algebraMap (Polynomial K) E p ∈ V := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact V.toSubring.add_mem hp hq
    | monomial n c =>
      rw [Polynomial.C_mul_X_pow_eq_monomial.symm, map_mul, map_pow]
      apply V.toSubring.mul_mem
      · change 0 ≤ (rho (algebraMap (Polynomial K) E (Polynomial.C c))).orderTop
        change 0 ≤ (rho (algebraMap (Polynomial K) E (algebraMap K (Polynomial K) c))).orderTop
        rw [← IsScalarTower.algebraMap_apply K (Polynomial K) E, rho.commutes]
        have hc : 0 ≤ (HahnSeries.C c : HahnSeries ℚ K).orderTop := by
          rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.order_C]
        simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using hc
      · exact V.toSubring.pow_mem htr n
  have hA : ∀ a : A, (a : E) ∈ V := by
    exact fun a => (Subring.integralClosure_le_iff.mpr hpoly) a.property
  let f : A →+* nonnegativeHahnRing K :=
    (rho.toRingHom.comp (algebraMap A E)).codRestrict _ hA
  let phi : A →+* K := (hahnResidueHom K).comp f
  have hres (a : A) : (rho (algebraMap A E a)).coeff 0 = phi a := rfl
  have hcomp : phi.comp (algebraMap (Polynomial K) A) = Polynomial.evalRingHom (0 : K) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      change (rho (algebraMap A E (algebraMap (Polynomial K) A (Polynomial.C c)))).coeff 0 = c
      rw [← IsScalarTower.algebraMap_apply]
      change (rho (algebraMap (Polynomial K) E (algebraMap K (Polynomial K) c))).coeff 0 = c
      rw [← IsScalarTower.algebraMap_apply K (Polynomial K) E, rho.commutes]
      simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      change (rho (algebraMap A E (algebraMap (Polynomial K) A Polynomial.X))).coeff 0 = 0
      rw [← IsScalarTower.algebraMap_apply]
      exact htz
  letI : Module.Finite (Polynomial K) A :=
    IsIntegralClosure.finite (Polynomial K) (RatFunc K) E A
  letI : Module.IsTorsionFree (Polynomial K) A :=
    IsIntegralClosure.isTorsionFree (Polynomial K) E
  letI : Module.Flat (Polynomial K) A := inferInstance
  letI : IsFractionRing A E :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial K) (RatFunc K) E A
  letI : IsDedekindDomain A :=
    IsIntegralClosure.isDedekindDomain (Polynomial K) (RatFunc K) E A
  letI : Algebra.IsAlgebraic A E := IsLocalization.isAlgebraic E (nonZeroDivisors A)
  obtain ⟨sigma, ht, hs⟩ := finite_curve_series_embedding A E phi hcomp
  have ht' : sigma (algebraMap (Polynomial K) E Polynomial.X) =
      HahnSeries.single (1 : ℚ) (1 : K) := by
    rw [IsScalarTower.algebraMap_apply (Polynomial K) A E]
    exact ht
  have ht'' : sigma (algebraMap (RatFunc K) E
      (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : K) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact ht'
  have hsurj : Function.Surjective phi := by
    intro c
    refine ⟨algebraMap K A c, ?_⟩
    change (rho (algebraMap A E (algebraMap K A c))).coeff 0 = c
    rw [← IsScalarTower.algebraMap_apply, rho.commutes]
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]
  have hXne : algebraMap (Polynomial K) E Polynomial.X ≠ 0 := by
    simpa only [map_zero] using
      (FaithfulSMul.algebraMap_injective (Polynomial K) E).ne Polynomial.X_ne_zero
  have hk : RingHom.ker phi ≠ ⊥ := by
    intro hk
    have hmem : algebraMap (Polynomial K) A Polynomial.X ∈ RingHom.ker phi := by
      rw [RingHom.mem_ker]
      simpa using RingHom.congr_fun hcomp Polynomial.X
    rw [hk, Ideal.mem_bot] at hmem
    apply hXne
    rw [IsScalarTower.algebraMap_apply (Polynomial K) A E, hmem, map_zero]
  refine ⟨sigma, ht', algebraic_image_puiseux sigma ht'', ?_⟩
  apply hahn_residue_comparison rho.toRingHom sigma.toRingHom
    (fun a => by
      have hh := hA a
      change 0 ≤ (rho (algebraMap A E a)).orderTop at hh
      exact hh) (fun a => (hs a).1) phi hsurj hk hres (fun a => (hs a).2)
  · exact hahn_comap_ne_top_of_zero_residue rho.toRingHom _ hXne htr htz
  · apply hahn_comap_ne_top_of_zero_residue sigma.toRingHom _ hXne
    · change 0 ≤ (sigma (algebraMap (Polynomial K) E Polynomial.X)).orderTop
      rw [ht', HahnSeries.orderTop_single one_ne_zero]
      norm_num
    · change (sigma (algebraMap (Polynomial K) E Polynomial.X)).coeff 0 = 0
      rw [ht']
      simp

end APSCounting893.Main.GenericSeries
end Component_24

section Component_25

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc
namespace APSCounting893.Main.GenericSeries

lemma curve_branch_prescribed_parameter
    {K B E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (hdim : ringKrullDim B = 1) (psi : B →ₐ[K] K)
    [Field E] [Algebra B E] [IsFractionRing B E] [Algebra K E] [IsScalarTower K B E]
    [Algebra (Polynomial K) E] [Algebra (RatFunc K) E]
    [IsScalarTower K (Polynomial K) E] [IsScalarTower K (RatFunc K) E]
    [IsScalarTower (Polynomial K) (RatFunc K) E]
    (t : B) (ht : algebraMap (Polynomial K) E Polynomial.X = algebraMap B E t)
    (hzero : psi t = 0) :
    ∃ rho : E →ₐ[K] HahnSeries ℚ K,
      rho (algebraMap (Polynomial K) E Polynomial.X) = HahnSeries.single (1 : ℚ) (1 : K) ∧
      (∀ x : E, IsPuiseuxOver (rho x)) ∧
      (∀ b : B, 0 ≤ (rho (algebraMap B E b)).orderTop ∧
        (rho (algebraMap B E b)).coeff 0 = psi b) := by
  letI : Algebra.IsAlgebraic B E := IsLocalization.isAlgebraic E (nonZeroDivisors B)
  obtain ⟨sigma, hs, hres⟩ := curve_branch_embedding B E hdim psi
  letI : FiniteDimensional (RatFunc K) E := curve_finite_over_parameter hdim psi
  have hr : 0 ≤ (sigma (algebraMap (Polynomial K) E Polynomial.X)).orderTop := by
    rw [ht]
    exact (hres t).1
  have hz : (sigma (algebraMap (Polynomial K) E Polynomial.X)).coeff 0 = 0 := by
    rw [ht, (hres t).2, hzero]
  obtain ⟨rho, ht', hpu, hsame⟩ := prescribe_series_parameter sigma hr hz
  refine ⟨rho, ht', hpu, ?_⟩
  intro b
  obtain ⟨hreg, heq⟩ := hsame _ (hres b).1
  exact ⟨hreg, heq.trans (hres b).2⟩

end APSCounting893.Main.GenericSeries
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped RatFunc
namespace APSCounting893.Main.GenericSeries

lemma integral_eq_constant {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A]
    (x : A) (hx : IsIntegral K x) : ∃ c : K, algebraMap K A c = x := by
  let p := minpoly K x
  have hmonic : p.leadingCoeff = 1 := minpoly.monic hx
  have hdeg : p.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hx)
  have hroot : Polynomial.aeval x p = 0 := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg, hmonic, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hroot
  exact ⟨-p.coeff 0, by rw [map_neg]; exact hroot.symm⟩

lemma curve_series_arc
    {K B : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (hdim : ringKrullDim B = 1) (psi psi' : B →ₐ[K] K)
    (t : B) (hzero : psi t = 0) (hne : psi' t ≠ 0) :
    ∃ rho : B →ₐ[K] HahnSeries ℚ K,
      rho t = HahnSeries.single (1 : ℚ) (1 : K) ∧
      (∀ b : B, IsPuiseuxOver (rho b) ∧ 0 ≤ (rho b).orderTop ∧
        (rho b).coeff 0 = psi b) := by
  classical
  have htB : Transcendental K t := by
    intro h
    obtain ⟨c, hc⟩ := integral_eq_constant t h.isIntegral
    have hc0 : c = 0 := by
      have hh := congrArg psi hc
      rw [psi.commutes, hzero] at hh
      exact hh
    apply hne
    rw [← hc, psi'.commutes, hc0, map_zero]
  let E := FractionRing B
  let tE := algebraMap B E t
  have htE : Transcendental K tE := by
    intro h
    exact htB ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom K B E)
      (IsFractionRing.injective B E)).mp h)
  let g : Polynomial K →+* E := (Polynomial.aeval tE).toRingHom
  have hg : Function.Injective g := transcendental_iff_injective.mp htE
  letI : Algebra (Polynomial K) E := g.toAlgebra
  let u : RatFunc K →+* E := IsFractionRing.lift hg
  letI : Algebra (RatFunc K) E := u.toAlgebra
  have hu (p : Polynomial K) : u (algebraMap (Polynomial K) (RatFunc K) p) = g p :=
    IsFractionRing.lift_algebraMap hg p
  letI : IsScalarTower (Polynomial K) (RatFunc K) E := IsScalarTower.of_algebraMap_eq (fun p => (hu p).symm)
  letI : IsScalarTower K (Polynomial K) E := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap K E c = Polynomial.aeval tE (algebraMap K (Polynomial K) c)
    exact (Polynomial.aeval tE).commutes c |>.symm)
  letI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
    change algebraMap K E c = u (algebraMap (Polynomial K) (RatFunc K) (algebraMap K (Polynomial K) c))
    rw [hu]
    exact (Polynomial.aeval tE).commutes c |>.symm)
  obtain ⟨sigma, hs, hpu, hres⟩ := curve_branch_prescribed_parameter (E := E) hdim psi t
    (by change Polynomial.aeval tE Polynomial.X = tE; exact Polynomial.aeval_X tE) hzero
  let rho : B →ₐ[K] HahnSeries ℚ K := sigma.comp (IsScalarTower.toAlgHom K B E)
  refine ⟨rho, ?_, ?_⟩
  · change sigma tE = _
    have hh : sigma (Polynomial.aeval tE Polynomial.X) = _ := hs
    simpa only [Polynomial.aeval_X] using hh
  · intro b
    exact ⟨hpu _, (hres b).1, (hres b).2⟩

end APSCounting893.Main.GenericSeries
end Component_26

section Component_27

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main.GenericSeries

lemma algHom_to_ground_surjective {K A : Type} [Field K] [CommRing A] [Algebra K A]
    (psi : A →ₐ[K] K) : Function.Surjective psi := by
  intro c
  exact ⟨algebraMap K A c, by simpa using psi.commutes c⟩

lemma two_point_series_arc
    {K A : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (psi psi' : A →ₐ[K] K) (t : A) (hzero : psi t = 0) (hne : psi' t ≠ 0) :
    ∃ rho : A →ₐ[K] HahnSeries ℚ K,
      rho t = HahnSeries.single (1 : ℚ) (1 : K) ∧
      (∀ a : A, IsPuiseuxOver (rho a) ∧ 0 ≤ (rho a).orderTop ∧
        (rho a).coeff 0 = psi a) := by
  classical
  let m := RingHom.ker psi.toRingHom
  let m' := RingHom.ker psi'.toRingHom
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (algHom_to_ground_surjective psi)
  letI : m'.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (algHom_to_ground_surjective psi')
  have ht : t ≠ 0 := fun hz => hne (by rw [hz, map_zero])
  have htm : Ideal.span ({t} : Set A) ≤ m := Ideal.span_le.mpr (by
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    exact hzero)
  have hheight : (1 : ℕ∞) ≤ m.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr ht)).trans (Ideal.height_mono htm)
  have hdim : 1 ≤ ringKrullDim A :=
    (show (1 : WithBot ℕ∞) ≤ (m.height : WithBot ℕ∞) by exact_mod_cast hheight).trans
      Ideal.height_le_ringKrullDim_of_isPrime
  obtain ⟨P, hP, hPm, hPm', hdimP⟩ :=
    Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one K hdim m m'
  letI : P.IsPrime := hP
  let q := Ideal.Quotient.mkₐ K P
  let phi : A ⧸ P →ₐ[K] K := Ideal.Quotient.liftₐ P psi hPm
  let phi' : A ⧸ P →ₐ[K] K := Ideal.Quotient.liftₐ P psi' hPm'
  obtain ⟨sigma, hs, hres⟩ := curve_series_arc hdimP phi phi' (q t) hzero hne
  refine ⟨sigma.comp q, hs, ?_⟩
  intro a
  exact hres (q a)

end APSCounting893.Main.GenericSeries
end Component_27

section Component_28

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def coordinateEvaluation {K : Type} [Field K] {n : ℕ}
    (W : Set (Affine K n)) : CoordinateRing W →ₐ[K] (W → K) :=
  AlgHom.pi (fun x : W => Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x.val)
    (fun p hp => hp x.val x.property))

lemma coordinateEvaluation_injective {K : Type} [Field K] {n : ℕ}
    (W : Set (Affine K n)) : Function.Injective (coordinateEvaluation W) := by
  apply (RingHom.injective_iff_ker_eq_bot (coordinateEvaluation W).toRingHom).mpr
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  intro x hx
  exact congrFun (show coordinateEvaluation W (Ideal.Quotient.mk _ p) = 0 from ha) ⟨x, hx⟩

lemma finiteAffineSet_module_finite {K : Type} [Field K] {n : ℕ}
    (W : Set (Affine K n)) (hW : W.Finite) : Module.Finite K (CoordinateRing W) := by
  letI : Fintype W := hW.fintype
  exact Module.Finite.of_injective (coordinateEvaluation W).toLinearMap
    (coordinateEvaluation_injective W)

lemma finite_irreducibleAffine_dimension_zero {K : Type} [Field K] {n : ℕ}
    (W : Set (Affine K n)) (hirr : IrreducibleAffine W) (hW : W.Finite) :
    ringKrullDim (CoordinateRing W) = 0 := by
  letI : (vanishingIdeal K W).IsPrime := irreducibleAffine_ideal_prime hirr
  letI : Module.Finite K (CoordinateRing W) := finiteAffineSet_module_finite W hW
  have hh := integral_dimension_eq (R := K) (S := CoordinateRing W)
    (algebraMap K (CoordinateRing W)).injective
  rw [ringKrullDim_eq_zero_of_field] at hh
  exact hh.symm

end APSCounting893.Main
end Component_28

section Component_29

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma square_system_component_dimension_positive
    {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (p : Fin n → Polynomials K (n+1))
    (W : Set (Affine K (n+1)))
    (hW : AffineComponent (zeroLocus K (Ideal.span (Set.range p))) W) :
    ¬ ringKrullDim (CoordinateRing W) ≤ 0 := by
  classical
  let s := Finset.univ.image p
  have hmin := affineComponent_ideal_minimal (isAlgSet_zeroLocus (Ideal.span (Set.range p))) hW
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmin
  have hm : vanishingIdeal K W ∈ (Ideal.span (Set.range p)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes]
    exact hmin
  have hspan : Ideal.span (Set.range p) = Ideal.span (s : Set (Polynomials K (n+1))) := by
    congr 1
    ext a
    simp [s]
  rw [hspan] at hm
  have hheight := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hm
  have hcard : s.card ≤ n := by
    exact (Finset.card_image_le).trans (by simp)
  have hh : (vanishingIdeal K W).height ≤ (n : ℕ∞) := hheight.trans (by exact_mod_cast hcard)
  intro hdim
  have hd := DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le
    (vanishingIdeal K W) (irreducibleAffine_ideal_prime hW.1) 0 hdim
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_zero, add_zero] at hd
  have hbad : (n+1 : ℕ) ≤ n := by exact_mod_cast hd.trans hh
  omega

lemma isolated_fiber_series_lift
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (p : Fin n → Polynomials K (n+1))
    (hfinite : {x : Affine K (n+1) | (∀ i, eval x (p i) = 0) ∧ x 0 = 0}.Finite)
    (z : Affine K (n+1)) (hz : ∀ i, eval z (p i) = 0) (hz0 : z 0 = 0) :
    ∃ q : Fin (n+1) → HahnSeries ℚ K,
      q 0 = HahnSeries.single (1 : ℚ) (1 : K) ∧
      (∀ j, GenericSeries.IsPuiseuxOver (q j) ∧ 0 ≤ (q j).orderTop ∧ (q j).coeff 0 = z j) ∧
      (∀ i, MvPolynomial.eval₂ HahnSeries.C q (p i) = 0) := by
  classical
  let I := Ideal.span (Set.range p)
  have hzI : z ∈ zeroLocus K I := by
    rw [MvPolynomial.zeroLocus_span]
    rintro f ⟨i, rfl⟩
    exact hz i
  obtain ⟨W, hW, hzW⟩ := exists_affineComponent_mem (isAlgSet_zeroLocus I) hzI
  have hpos := square_system_component_dimension_positive p W hW
  have hnonvertical : ∃ x ∈ W, x 0 ≠ 0 := by
    by_contra h
    push_neg at h
    have hwfinite : W.Finite := hfinite.subset (by
      intro x hx
      refine ⟨?_, h x hx⟩
      intro i
      exact (hW.2.1 hx) (p i) (Ideal.subset_span ⟨i, rfl⟩))
    exact hpos (finite_irreducibleAffine_dimension_zero W hW.1 hwfinite |>.le)
  obtain ⟨z', hz'W, hz'0⟩ := hnonvertical
  letI : (vanishingIdeal K W).IsPrime := irreducibleAffine_ideal_prime hW.1
  let psi : CoordinateRing W →ₐ[K] K := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval z)
    (fun f hf => hf z hzW)
  let psi' : CoordinateRing W →ₐ[K] K := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval z')
    (fun f hf => hf z' hz'W)
  have hp0 : psi (coordinate W 0) = 0 := by simpa [psi, coordinate] using hz0
  have hp1 : psi' (coordinate W 0) ≠ 0 := by simpa [psi', coordinate] using hz'0
  obtain ⟨rho, ht, hres⟩ := GenericSeries.two_point_series_arc psi psi' (coordinate W 0) hp0 hp1
  let q : Fin (n+1) → HahnSeries ℚ K := fun j => rho (coordinate W j)
  refine ⟨q, ht, ?_, ?_⟩
  · intro j
    have hh := hres (coordinate W j)
    simpa [q, psi, coordinate] using hh
  · intro i
    have hmem : p i ∈ vanishingIdeal K W := by
      intro x hx
      exact (hW.2.1 hx) (p i) (Ideal.subset_span ⟨i, rfl⟩)
    have hh : Ideal.Quotient.mk (vanishingIdeal K W) (p i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have heval : MvPolynomial.eval₂Hom HahnSeries.C q =
        rho.toRingHom.comp (Ideal.Quotient.mk (vanishingIdeal K W)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
        change HahnSeries.C c = rho (algebraMap K (CoordinateRing W) c)
        rw [rho.commutes]
        simp [HahnSeries.algebraMap_apply']
      · intro j
        change MvPolynomial.eval₂ HahnSeries.C q (MvPolynomial.X j) =
          rho (Ideal.Quotient.mk (vanishingIdeal K W) (MvPolynomial.X j))
        rw [MvPolynomial.eval₂_X]
        rfl
    change MvPolynomial.eval₂Hom HahnSeries.C q (p i) = 0
    rw [heval, RingHom.comp_apply, hh, map_zero]

end APSCounting893.Main
end Component_29

section Component_30

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma monomial_perturbation_lift
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (f : Fin n → Polynomials K n) (degrees : Fin n → ℕ)
    (hfinite : {x : Affine K n | ∀ i, eval x (f i) = 0}.Finite)
    (z : Affine K n) (hz : ∀ i, eval z (f i) = 0) :
    ∃ q : Fin n → HahnSeries ℚ K,
      (∀ j, GenericSeries.IsPuiseuxOver (q j) ∧ 0 ≤ (q j).orderTop ∧ (q j).coeff 0 = z j) ∧
      (∀ i, MvPolynomial.eval₂ HahnSeries.C q (f i) +
        HahnSeries.single (1 : ℚ) (1 : K) * q i ^ degrees i = 0) := by
  classical
  let p : Fin n → Polynomials K (n+1) := fun i =>
    MvPolynomial.rename Fin.succ (f i) + MvPolynomial.X 0 * MvPolynomial.X i.succ ^ degrees i
  have hfiber : {x : Affine K (n+1) | (∀ i, eval x (p i) = 0) ∧ x 0 = 0}.Finite := by
    apply (hfinite.image (Fin.cons 0)).subset
    intro x hx
    have hxt : (fun j => x j.succ) ∈ {u : Affine K n | ∀ i, eval u (f i) = 0} := by
      intro i
      simpa [p, MvPolynomial.eval_rename, Function.comp_def, hx.2] using hx.1 i
    refine ⟨(fun j => x j.succ), hxt, ?_⟩
    funext j
    exact Fin.cases hx.2.symm (fun i => by simp) j
  have hz' : ∀ i, eval (Fin.cons 0 z) (p i) = 0 := by
    intro i
    simpa [p, MvPolynomial.eval_rename] using hz i
  obtain ⟨q, hq0, hq, hroot⟩ := isolated_fiber_series_lift p hfiber (Fin.cons 0 z) hz' (by simp)
  refine ⟨(fun j => q j.succ), ?_, ?_⟩
  · intro j
    simpa using hq j.succ
  · intro i
    simpa [p, MvPolynomial.eval₂_rename, Function.comp_def, hq0] using hroot i

end APSCounting893.Main
end Component_30

section Component_31

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_31

section Component_32

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_32

section Component_33

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonRegular : nonnegativeHahnRing PuiseuxAmbient :=
  Classical.choose (hahnResidue_single_one (K := PuiseuxAmbient))

lemma epsilonRegular_val : epsilonRegular.val = HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient) :=
  (Classical.choose_spec (hahnResidue_single_one (K := PuiseuxAmbient))).1

lemma epsilonRegular_residue : hahnResidueHom PuiseuxAmbient epsilonRegular = 0 :=
  (Classical.choose_spec (hahnResidue_single_one (K := PuiseuxAmbient))).2

noncomputable def epsilonAuxHom : Aux →+* EpsilonAmbient :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp HahnSeries.C)
    (fun v : Fin 4 => if v = 0 then HahnSeries.single (1 : ℚ) 1
      else if v = 2 then HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)

noncomputable def epsilonAuxLift : Aux →+* nonnegativeHahnRing PuiseuxAmbient :=
  MvPolynomial.eval₂Hom ((hahnConstantLift PuiseuxAmbient).comp HahnSeries.C)
    (fun v : Fin 4 => if v = 0 then epsilonRegular
      else if v = 2 then hahnConstantLift PuiseuxAmbient (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)

lemma epsilonAuxLift_underlying :
    (nonnegativeHahnRing PuiseuxAmbient).subtype.comp epsilonAuxLift = epsilonAuxHom := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [epsilonAuxLift, epsilonAuxHom, hahnConstantLift]
  · intro v
    fin_cases v <;> simp [epsilonAuxLift, epsilonAuxHom, hahnConstantLift, epsilonRegular_val]

lemma epsilonAuxLift_residue :
    (hahnResidueHom PuiseuxAmbient).comp epsilonAuxLift = tAuxHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [epsilonAuxLift, tAuxHom, hahnResidue_constant]
  · intro v
    fin_cases v <;> simp [epsilonAuxLift, tAuxHom, hahnResidue_constant, epsilonRegular_residue]

lemma epsilon_specialization_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (q : Fin (F.n + (F.n + 1) + 1) → EpsilonAmbient)
    (hq : ∀ j, 0 ≤ (q j).orderTop)
    (hroot : ∀ i, MvPolynomial.eval₂ epsilonAuxHom q (perturbedEquation F c alpha degrees i) = 0) :
    ∀ i, MvPolynomial.eval₂ tAuxHom (fun j => (q j).coeff 0) (homogenizedEquation F c alpha degrees i) = 0 := by
  let qlift : Fin (F.n + (F.n + 1) + 1) → nonnegativeHahnRing PuiseuxAmbient := fun j => ⟨q j, hq j⟩
  intro i
  have hlift : MvPolynomial.eval₂ epsilonAuxLift qlift (perturbedEquation F c alpha degrees i) = 0 := by
    apply Subtype.val_injective
    change (nonnegativeHahnRing PuiseuxAmbient).subtype
      (MvPolynomial.eval₂ epsilonAuxLift qlift (perturbedEquation F c alpha degrees i)) = 0
    rw [MvPolynomial.hom_eval₂, epsilonAuxLift_underlying]
    exact hroot i
  have h := congrArg (hahnResidueHom PuiseuxAmbient) hlift
  rw [MvPolynomial.hom_eval₂, map_zero, epsilonAuxLift_residue] at h
  change MvPolynomial.eval₂ tAuxHom (fun j => (q j).coeff 0) (perturbedEquation F c alpha degrees i) = 0 at h
  simpa [perturbedEquation, tAuxHom] using h

lemma epsilon_limit_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F c alpha degrees)
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F c alpha degrees) :
    z ≠ 0 ∧ ∀ i, MvPolynomial.eval₂ tAuxHom z (homogenizedEquation F c alpha degrees i) = 0 := by
  obtain ⟨q, hq, hmin, hroot, hz⟩ := hz
  have hq0 : (fun j => (q j).coeff 0) ≠ 0 := by
    obtain ⟨j, hj⟩ := hmin
    intro h
    have hh := congrFun h j
    exact HahnSeries.coeff_orderTop_ne hj hh
  have heq := epsilon_specialization_homogeneous F c alpha degrees q (fun j => (hq j).2) hroot
  rw [hz]
  refine ⟨projectiveRepresentative_ne_zero _ hq0, ?_⟩
  intro i
  apply homogeneous_root_projectiveRepresentative (homogenizedEquation F c alpha degrees i) (degrees i)
    (homogenizeAll_homogeneous _ _ (hdegrees i).2.2) tAuxHom _ hq0 (heq i)

end APSCounting893.Main
end Component_33

section Component_34

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma epsilonAux_polynomial_coefficients (p : Polynomial ℂ) :
    epsilonAuxHom ((Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) p) =
      HahnSeries.C (tCoefficientHom p) := by
  have hh : epsilonAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      (HahnSeries.C : PuiseuxAmbient →+* EpsilonAmbient).comp tCoefficientHom := by
    apply Polynomial.ringHom_ext (R := ℂ) (S := EpsilonAmbient)
    · intro c
      simp [epsilonAuxHom, tCoefficientHom]
    · simp [epsilonAuxHom, tCoefficientHom]
  exact RingHom.congr_fun hh p

lemma epsilon_equationWithAux_eval (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) (q : Fin (F.n + (F.n + 1)) → EpsilonAmbient) :
    MvPolynomial.eval₂ epsilonAuxHom q (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ HahnSeries.C q (MvPolynomial.map tAuxHom (equationWithAux F c alpha i)) := by
  rw [MvPolynomial.eval₂_map, equationWithAux, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map]
  congr 1
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply]
  rw [epsilonAux_polynomial_coefficients, tAux_polynomial_coefficients]

lemma affine_root_mem_epsilonLimitSet
    (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F c alpha degrees)
    (hfinite : {x : Affine PuiseuxAmbient (F.n + (F.n + 1)) |
      ∀ i, MvPolynomial.eval₂ tAuxHom x (equationWithAux F c alpha i) = 0}.Finite)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1)))
    (hz : ∀ i, MvPolynomial.eval₂ tAuxHom z (equationWithAux F c alpha i) = 0) :
    projectiveRepresentative (Fin.cons 1 z) ∈ epsilonLimitSet F c alpha degrees := by
  classical
  letI : IsAlgClosed PuiseuxAmbient := HahnSeries.isAlgClosed_rat
  letI : CharZero PuiseuxAmbient := charZero_of_injective_ringHom (HahnSeries.C : ℂ →+* PuiseuxAmbient).injective
  let f := fun i => MvPolynomial.map tAuxHom (equationWithAux F c alpha i)
  have hf : {x : Affine PuiseuxAmbient (F.n + (F.n + 1)) | ∀ i, eval x (f i) = 0}.Finite := by
    simpa only [f, MvPolynomial.eval_map] using hfinite
  have hz' : ∀ i, eval z (f i) = 0 := by
    simpa only [f, MvPolynomial.eval_map] using hz
  obtain ⟨q, hq, hroot⟩ := monomial_perturbation_lift f degrees hf z hz'
  let Q : Fin (F.n + (F.n + 1) + 1) → EpsilonAmbient := Fin.cons 1 q
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ⟨(hq i).1, (hq i).2.1⟩) j
    refine ⟨⟨1, by decide, ?_⟩, ?_⟩
    · exact Subfield.one_mem _
    · change 0 ≤ (1 : EpsilonAmbient).orderTop
      simp
  · refine ⟨0, ?_⟩
    change (1 : EpsilonAmbient).orderTop = 0
    simp
  · intro i
    change MvPolynomial.eval₂ epsilonAuxHom Q (perturbedEquation F c alpha degrees i) = 0
    have hh := eval_homogenize_scaled epsilonAuxHom (equationWithAux F c alpha i) (degrees i)
      (hdegrees i).2.2 1 q
    have hhom : MvPolynomial.eval₂ epsilonAuxHom Q (homogenizedEquation F c alpha degrees i) =
        MvPolynomial.eval₂ epsilonAuxHom q (equationWithAux F c alpha i) := by
      have heq : Fin.cases (1 : EpsilonAmbient) (fun j => 1 * q j) = Q := by
        funext j
        refine Fin.cases (by simp only [Fin.cases_zero, Q, Fin.cons_zero]) (fun j => ?_) j
        simp only [Fin.cases_succ, Q, Fin.cons_succ]
        exact one_mul (q j)
      rw [heq, one_pow, one_mul] at hh
      exact hh
    rw [perturbedEquation, MvPolynomial.eval₂_add, hhom, epsilon_equationWithAux_eval]
    have hri := hroot i
    simpa [Q, epsilonAuxHom, f] using hri
  · congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [Q]
    · exact (hq i).2.2.symm

end APSCounting893.Main
end Component_34

section Component_35

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma projectiveRepresentative_affine {K : Type} [Field K] {n : ℕ}
    (z : Fin (n+1) → K) (hz : z 0 ≠ 0) :
    projectiveRepresentative z = fun j => z j / z 0 := by
  classical
  let S := Finset.univ.filter (fun j : Fin (n+1) => z j ≠ 0)
  have h0 : 0 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  have hS : S.Nonempty := ⟨0, h0⟩
  have hmin : S.min' hS = 0 := le_antisymm (Finset.min'_le S 0 h0) (Fin.zero_le _)
  rw [projectiveRepresentative, dif_pos hS]
  change (fun j => z j / z (S.min' hS)) = _
  rw [hmin]

lemma projectiveRepresentative_cons_one {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) : projectiveRepresentative (Fin.cons 1 z) = Fin.cons 1 z := by
  rw [projectiveRepresentative_affine _ (by simp)]
  funext j
  simp

end APSCounting893.Main
end Component_35

section Component_36

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma raw_aux_equations_iff (F : RawMap) (c alpha : Affine ℂ F.n)
    (z : Affine PuiseuxAmbient (F.n + (F.n+1))) :
    (∀ i, MvPolynomial.eval₂ tAuxHom z (equationWithAux F c alpha i) = 0) ↔
      (∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F c alpha i) = 0) := by
  constructor
  · intro h j
    have hh := h (Fin.cast (Nat.add_comm _ _) j)
    rw [equationWithAux_specializes] at hh
    simpa using hh
  · intro h i
    rw [equationWithAux_specializes]
    exact h _

lemma raw_aux_points_finite (F : ReducedMap) (D : LineData F) :
    {z : Affine PuiseuxAmbient (F.n + (F.n+1)) |
      ∀ i, MvPolynomial.eval₂ tAuxHom z (equationWithAux F D.c D.alpha i) = 0}.Finite := by
  have heq : {z : Affine PuiseuxAmbient (F.n + (F.n+1)) |
      ∀ i, MvPolynomial.eval₂ tAuxHom z (equationWithAux F D.c D.alpha i) = 0} =
      {z : Affine PuiseuxAmbient (F.n + (F.n+1)) |
      ∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0} := by
    ext z
    exact raw_aux_equations_iff F D.c D.alpha z
  rw [heq]
  exact raw_line_points_finite F D

lemma epsilon_affine_point_lineSolution (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F D.c D.alpha degrees) (hz0 : z 0 ≠ 0) :
    (fun j => z j.succ / z 0) ∈ lineSolutions F D := by
  have hh := (epsilon_limit_homogeneous F D.c D.alpha degrees hdegrees z hz).2
  apply raw_line_point_puiseux
  apply (raw_aux_equations_iff F D.c D.alpha _).mp
  intro i
  have h := hh i
  rw [homogenizedEquation, eval_homogenize_dehomogenize tAuxHom _ _ (hdegrees i).2.2 z hz0] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hz0)

lemma lineSolution_mem_epsilonLimitSet (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (z : Affine PuiseuxAmbient (F.n + (F.n+1))) (hz : z ∈ lineSolutions F D) :
    Fin.cons 1 z ∈ epsilonLimitSet F D.c D.alpha degrees := by
  rw [← projectiveRepresentative_cons_one z]
  apply affine_root_mem_epsilonLimitSet F D.c D.alpha degrees hdegrees (raw_aux_points_finite F D)
  apply (raw_aux_equations_iff F D.c D.alpha z).mpr
  apply (affineLineEquations_iff F D z).mpr
  exact ⟨hz.2.1, hz.2.2⟩

end APSCounting893.Main
end Component_36

section Component_37

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonAffineOutput (F : RawMap)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient) : Affine PuiseuxAmbient (F.n+1) :=
  fun j => z (j.natAdd F.n).succ / z 0

lemma epsilon_affine_output_integral (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F D.c D.alpha degrees) (hz0 : z 0 ≠ 0) :
    (∀ j, PuiseuxIntegral (epsilonAffineOutput F z j)) ∧
      (fun j => residue (epsilonAffineOutput F z j)) ∈ zeroFiber F D.c := by
  exact (zero_fiber_residues F D).1 _
    (epsilon_affine_point_lineSolution F D degrees hdegrees z hz hz0)

lemma epsilon_affine_output_residues_cover (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    {y : Affine ℂ (F.n+1) | ∃ z ∈ epsilonLimitSet F D.c D.alpha degrees,
      z 0 ≠ 0 ∧ (fun j => residue (epsilonAffineOutput F z j)) = y} = zeroFiber F D.c := by
  ext y
  constructor
  · rintro ⟨z, hz, hz0, rfl⟩
    exact (epsilon_affine_output_integral F D degrees hdegrees z hz hz0).2
  · intro hy
    obtain ⟨z, hz, hres⟩ := (zero_fiber_residues F D).2 y hy
    refine ⟨Fin.cons 1 z, lineSolution_mem_epsilonLimitSet F D degrees hdegrees z hz, by simp, ?_⟩
    change (fun j => residue (z (j.natAdd F.n))) = y at hres
    simpa only [epsilonAffineOutput, Fin.cons_zero, Fin.cons_succ, div_one] using hres

lemma epsilonAffineOutput_rescale (F : RawMap)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient) (a : PuiseuxAmbient) (ha : a ≠ 0) :
    epsilonAffineOutput F (a • z) = epsilonAffineOutput F z := by
  funext j
  simp only [epsilonAffineOutput, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ ha

end APSCounting893.Main
end Component_37

open APSCounting893.Main
theorem solution
    (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    (∀ z ∈ epsilonLimitSet F D.c D.alpha degrees, z 0 ≠ 0 →
      (∀ j : Fin (F.n+1), PuiseuxIntegral (z (j.natAdd F.n).succ / z 0)) ∧
        outputResidue F (fun j => z j.succ / z 0) ∈ zeroFiber F D.c) ∧
    (∀ y ∈ zeroFiber F D.c, ∃ z ∈ epsilonLimitSet F D.c D.alpha degrees,
      z 0 ≠ 0 ∧ outputResidue F (fun j => z j.succ / z 0) = y) := by
  refine ⟨?_, ?_⟩
  · intro z hz hz0
    exact epsilon_affine_output_integral F D degrees hdegrees z hz hz0
  · intro y hy
    have hh : y ∈ {y : Affine ℂ (F.n+1) | ∃ z ∈ epsilonLimitSet F D.c D.alpha degrees,
      z 0 ≠ 0 ∧ (fun j => residue (epsilonAffineOutput F z j)) = y} := by
      rw [epsilon_affine_output_residues_cover F D degrees hdegrees]
      exact hy
    exact hh
