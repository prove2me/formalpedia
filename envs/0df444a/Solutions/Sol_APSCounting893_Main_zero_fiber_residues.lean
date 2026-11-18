-- Prove2me | solution 1 for APSCounting893.Main.zero_fiber_residues
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:50:03.439314+00:00
-- url     : https://prove2.me/submissions/2440ac88-01b1-421d-8bec-da7bfdd2bde3

import Definitions.Def_APSCounting893_Main_Geometry
import Theorems.Thm_HahnSeries_isAlgClosed_rat
import Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Definitions.Def_APSCounting893_Main_LineGeometry
import Theorems.Thm_ValuationSubring_exists_ringHom_comp_eq_of_moduleFinite_of_flat
import Theorems.Thm_APSCounting893_Main_dominant_graph_components

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

lemma residue_polynomial_relation {m : ℕ} (p : Polynomials ℂ m)
    (y : Affine PuiseuxAmbient m) (hy : ∀ i, 0 ≤ (y i).orderTop)
    (hrel : MvPolynomial.eval₂ HahnSeries.C y p = 0) :
    MvPolynomial.eval (fun i => (y i).coeff 0) p = 0 := by
  let z : Fin m → seriesValuationRing := fun i => ⟨y i, hy i⟩
  have hz : MvPolynomial.eval₂ constantSeriesHom z p = 0 := by
    apply Subtype.val_injective
    change seriesValuationRing.subtype (MvPolynomial.eval₂ constantSeriesHom z p) = 0
    rw [MvPolynomial.hom_eval₂]
    exact hrel
  have h := congrArg seriesResidueHom hz
  rw [MvPolynomial.hom_eval₂, map_zero] at h
  have hc : seriesResidueHom.comp constantSeriesHom = RingHom.id ℂ := by
    ext c
    exact seriesResidue_constant c
  rw [hc] at h
  exact h

lemma series_eval_substitution {n m : ℕ} (F : PolynomialMap ℂ n m)
    (p : Polynomials ℂ m) (x : Affine PuiseuxAmbient n) :
    MvPolynomial.eval₂ HahnSeries.C x (eval₂Hom MvPolynomial.C F p) =
      MvPolynomial.eval₂ HahnSeries.C (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) p := by
  have heq : (MvPolynomial.eval₂Hom HahnSeries.C x).comp (eval₂Hom MvPolynomial.C F) =
      MvPolynomial.eval₂Hom HahnSeries.C (fun j => MvPolynomial.eval₂ HahnSeries.C x (F j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  exact RingHom.congr_fun heq p

lemma residue_output_mem_imageClosure {n m : ℕ} (F : PolynomialMap ℂ n m)
    (x : Affine PuiseuxAmbient n) (y : Affine PuiseuxAmbient m)
    (hy : ∀ j, y j = MvPolynomial.eval₂ HahnSeries.C x (F j))
    (horder : ∀ j, 0 ≤ (y j).orderTop) :
    (fun j => (y j).coeff 0) ∈ imageClosure F := by
  intro p hp
  have hpker : eval₂Hom MvPolynomial.C F p = 0 := by
    rw [image_vanishingIdeal_eq_kernel] at hp
    exact hp
  have hrel : MvPolynomial.eval₂ HahnSeries.C y p = 0 := by
    have h := congrArg (MvPolynomial.eval₂Hom HahnSeries.C x) hpker
    rw [map_zero] at h
    change MvPolynomial.eval₂ HahnSeries.C x (eval₂Hom MvPolynomial.C F p) = 0 at h
    rw [series_eval_substitution, ← funext hy] at h
    exact h
  simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using
    residue_polynomial_relation p y horder hrel

lemma series_polynomial_nonnegative {m : ℕ} (p : Polynomials ℂ m)
    (y : Affine PuiseuxAmbient m) (hy : ∀ i, 0 ≤ (y i).orderTop) :
    0 ≤ (MvPolynomial.eval₂ HahnSeries.C y p).orderTop := by
  let z : Fin m → seriesValuationRing := fun i => ⟨y i, hy i⟩
  let r := MvPolynomial.eval₂ constantSeriesHom z p
  have heq : r.val = MvPolynomial.eval₂ HahnSeries.C y p := by
    change seriesValuationRing.subtype (MvPolynomial.eval₂ constantSeriesHom z p) = _
    rw [MvPolynomial.hom_eval₂]
    rfl
  rw [← heq]
  exact r.property

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

lemma lineSolution_output_integral (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) (hz : z ∈ lineSolutions F D) :
    ∀ j : Fin (F.n + 1), PuiseuxIntegral (z (j.natAdd F.n)) := by
  classical
  let x : Affine PuiseuxAmbient F.n := fun i => z (i.castAdd (F.n + 1))
  let y : Affine PuiseuxAmbient (F.n + 1) := fun j => z (j.natAdd F.n)
  have hy : ∀ j, y j = MvPolynomial.eval₂ HahnSeries.C x (F.F j) := hz.2.1
  let v : Affine PuiseuxAmbient F.n := fun j => HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)
  have hv (j : Fin F.n) : 0 ≤ (v j).orderTop := by
    dsimp only [v]
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp only [zero_add, mul_one]
    exact (show (0 : WithTop ℚ) ≤ 1 by norm_num).trans HahnSeries.orderTop_single_le
  have hnorm (j : Fin F.n) : MvPolynomial.eval₂ HahnSeries.C y (normalizationPolynomials D.c j) = v j := by
    change (MvPolynomial.eval₂Hom HahnSeries.C y)
      (MvPolynomial.X j.castSucc - MvPolynomial.C (D.c j) * MvPolynomial.X (Fin.last F.n)) = v j
    simp only [map_sub, map_mul, eval₂Hom_X', eval₂Hom_C]
    exact hz.2.2 j
  intro j
  refine ⟨hz.1 _, ?_⟩
  obtain ⟨d, hd, A, hA⟩ := D.normalization.2.2.2 j
  let Q : Polynomials ℂ (F.n + 1) := MvPolynomial.X j ^ d + ∑ i : Fin d,
    eval₂Hom MvPolynomial.C (normalizationPolynomials D.c) (A i) * MvPolynomial.X j ^ i.val
  have hQI : Q ∈ vanishingIdeal ℂ (imageClosure F.F) := by
    intro w hw
    simpa only [Q, aeval_def, Algebra.algebraMap_self, eval₂_id, map_add, map_sum, map_mul,
      map_pow, eval_X, evaluation_substitution] using hA w hw
  have hQker : eval₂Hom MvPolynomial.C F.F Q = 0 := by
    have hI : Q ∈ vanishingIdeal ℂ (Set.range (evaluate F.F)) := by
      simpa only [imageClosure, vanishingIdeal_zClosure] using hQI
    rw [image_vanishingIdeal_eq_kernel] at hI
    exact hI
  have hseries := congrArg (MvPolynomial.eval₂Hom HahnSeries.C x) hQker
  rw [map_zero] at hseries
  change MvPolynomial.eval₂ HahnSeries.C x (eval₂Hom MvPolynomial.C F.F Q) = 0 at hseries
  rw [series_eval_substitution, ← funext hy] at hseries
  let a : Fin d → PuiseuxAmbient := fun i => MvPolynomial.eval₂ HahnSeries.C v (A i)
  have hcoeff (i : Fin d) : (MvPolynomial.eval₂Hom HahnSeries.C y)
      (eval₂Hom MvPolynomial.C (normalizationPolynomials D.c) (A i)) = a i := by
    change MvPolynomial.eval₂ HahnSeries.C y (eval₂Hom MvPolynomial.C (normalizationPolynomials D.c) (A i)) = a i
    rw [series_eval_substitution, funext hnorm]
  have heq : y j ^ d + ∑ i : Fin d, a i * y j ^ i.val = 0 := by
    change (MvPolynomial.eval₂Hom HahnSeries.C y) Q = 0 at hseries
    simpa only [Q, map_add, map_sum, map_mul, map_pow, eval₂Hom_X', hcoeff] using hseries
  let av : Fin d → seriesValuationRing := fun i => ⟨a i, series_polynomial_nonnegative (A i) v hv⟩
  let qv : Polynomial seriesValuationRing := Polynomial.X ^ d + ∑ i : Fin d,
    Polynomial.C (av i) * Polynomial.X ^ i.val
  let q := qv.map seriesValuationRing.subtype
  apply orderTop_nonnegative_of_monic_root (y j) q
  · exact (monic_from_relation av).map _
  · intro i
    change 0 ≤ (q.coeff i).orderTop
    dsimp only [q]
    rw [Polynomial.coeff_map]
    exact (qv.coeff i).property
  · simpa [q, qv, Polynomial.map_sum, Polynomial.eval_finsetSum, av] using heq

lemma lineSolution_residue_zeroFiber (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) (hz : z ∈ lineSolutions F D) :
    outputResidue F z ∈ zeroFiber F D.c := by
  have hint := lineSolution_output_integral F D z hz
  constructor
  · exact residue_output_mem_imageClosure F.F
      (fun i => z (i.castAdd (F.n + 1))) (fun j => z (j.natAdd F.n)) hz.2.1
      (fun j => (hint j).2)
  · funext j
    have h := congrArg (fun s : PuiseuxAmbient => s.coeff 0) (hz.2.2 j)
    simpa [normalization, evaluate, normalizationPolynomials, outputResidue, residue,
      HahnSeries.C_apply, HahnSeries.single_zero_mul_eq_smul] using h

lemma zero_fiber_residues_forward (F : ReducedMap) (D : LineData F) :
    ∀ z ∈ lineSolutions F D,
      (∀ j : Fin (F.n + 1), PuiseuxIntegral (z (j.natAdd F.n))) ∧
        outputResidue F z ∈ zeroFiber F D.c := by
  intro z hz
  exact ⟨lineSolution_output_integral F D z hz, lineSolution_residue_zeroFiber F D z hz⟩

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
open MvPolynomial HahnSeries
open scoped RatFunc LaurentSeries
namespace APSCounting893.Main

lemma coordinate_branch_embedding (E : Type) [Field E] [Algebra ℂ E]
    [Algebra (RatFunc ℂ) E] [IsScalarTower ℂ (RatFunc ℂ) E]
    [Algebra.IsAlgebraic (RatFunc ℂ) E]
    [Algebra (Polynomial ℂ) E] [IsScalarTower ℂ (Polynomial ℂ) E]
    [IsScalarTower (Polynomial ℂ) (RatFunc ℂ) E]
    {m : ℕ} (v : Fin m → E) (y : Affine ℂ m)
    (τ : Polynomials ℂ m)
    (hτ : MvPolynomial.aeval v τ =
      algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X))
    (hyτ : eval y τ = 0)
    (hv : ∀ j, IsIntegral (Polynomial ℂ) (v j))
    (hker : RingHom.ker (MvPolynomial.aeval v).toRingHom ≤ RingHom.ker (MvPolynomial.eval y)) :
    ∃ ρ : E →ₐ[ℂ] PuiseuxAmbient,
      ρ (algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
        HahnSeries.single (1 : ℚ) (1 : ℂ) ∧
      (∀ j, PuiseuxIntegral (ρ (v j)) ∧ (ρ (v j)).coeff 0 = y j) ∧
      ∀ x : E, IsPuiseux (ρ x) := by
  classical
  let f : Polynomials ℂ m →ₐ[ℂ] E := MvPolynomial.aeval v
  let A := f.range
  let tA : A := f.rangeRestrict τ
  let pA : Polynomial ℂ →+* A := Polynomial.eval₂RingHom (algebraMap ℂ A) tA
  letI : Algebra (Polynomial ℂ) A := pA.toAlgebra
  letI : IsScalarTower ℂ (Polynomial ℂ) A := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap ℂ A c = pA (Polynomial.C c)
    simp [pA])
  have htA : (tA : E) =
      algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) := hτ
  letI : IsScalarTower (Polynomial ℂ) A E := IsScalarTower.of_algebraMap_eq' (by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      change algebraMap (Polynomial ℂ) E (algebraMap ℂ (Polynomial ℂ) c) = _
      rw [← IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) E]
      change algebraMap ℂ E c = (pA (Polynomial.C c)).val
      simp [pA]
    · change algebraMap (Polynomial ℂ) E Polynomial.X = (pA Polynomial.X).val
      simp only [pA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rw [IsScalarTower.algebraMap_apply (Polynomial ℂ) (RatFunc ℂ) E]
      exact htA.symm)
  have hpAinj : Function.Injective (algebraMap (Polynomial ℂ) A) := by
    have h := (algebraMap (RatFunc ℂ) E).injective.comp
      (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ))
    intro p q hpq
    apply h
    change algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) q)
    rw [← IsScalarTower.algebraMap_apply (Polynomial ℂ) (RatFunc ℂ) E,
      ← IsScalarTower.algebraMap_apply (Polynomial ℂ) (RatFunc ℂ) E,
      IsScalarTower.algebraMap_apply (Polynomial ℂ) A E,
      IsScalarTower.algebraMap_apply (Polynomial ℂ) A E]
    exact congrArg (algebraMap A E) hpq
  letI : Module.IsTorsionFree (Polynomial ℂ) A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hpAinj
  let u : Fin m → A := fun j => f.rangeRestrict (MvPolynomial.X j)
  have hu (j : Fin m) : (u j : E) = v j := by simp [u, f]
  have hadjoin : Algebra.adjoin (Polynomial ℂ) (Set.range u) = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨p, hp⟩ := a.property
    have hh (p : Polynomials ℂ m) : f.rangeRestrict p ∈ Algebra.adjoin (Polynomial ℂ) (Set.range u) := by
      induction p using MvPolynomial.induction_on with
      | C c =>
          have heq : f.rangeRestrict (MvPolynomial.C c) = algebraMap (Polynomial ℂ) A (Polynomial.C c) := by
            apply Subtype.ext
            change f (MvPolynomial.C c) = (pA (Polynomial.C c)).val
            simp [f, pA]
          rw [heq]
          exact (Algebra.adjoin (Polynomial ℂ) (Set.range u)).algebraMap_mem _
      | add p q hp hq => simpa only [map_add] using (Algebra.adjoin (Polynomial ℂ) (Set.range u)).add_mem hp hq
      | mul_X p j hp =>
          simpa only [map_mul] using (Algebra.adjoin (Polynomial ℂ) (Set.range u)).mul_mem hp
            (Algebra.subset_adjoin ⟨j, rfl⟩)
    have heq : f.rangeRestrict p = a := Subtype.ext hp
    rw [← heq]
    exact hh p
  have hui (j : Fin m) : IsIntegral (Polynomial ℂ) (u j) := by
    let incl : A →ₐ[Polynomial ℂ] E := IsScalarTower.toAlgHom (Polynomial ℂ) A E
    apply (isIntegral_algHom_iff incl Subtype.val_injective).mp
    change IsIntegral (Polynomial ℂ) ((u j : A) : E)
    rw [hu]
    exact hv j
  have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range u)
    (by rintro z ⟨j, rfl⟩; exact hui j)
  rw [hadjoin] at hfin
  letI := hfin
  letI : Module.Finite (Polynomial ℂ) A := Module.Finite.of_surjective
    (Subalgebra.topEquiv.toLinearMap : (⊤ : Subalgebra (Polynomial ℂ) A) →ₗ[Polynomial ℂ] A)
    Subalgebra.topEquiv.surjective
  letI : Module.Flat (Polynomial ℂ) A := inferInstance
  let ψ : A →ₐ[ℂ] ℂ := AlgHom.liftOfSurjective f.rangeRestrict f.rangeRestrict_surjective
    (MvPolynomial.aeval y) (by
      intro p hp
      apply hker
      exact congrArg Subtype.val hp)
  have hψ (p : Polynomials ℂ m) : ψ (f.rangeRestrict p) = eval y p := by
    simpa only [ψ, MvPolynomial.aeval_def, Algebra.algebraMap_self, eval₂_id] using
      AlgHom.liftOfSurjective_apply f.rangeRestrict f.rangeRestrict_surjective
        (MvPolynomial.aeval y) (show RingHom.ker f.rangeRestrict.toRingHom ≤
          RingHom.ker (MvPolynomial.aeval y).toRingHom from by
            intro p hp; exact hker (congrArg Subtype.val hp)) p
  have hψcomp : ψ.toRingHom.comp (algebraMap (Polynomial ℂ) A) = Polynomial.evalRingHom (0 : ℂ) := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      change ψ (pA (Polynomial.C c)) = c
      simpa only [pA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Algebra.algebraMap_self, RingHom.id_apply] using ψ.commutes c
    · simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      change ψ (pA Polynomial.X) = 0
      simpa only [pA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, tA, hψ] using hyτ
  letI : Algebra.IsAlgebraic (Polynomial ℂ) E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial ℂ) (K := RatFunc ℂ) (C := E)).mpr inferInstance
  letI : Algebra.IsAlgebraic A E := Algebra.IsAlgebraic.extendScalars hpAinj
  obtain ⟨ρ, hρt, hρA⟩ := finite_curve_series_embedding A E ψ.toRingHom hψcomp
  have hρt' : ρ (algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)) =
      HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    change ρ ((pA Polynomial.X).val) = _ at hρt
    simp only [pA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at hρt
    rwa [htA] at hρt
  refine ⟨ρ, hρt', ?_, algebraic_image_puiseux ρ hρt'⟩
  intro j
  have hj := hρA (u j)
  change 0 ≤ (ρ (u j).val).orderTop ∧ (ρ (u j).val).coeff 0 = ψ (u j) at hj
  rw [hu] at hj
  refine ⟨⟨algebraic_image_puiseux ρ hρt' _, hj.1⟩, ?_⟩
  exact hj.2.trans (by simpa [u] using hψ (MvPolynomial.X j))

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
open MvPolynomial HahnSeries
open scoped LaurentSeries RatFunc
namespace APSCounting893.Main

lemma zero_fiber_residues_converse (F : ReducedMap) (D : LineData F)
    (y₀ : Affine ℂ (F.n + 1)) (hy₀ : y₀ ∈ zeroFiber F D.c) :
    ∃ z ∈ lineSolutions F D, outputResidue F z = y₀ := by
  classical
  have hyC : y₀ ∈ {y | y ∈ imageClosure F.F ∧ normalization D.c y ∈ affineLine 0 D.alpha} := by
    refine ⟨hy₀.1, ?_⟩
    rw [hy₀.2]
    exact ⟨0, by simp⟩
  have hyD := closedGraph_image_dense_lineFiber F D hyC
  obtain ⟨W, hW, hyW⟩ := exists_component_imageClosure_mem
    (closedGraphCurve F D.c D.alpha D.U) (isAlgSet_zeroLocus _) F.F y₀ hyD
  obtain ⟨hDomain, a, hTower, hFinite, hβ⟩ := (dominant_graph_components F D W hW).2
  letI : IsDomain (CoordinateRing W) := hDomain
  let E := FractionRing (CoordinateRing W)
  letI : Algebra (RatFunc ℂ) E := a
  letI : IsScalarTower ℂ (RatFunc ℂ) E := hTower
  letI : Module.Finite (RatFunc ℂ) E := hFinite
  letI : Algebra (Polynomial ℂ) E := Algebra.compHom E (algebraMap (Polynomial ℂ) (RatFunc ℂ))
  letI : IsScalarTower (Polynomial ℂ) (RatFunc ℂ) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ℂ (Polynomial ℂ) E := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) E,
      IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ)]
    rfl)
  let x : Fin F.n → E := fun j => algebraMap (CoordinateRing W) E (coordinate W j)
  let v : Fin (F.n + 1) → E := fun j => (MvPolynomial.aeval x) (F.F j)
  let tE := algebraMap (RatFunc ℂ) E (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)
  have hb (j : Fin F.n) : MvPolynomial.aeval x (betaPolynomials F D.c j) =
      algebraMap ℂ E (D.alpha j) * tE := by
    rw [coordinate_aeval_eq]
    exact hβ j
  have hnorm (j : Fin F.n) : MvPolynomial.aeval v (normalizationPolynomials D.c j) =
      algebraMap ℂ E (D.alpha j) * tE := by
    rw [← aeval_substitution]
    exact hb j
  have hv : ∀ j, IsIntegral (Polynomial ℂ) (v j) :=
    output_coordinates_integral F D E x hb
  have hker : RingHom.ker (MvPolynomial.aeval v).toRingHom ≤ RingHom.ker (MvPolynomial.eval y₀) := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    have hq : Ideal.Quotient.mk (vanishingIdeal ℂ W) (eval₂Hom MvPolynomial.C F.F p) = 0 := by
      apply IsFractionRing.injective (CoordinateRing W) E
      rw [map_zero, ← coordinate_aeval_eq, aeval_substitution]
      exact hp
    have hqI := Ideal.Quotient.eq_zero_iff_mem.mp hq
    have hpI : p ∈ vanishingIdeal ℂ (evaluate F.F '' W) := by
      rintro w ⟨z, hz, rfl⟩
      simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, evaluation_substitution] using hqI z hz
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using hyW p hpI
  obtain ⟨k, hk⟩ := Function.ne_iff.mp D.nonzero
  have hk' : D.alpha k ≠ 0 := hk
  let τ : Polynomials ℂ (F.n + 1) := MvPolynomial.C ((D.alpha k)⁻¹) * normalizationPolynomials D.c k
  have hτ : MvPolynomial.aeval v τ = tE := by
    simp only [τ, map_mul, MvPolynomial.aeval_C, hnorm, map_inv₀]
    rw [← mul_assoc, inv_mul_cancel₀ ((map_ne_zero (algebraMap ℂ E)).mpr hk'), one_mul]
  have hyτ : MvPolynomial.eval y₀ τ = 0 := by
    simp only [τ, map_mul, eval_C]
    have heq : eval y₀ (normalizationPolynomials D.c k) = 0 := congrFun hy₀.2 k
    rw [heq, mul_zero]
  obtain ⟨ρ, hρt, hρv, hρall⟩ := coordinate_branch_embedding E v y₀ τ hτ hyτ hv hker
  change ρ tE = _ at hρt
  let z : Affine PuiseuxAmbient (F.n + (F.n + 1)) :=
    Fin.addCases (fun j => ρ (x j)) (fun j => ρ (v j))
  have hzc (j : Fin F.n) : z (j.castAdd (F.n + 1)) = ρ (x j) := by simp [z]
  have hzo (j : Fin (F.n + 1)) : z (j.natAdd F.n) = ρ (v j) := by simp [z]
  have hmap (p : Polynomials ℂ F.n) : ρ ((MvPolynomial.aeval x) p) =
      MvPolynomial.eval₂ HahnSeries.C (fun j => ρ (x j)) p := by
    have heq : ρ.toRingHom.comp (MvPolynomial.aeval x).toRingHom =
        MvPolynomial.eval₂Hom HahnSeries.C (fun j => ρ (x j)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change ρ ((MvPolynomial.aeval x) (MvPolynomial.C c)) = _
        rw [MvPolynomial.aeval_C, ρ.commutes]
        simp only [eval₂Hom_C, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C]
      · intro j
        change ρ ((MvPolynomial.aeval x) (MvPolynomial.X j)) = _
        simp
    exact RingHom.congr_fun heq p
  refine ⟨z, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [hzc] using hρall (x j)
    · simpa only [hzo] using hρall (v j)
  · intro j
    rw [hzo, funext hzc]
    exact hmap (F.F j)
  · intro j
    rw [hzo, hzo]
    have hn := hnorm j
    simp only [normalizationPolynomials, map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C] at hn
    have h := congrArg ρ hn
    simp only [map_sub, map_mul, ρ.commutes, hρt] at h
    simpa only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C] using h
  · funext j
    change (z (j.natAdd F.n)).coeff 0 = y₀ j
    rw [hzo]
    exact (hρv j).2

end APSCounting893.Main

end


open APSCounting893.Main

theorem solution (F : ReducedMap) (D : LineData F) :
    (∀ z ∈ lineSolutions F D,
      (∀ j : Fin (F.n + 1), PuiseuxIntegral (z (j.natAdd F.n))) ∧
        outputResidue F z ∈ zeroFiber F D.c) ∧
    (∀ y ∈ zeroFiber F D.c, ∃ z ∈ lineSolutions F D, outputResidue F z = y) := by
  exact ⟨zero_fiber_residues_forward F D, fun y hy => zero_fiber_residues_converse F D y hy⟩


