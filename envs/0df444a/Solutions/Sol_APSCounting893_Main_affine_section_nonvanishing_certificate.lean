-- Prove2me | solution 1 for APSCounting893.Main.affine_section_nonvanishing_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:13:54.06982+00:00
-- url     : https://prove2.me/submissions/39696b20-2b98-4add-8e0d-26b6fa1dde84

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_RandomReduction
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic
import Theorems.Thm_APSCounting893_Main_jacobian_independence_criterion
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_exists_coordinate_transcendence_basis
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_determinant_le_row_bound {R σ ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ R)) (d : ι → ℕ)
    (hd : ∀ i j, (M i j).totalDegree ≤ d i) :
    M.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  have hcast : ((Equiv.Perm.sign s : MvPolynomial σ R)).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hh | hh <;> rw [hh] <;> simp
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [hcast,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i, (M (s i) i).totalDegree) ≤ ∑ i, d (s i) := Finset.sum_le_sum (fun i hi => hd _ _)
    _ = ∑ i, d i := Equiv.sum_comp s d

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma totalDegree_cramer_le {R σ : Type} [CommRing R] {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (MvPolynomial σ R)) (b : Fin k → MvPolynomial σ R)
    (hA : ∀ i j, (A i j).totalDegree ≤ 1) (hb : ∀ i, (b i).totalDegree ≤ 1)
    (j : Fin k) : (A.cramer b j).totalDegree ≤ k := by
  classical
  rw [Matrix.cramer_apply]
  have hh := totalDegree_determinant_le_row_bound (A.updateCol j b) (fun _ => 1) (by
    intro i l
    by_cases hl : l=j
    · subst l
      simpa using hb i
    · simpa [Matrix.updateCol_apply,hl] using hA i l)
  simpa using hh

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main
lemma totalDegree_eval₂_bounded_general {K L σ : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial σ L) (D : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ D * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  rw [← Finset.sum_mul]
  simpa [Finsupp.sum_fintype, Nat.mul_comm] using Nat.mul_le_mul_right D (le_totalDegree he)

end APSCounting893.Main
end Component_2

section Component_3

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
end Component_3

section Component_4

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

end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial
namespace APSCounting893.Main

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

theorem normalization_internal_solution (n : ℕ) (hn : 0 < n) (Y : Set (Affine ℂ (n + 1)))
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
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def coefficientFunctional {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) : MvPolynomial σ K :=
  AddMonoidAlgebra.map φ.toAddMonoidHom p

lemma coefficientFunctional_coeff {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) (e : σ →₀ ℕ) :
    (coefficientFunctional φ p).coeff e = φ (p.coeff e) := rfl

lemma coefficientFunctional_degree_le {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) :
    (coefficientFunctional φ p).totalDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  apply MvPolynomial.le_totalDegree
  apply MvPolynomial.mem_support_iff.mpr
  intro h
  have hq := MvPolynomial.mem_support_iff.mp he
  rw [coefficientFunctional_coeff,h,map_zero] at hq
  exact hq rfl

lemma coefficientFunctional_sum_monomials {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) :
    coefficientFunctional φ p = ∑ e ∈ p.support, MvPolynomial.monomial e (φ (p.coeff e)) := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [coefficientFunctional_coeff,MvPolynomial.coeff_sum]
  by_cases he : e ∈ p.support
  · simp [MvPolynomial.coeff_monomial,he]
  · have hzero := MvPolynomial.notMem_support_iff.mp he
    simp [MvPolynomial.coeff_monomial,he,hzero]

lemma coefficientFunctional_eval {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (φ : E →ₗ[K] K) (p : MvPolynomial σ E) (x : σ → K) :
    MvPolynomial.eval x (coefficientFunctional φ p) =
      φ (MvPolynomial.eval (fun j => algebraMap K E (x j)) p) := by
  classical
  rw [coefficientFunctional_sum_monomials]
  conv_rhs => rw [MvPolynomial.eval_eq]
  simp only [MvPolynomial.eval_sum,MvPolynomial.eval_monomial,map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hmul : p.coeff e * e.prod (fun j k => algebraMap K E (x j)^k) =
      (e.prod (fun j k => x j^k)) • p.coeff e := by
    rw [Algebra.smul_def,map_finsuppProd]
    simp only [map_pow]
    exact mul_comm _ _
  change φ (p.coeff e) * e.prod (fun j k => x j^k) =
    φ (p.coeff e * e.prod (fun j k => algebraMap K E (x j)^k))
  rw [hmul,map_smul,smul_eq_mul,mul_comm]

lemma exists_base_coefficient_certificate {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (p : MvPolynomial σ E) (hp : p ≠ 0) :
    ∃ q : MvPolynomial σ K, q ≠ 0 ∧ q.totalDegree ≤ p.totalDegree ∧
      ∀ x : σ → K, MvPolynomial.eval x q ≠ 0 →
        MvPolynomial.eval (fun j => algebraMap K E (x j)) p ≠ 0 := by
  classical
  have hex : ∃ e, p.coeff e ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hp
    ext e
    exact hh e
  obtain ⟨e,he⟩ := hex
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one K he
  refine ⟨coefficientFunctional φ p,?_,coefficientFunctional_degree_le φ p,?_⟩
  · intro h
    have hh := congrArg (MvPolynomial.coeff e) h
    rw [coefficientFunctional_coeff,hφ,MvPolynomial.coeff_zero] at hh
    exact one_ne_zero hh
  · intro x hx hpx
    rw [coefficientFunctional_eval,hpx,map_zero] at hx
    exact hx rfl

lemma exists_base_point_eval_ne_zero {K E σ : Type} [Field K] [Infinite K] [Field E] [Algebra K E]
    (p : MvPolynomial σ E) (hp : p ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval (fun j => algebraMap K E (x j)) p ≠ 0 := by
  classical
  obtain ⟨q,hq,hdegree,hgood⟩ := exists_base_coefficient_certificate (K := K) p hp
  have hex : ∃ x : σ → K, MvPolynomial.eval x q ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hq
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using hh x
  obtain ⟨x,hx⟩ := hex
  exact ⟨x,hgood x hx⟩

end APSCounting893.Main
end Component_6

section Component_7
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main.GenericLinearNormalization

noncomputable def linearProjectionPolynomials {K : Type} [Field K] {n : ℕ}
    (c : Affine K n) : PolynomialMap K (n+1) n :=
  fun i => MvPolynomial.X i.castSucc - MvPolynomial.C (c i) * MvPolynomial.X (Fin.last n)

lemma normalizationShear_eval {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K (n + 1)))
    (c : Affine K n) (p : Polynomials K (n + 1)) :
    (normalizationShear c p).eval₂ (coordinatePullback Y (linearProjectionPolynomials c))
      (coordinate Y (Fin.last n)) = Ideal.Quotient.mk (vanishingIdeal K Y) p := by
  let phi := Polynomial.eval₂RingHom (coordinatePullback Y (linearProjectionPolynomials c))
    (coordinate Y (Fin.last n))
  have heq : phi.comp (eval₂Hom (Polynomial.C.comp MvPolynomial.C) (normalizationLinearForms c)) =
      Ideal.Quotient.mk (vanishingIdeal K Y) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [phi, coordinatePullback]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [phi, normalizationLinearForms, coordinate]
      · simp [phi, normalizationLinearForms, coordinatePullback, linearProjectionPolynomials, coordinate]
  exact RingHom.congr_fun heq p

lemma normalization_last_integral {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K (n + 1)))
    (c : Affine K n) (p : Polynomials K (n + 1)) (hp : p ∈ vanishingIdeal K Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (linearProjectionPolynomials c)
    IsIntegral (Polynomials K n) (coordinate Y (Fin.last n)) := by
  classical
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (linearProjectionPolynomials c)
  let q := normalizationShear c p
  have hu : IsUnit q.leadingCoeff := normalizationShear_unit_leadingCoeff c p hc
  have hzero : q.eval₂ (coordinatePullback Y (linearProjectionPolynomials c))
      (coordinate Y (Fin.last n)) = 0 :=
    (normalizationShear_eval Y c p).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  refine ⟨hu.unit⁻¹.val • q, Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu, ?_⟩
  change Polynomial.eval₂ (coordinatePullback Y (linearProjectionPolynomials c))
    (coordinate Y (Fin.last n)) (hu.unit⁻¹.val • q) = 0
  rw [Polynomial.eval₂_smul, hzero, mul_zero]

lemma normalization_adjoin_last_eq_top {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K (n + 1))) (c : Affine K n) :
    letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (linearProjectionPolynomials c)
    Algebra.adjoin (Polynomials K n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y)) = ⊤ := by
  classical
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (linearProjectionPolynomials c)
  have halg : algebraMap (Polynomials K n) (CoordinateRing Y) = coordinatePullback Y (linearProjectionPolynomials c) := rfl
  let S := Algebra.adjoin (Polynomials K n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  have hz : coordinate Y (Fin.last n) ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  have hvar (i : Fin (n + 1)) : coordinate Y i ∈ S := by
    refine Fin.lastCases hz (fun j => ?_) i
    have h := S.add_mem (S.algebraMap_mem (MvPolynomial.X j))
      (S.mul_mem (S.algebraMap_mem (MvPolynomial.C (c j))) hz)
    simpa [halg, coordinatePullback, coordinate, linearProjectionPolynomials] using h
  apply top_unique
  intro b hb
  clear hb
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [halg, coordinatePullback] using S.algebraMap_mem (MvPolynomial.C a)
  | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
  | mul_X p i hp => simpa only [map_mul, coordinate, S] using S.mul_mem hp (hvar i)

lemma normalization_module_finite {K : Type} [Field K] {n : ℕ} (Y : Set (Affine K (n + 1)))
    (c : Affine K n) (p : Polynomials K (n + 1)) (hp : p ∈ vanishingIdeal K Y)
    (hc : eval c (normalizationParameter p) ≠ 0) :
    letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (linearProjectionPolynomials c)
    Module.Finite (Polynomials K n) (CoordinateRing Y) := by
  classical
  letI : Algebra (Polynomials K n) (CoordinateRing Y) := coordinatePullbackAlgebra Y (linearProjectionPolynomials c)
  let S := Algebra.adjoin (Polynomials K n) ({coordinate Y (Fin.last n)} : Set (CoordinateRing Y))
  letI : Module.Finite (Polynomials K n) S :=
    Algebra.finite_adjoin_simple_of_isIntegral (normalization_last_integral Y c p hp hc)
  apply Module.Finite.of_surjective S.val.toLinearMap
  intro b
  have hS : S = ⊤ := normalization_adjoin_last_eq_top Y c
  have hb : b ∈ S := by rw [hS]; trivial
  exact ⟨⟨b, hb⟩, rfl⟩


lemma exists_rational_direction {K : Type} [Field K] [CharZero K] {n : ℕ}
    (p : Polynomials K (n+1)) (hp : p ≠ 0) :
    ∃ c : Affine ℚ n, eval (fun j => (c j : K)) (normalizationParameter p) ≠ 0 := by
  obtain ⟨c,hc⟩ := exists_base_point_eval_ne_zero (K := ℚ) (normalizationParameter p)
    (normalizationParameter_ne_zero p hp)
  exact ⟨c,by simpa only [eq_ratCast] using hc⟩

end APSCounting893.Main.GenericLinearNormalization
end Component_7

section Component_8
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def composePolynomialMap {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K m r) : PolynomialMap K n r :=
  fun j => MvPolynomial.eval₂Hom MvPolynomial.C F (G j)

lemma evaluate_composePolynomialMap {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K m r) (x : Affine K n) :
    evaluate (composePolynomialMap F G) x = evaluate G (evaluate F x) := by
  funext j
  exact evaluation_substitution F (G j) x

lemma finiteMorphism_compose {K : Type} [Field K] {n m r : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) (G : PolynomialMap K m r)
    (hF : FiniteMorphism X F) (hG : FiniteMorphism (evaluate F '' X) G) :
    FiniteMorphism X (composePolynomialMap F G) := by
  classical
  obtain ⟨s,a,ha⟩ := hF
  obtain ⟨t,b,hb⟩ := hG
  let E : Fin (s*t) ≃ Fin s × Fin t := finProdFinEquiv.symm
  refine ⟨s*t,fun z => a (E z).1 * MvPolynomial.eval₂Hom MvPolynomial.C F (b (E z).2),?_⟩
  intro f
  obtain ⟨A,hA⟩ := ha f
  have hB (i : Fin s) := hb (A i)
  choose B hB using hB
  refine ⟨fun z => B (E z).1 (E z).2,?_⟩
  intro x hx
  have hFx : evaluate F x ∈ evaluate F '' X := ⟨x,hx,rfl⟩
  rw [hA x hx]
  calc
    (∑ i, eval (evaluate F x) (A i) * eval x (a i)) =
        ∑ i, (∑ j, eval (evaluate G (evaluate F x)) (B i j) * eval (evaluate F x) (b j)) * eval x (a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hB i _ hFx]
    _ = ∑ i : Fin s, ∑ j : Fin t,
        eval (evaluate (composePolynomialMap F G) x) (B i j) *
          eval x (a i * eval₂Hom MvPolynomial.C F (b j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [evaluate_composePolynomialMap,map_mul,evaluation_substitution]
      ring
    _ = ∑ z : Fin (s*t), eval (evaluate (composePolynomialMap F G) x) (B (E z).1 (E z).2) *
          eval x (a (E z).1 * eval₂Hom MvPolynomial.C F (b (E z).2)) := by
      have he := Equiv.sum_comp E (fun z : Fin s × Fin t =>
        eval (evaluate (composePolynomialMap F G) x) (B z.1 z.2) *
          eval x (a z.1 * eval₂Hom MvPolynomial.C F (b z.2)))
      simpa only [Fintype.sum_prod_type] using he.symm

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def rationalLinearPolynomials {K : Type} [Field K] [CharZero K] {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) : PolynomialMap K n r :=
  fun i => ∑ j, MvPolynomial.C (A i j : K) * MvPolynomial.X j

lemma rationalLinearPolynomials_degree {K : Type} [Field K] [CharZero K] {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (i : Fin r) :
    (rationalLinearPolynomials (K := K) A i).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

lemma evaluate_rationalLinearPolynomials {K : Type} [Field K] [CharZero K] {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (x : Affine K n) (i : Fin r) :
    evaluate (rationalLinearPolynomials A) x i = ∑ j, (A i j : K) * x j := by
  classical
  simp [evaluate,rationalLinearPolynomials]

lemma rationalLinearPolynomials_identity {K : Type} [Field K] [CharZero K] (n : ℕ) :
    rationalLinearPolynomials (K := K) (1 : Matrix (Fin n) (Fin n) ℚ) = fun i => MvPolynomial.X i := by
  classical
  funext i
  simp [rationalLinearPolynomials,Matrix.one_apply,apply_ite,ite_mul]

lemma rationalLinearPolynomials_compose {K : Type} [Field K] [CharZero K] {n m r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (B : Matrix (Fin r) (Fin m) ℚ) :
    composePolynomialMap (rationalLinearPolynomials (K := K) A) (rationalLinearPolynomials B) =
      rationalLinearPolynomials (B*A) := by
  classical
  funext i
  simp only [composePolynomialMap,rationalLinearPolynomials,map_sum,map_mul,MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X',Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul]
  simp only [Finset.mul_sum,Finset.sum_mul,map_sum,map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

noncomputable def rationalProjectionMatrix {n : ℕ} (c : Affine ℚ n) : Matrix (Fin n) (Fin (n+1)) ℚ :=
  fun i j => (if j = i.castSucc then 1 else 0) - if j = Fin.last n then c i else 0

lemma rationalProjectionMatrix_polynomials {K : Type} [Field K] [CharZero K] {n : ℕ}
    (c : Affine ℚ n) : rationalLinearPolynomials (K := K) (rationalProjectionMatrix c) =
      GenericLinearNormalization.linearProjectionPolynomials (fun j => (c j : K)) := by
  classical
  funext i
  simp only [rationalLinearPolynomials,rationalProjectionMatrix,GenericLinearNormalization.linearProjectionPolynomials,
    Rat.cast_sub,map_sub,sub_mul,Finset.sum_sub_distrib]
  congr 1
  · simp [apply_ite,ite_mul]
  · simp [apply_ite,ite_mul]

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

abbrev SectionCoefficientLabels (n k : ℕ) := Fin k × Fin (n+1)

noncomputable def universalSectionMatrix {K : Type} [CommRing K] {n k : ℕ} :
    Matrix (Fin k) (Fin n) (MvPolynomial (SectionCoefficientLabels n k) K) :=
  fun i j => MvPolynomial.X (i,j.castSucc)

noncomputable def universalSectionRhs {K : Type} [CommRing K] {n k : ℕ} :
    Fin k → MvPolynomial (SectionCoefficientLabels n k) K :=
  fun i => MvPolynomial.X (i,Fin.last n)

noncomputable def universalSectionPivot {K : Type} [CommRing K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) : Matrix (Fin k) (Fin k) (MvPolynomial (SectionCoefficientLabels n k) K) :=
  (universalSectionMatrix (K := K)).submatrix id (fun j => e (Sum.inr j))

noncomputable def universalSectionFree {K : Type} [CommRing K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) : Matrix (Fin k) (Fin r) (MvPolynomial (SectionCoefficientLabels n k) K) :=
  (universalSectionMatrix (K := K)).submatrix id (fun j => e (Sum.inl j))

noncomputable def sectionCramerVector {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) :
    Fin n → MvPolynomial (SectionCoefficientLabels n k) K :=
  fun j => Sum.elim
    (fun a => (universalSectionPivot (K := K) e).det * MvPolynomial.C (u a))
    (fun a => (universalSectionPivot e).cramer
      (universalSectionRhs - universalSectionFree e *ᵥ (fun a => MvPolynomial.C (u a))) a)
    (e.symm j)

lemma universalSectionPivot_degree {K : Type} [CommRing K] [Nontrivial K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) : (universalSectionPivot (K := K) e).det.totalDegree ≤ k := by
  have hh := totalDegree_determinant_le_row_bound (universalSectionPivot (K := K) e) (fun _ => 1)
    (fun i j => by simp [universalSectionPivot,universalSectionMatrix])
  simpa using hh

lemma sectionCramerVector_degree {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) (j : Fin n) :
    (sectionCramerVector e u j).totalDegree ≤ k := by
  classical
  unfold sectionCramerVector
  cases he : e.symm j with
  | inl a =>
    change ((universalSectionPivot (K := K) e).det * MvPolynomial.C (u a)).totalDegree ≤ k
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using universalSectionPivot_degree (K := K) e)
  | inr a =>
    apply totalDegree_cramer_le
    · intro i l
      simp [universalSectionPivot,universalSectionMatrix]
    · intro i
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · simp [universalSectionRhs]
      · apply MvPolynomial.totalDegree_finsetSum_le
        intro l hl
        apply (MvPolynomial.totalDegree_mul _ _).trans
        simp [universalSectionFree,universalSectionMatrix]

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 400000
open Matrix
namespace APSCounting893.Main

lemma ringHom_map_cramer {R S : Type} [CommRing R] [CommRing S] {k : ℕ}
    (f : R →+* S) (A : Matrix (Fin k) (Fin k) R) (b : Fin k → R) (j : Fin k) :
    f (A.cramer b j) = (A.map f).cramer (fun i => f (b i)) j := by
  classical
  rw [Matrix.cramer_apply,Matrix.cramer_apply,RingHom.map_det]
  congr 1
  ext i l
  by_cases h : l=j
  · subst l
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply,h,Ne.symm h]

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 400000
open Matrix
namespace APSCounting893.Main

lemma map_matrix_inverse_of_det_ne_zero {K L : Type} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  classical
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map f)
    (Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA))
  have he : (1 : Matrix (Fin n) (Fin n) K).map f = 1 := by
    ext i j
    simp [Matrix.one_apply,apply_ite]
  rw [Matrix.map_mul,he] at hh
  exact hh

lemma cramer_eq_det_smul_inverse_mulVec {K : Type} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (hA : A.det ≠ 0) :
    A.cramer b = A.det • (A⁻¹ *ᵥ b) := by
  classical
  calc
    A.cramer b = A⁻¹ *ᵥ (A *ᵥ A.cramer b) := by
      rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec]
    _ = A⁻¹ *ᵥ (A.det • b) := by rw [Matrix.mulVec_cramer]
    _ = _ := Matrix.mulVec_smul _ _ _

end APSCounting893.Main
end Component_12

section Component_13
set_option autoImplicit false
set_option maxHeartbeats 400000
open Matrix
namespace APSCounting893.Main

lemma ringHom_map_mulVec {R S ι κ : Type} [CommRing R] [CommRing S] [Fintype κ]
    (f : R →+* S) (A : Matrix ι κ R) (v : κ → R) :
    (fun i => f ((A *ᵥ v) i)) = (A.map f) *ᵥ (fun j => f (v j)) := by
  funext i
  simp [Matrix.mulVec,dotProduct,map_sum,map_mul]

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 400000
open Matrix
namespace APSCounting893.Main

noncomputable def splitAffineParam {K : Type} [Field K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K)
    (b : Fin k → K) (u : Fin r → K) : (Fin r ⊕ Fin k) → K :=
  Sum.elim u (B⁻¹ *ᵥ (b-C*ᵥu))

lemma splitAffineParam_injective {K : Type} [Field K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K)
    (b : Fin k → K) : Function.Injective (splitAffineParam B C b) := by
  intro u v h
  funext i
  exact congrFun h (Sum.inl i)

lemma splitAffineParam_range {K : Type} [Field K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K)
    (b : Fin k → K) (hB : B.det ≠ 0) :
    Set.range (splitAffineParam B C b) =
      {x | C *ᵥ (x ∘ Sum.inl) + B *ᵥ (x ∘ Sum.inr) = b} := by
  classical
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    change C*ᵥu + B*ᵥ(B⁻¹*ᵥ(b-C*ᵥu)) = b
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B hunit,Matrix.one_mulVec]
    abel
  · intro hx
    change C *ᵥ (x ∘ Sum.inl) + B *ᵥ (x ∘ Sum.inr) = b at hx
    have hp : B *ᵥ (x ∘ Sum.inr) = b-C*ᵥ(x ∘ Sum.inl) := by
      exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hx)
    refine ⟨x ∘ Sum.inl,?_⟩
    funext j
    cases j with
    | inl j => rfl
    | inr j =>
      change (B⁻¹*ᵥ(b-C*ᵥ(x ∘ Sum.inl))) j = x (Sum.inr j)
      rw [← hp,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul B hunit,Matrix.one_mulVec]
      rfl

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def evaluatedSectionPivot {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) : Matrix (Fin k) (Fin k) K :=
  (universalSectionPivot (K := K) e).map (eval s)

noncomputable def evaluatedSectionFree {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) : Matrix (Fin k) (Fin r) K :=
  (universalSectionFree (K := K) e).map (eval s)

noncomputable def evaluatedSectionRhs {K : Type} [Field K] {n k : ℕ}
    (s : SectionCoefficientLabels n k → K) : Fin k → K :=
  fun i => eval s (universalSectionRhs (K := K) i)

lemma eval_universalSectionPivot_det {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) :
    eval s (universalSectionPivot (K := K) e).det = (evaluatedSectionPivot e s).det := by
  rw [RingHom.map_det]
  rfl

lemma eval_section_linear_rhs {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K) :
    (fun i => eval s ((universalSectionRhs (K := K) -
      universalSectionFree e *ᵥ (fun j => MvPolynomial.C (u j)) :
        Fin k → MvPolynomial (SectionCoefficientLabels n k) K) i)) =
      evaluatedSectionRhs s - evaluatedSectionFree e s *ᵥ u := by
  funext i
  change eval s (universalSectionRhs i - ∑ j, universalSectionFree (K := K) e i j * MvPolynomial.C (u j)) = _
  simp only [map_sub,map_sum,map_mul,MvPolynomial.eval_C]
  rfl

lemma eval_sectionCramerVector {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (hB : (evaluatedSectionPivot e s).det ≠ 0) (j : Fin n) :
    eval s (sectionCramerVector e u j) = (evaluatedSectionPivot e s).det *
      splitAffineParam (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s) u (e.symm j) := by
  classical
  unfold sectionCramerVector
  cases hj : e.symm j with
  | inl a =>
    change eval s ((universalSectionPivot (K := K) e).det * MvPolynomial.C (u a)) = _
    rw [map_mul,eval_universalSectionPivot_det,MvPolynomial.eval_C]
    rfl
  | inr a =>
    change eval s ((universalSectionPivot (K := K) e).cramer
      (universalSectionRhs - universalSectionFree e *ᵥ (fun j => MvPolynomial.C (u j))) a) = _
    rw [ringHom_map_cramer,eval_section_linear_rhs]
    change (evaluatedSectionPivot e s).cramer _ a = _
    rw [cramer_eq_det_smul_inverse_mulVec _ _ hB]
    rfl

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def coordinateSectionSample {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) : SectionCoefficientLabels n k → K :=
  fun a => Fin.lastCases (x (e (Sum.inr a.1)))
    (fun j => if j = e (Sum.inr a.1) then 1 else 0) a.2

lemma coordinateSectionSample_matrix {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) (i : Fin k) (j : Fin n) :
    eval (coordinateSectionSample e x) (universalSectionMatrix (K := K) i j) =
      if j = e (Sum.inr i) then 1 else 0 := by
  simp [universalSectionMatrix,coordinateSectionSample]

lemma coordinateSectionSample_pivot {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) :
    (universalSectionPivot (K := K) e).map (eval (coordinateSectionSample e x)) = 1 := by
  classical
  ext i j
  simp [universalSectionPivot,Matrix.map_apply,Matrix.submatrix_apply,coordinateSectionSample_matrix,
    Matrix.one_apply,eq_comm]

lemma coordinateSectionSample_free {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) :
    (universalSectionFree (K := K) e).map (eval (coordinateSectionSample e x)) = 0 := by
  classical
  ext i j
  simp [universalSectionFree,Matrix.map_apply,Matrix.submatrix_apply,coordinateSectionSample_matrix]

lemma coordinateSectionSample_pivot_det {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) :
    eval (coordinateSectionSample e x) (universalSectionPivot (K := K) e).det = 1 := by
  rw [RingHom.map_det]
  change ((universalSectionPivot (K := K) e).map (eval (coordinateSectionSample e x))).det = 1
  rw [coordinateSectionSample_pivot,Matrix.det_one]

lemma coordinateSectionSample_cramerPoint {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) (j : Fin n) :
    eval (coordinateSectionSample e x) (sectionCramerVector e (fun a => x (e (Sum.inl a))) j) = x j := by
  classical
  unfold sectionCramerVector
  cases he : e.symm j with
  | inl a =>
    change eval (coordinateSectionSample e x)
      ((universalSectionPivot (K := K) e).det * MvPolynomial.C (x (e (Sum.inl a)))) = x j
    rw [map_mul,coordinateSectionSample_pivot_det,MvPolynomial.eval_C,one_mul]
    exact congrArg x (by simpa only [he] using e.apply_symm_apply j)
  | inr a =>
    change eval (coordinateSectionSample e x) ((universalSectionPivot (K := K) e).cramer
      (universalSectionRhs - universalSectionFree e *ᵥ (fun a => MvPolynomial.C (x (e (Sum.inl a))))) a) = x j
    rw [ringHom_map_cramer,coordinateSectionSample_pivot]
    have hb : (fun i : Fin k => eval (coordinateSectionSample e x)
        ((universalSectionRhs (K := K) (n := n) (k := k) -
          universalSectionFree e *ᵥ (fun a => MvPolynomial.C (x (e (Sum.inl a)))) :
            Fin k → MvPolynomial (SectionCoefficientLabels n k) K) i)) =
        fun i => x (e (Sum.inr i)) := by
      funext i
      change eval (coordinateSectionSample e x) (universalSectionRhs i -
        ∑ l, universalSectionFree (K := K) e i l * MvPolynomial.C (x (e (Sum.inl l)))) = _
      rw [map_sub,map_sum]
      have hfree (l : Fin r) : eval (coordinateSectionSample e x) (universalSectionFree (K := K) e i l) = 0 := by
        have hh := congrFun (congrFun (coordinateSectionSample_free e x) i) l
        exact hh
      simp only [map_mul,hfree,zero_mul,Finset.sum_const_zero,sub_zero]
      simp [universalSectionRhs,coordinateSectionSample]
    rw [hb,Matrix.cramer_one]
    exact congrArg x (by simpa only [he] using e.apply_symm_apply j)

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_pderiv_lt {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}
    (p : MvPolynomial (ι) K) (i : ι) (h : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs (e : ι →₀ ℕ) (he : e ∈ (pderiv i p).support) :
      e.sum (fun _ k => k) + 1 ≤ p.totalDegree := by
    have hcoef := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hcoef
    have hq : p.coeff (e + Finsupp.single i 1) ≠ 0 :=
      fun hz => hcoef (by rw [hz, zero_mul])
    have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hq)
    have heq : (e + Finsupp.single i 1).sum (fun _ k => k) = e.sum (fun _ k => k) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rwa [heq] at hh
  have hd : 0 < p.totalDegree := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr h
    have hh := hs e he
    omega
  have hb : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro e he
    have hh := hs e he
    omega
  omega

lemma eq_C_of_forall_pderiv_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι : Type*}
    (p : MvPolynomial (ι) K) (hp : ∀ i, pderiv i p = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    simp
  have hi : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hre : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have hc := congrArg (MvPolynomial.coeff (e - Finsupp.single i 1)) (hp i)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero, hre] at hc
  have hval : (e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 = e i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hn : (((e - Finsupp.single i 1 : ι →₀ ℕ) i : ℕ) : K) + 1 ≠ 0 := by
    have hh : (((e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hpc : p.coeff e = 0 := (mul_eq_zero.mp hc).resolve_right hn
  simp [MvPolynomial.coeff_C, Ne.symm he, hpc]

lemma pderiv_aeval_chain {K : Type*} [CommRing K] [IsDomain K] {ι κ : Type*} [Fintype ι]
    (F : ι → MvPolynomial (κ) K) (p : MvPolynomial (ι) K) (j : κ) :
    pderiv j (MvPolynomial.aeval F p) =
      ∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp,
      map_add, MvPolynomial.pderiv_X, map_mul, MvPolynomial.aeval_X]
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 : (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i)) * F k =
        ∑ i, MvPolynomial.aeval F (pderiv i p) * F k * pderiv j (F i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1]
    congr 1
    simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

end APSCounting893.Main
end Component_17

section Component_18

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
end Component_18

section Component_19

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
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def sectionHomogeneousPoint {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) :
    Fin (n+1) → MvPolynomial (SectionCoefficientLabels n k) K :=
  Fin.cons (universalSectionPivot (K := K) e).det (sectionCramerVector e u)

noncomputable def sectionTransverseMatrix {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) (d : ℕ)
    (F : Fin r → MvPolynomial (Fin n) K) :
    Matrix (Fin r ⊕ Fin k) (Fin r ⊕ Fin k) (MvPolynomial (SectionCoefficientLabels n k) K) :=
  fun i j => Sum.elim
    (fun a => MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e u)
      (homogenizeAll (d-1) (MvPolynomial.pderiv (e j) (F a))))
    (fun a => universalSectionMatrix a (e j)) i

noncomputable def sectionTransversalityPolynomial {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) (d : ℕ)
    (F : Fin r → MvPolynomial (Fin n) K) : MvPolynomial (SectionCoefficientLabels n k) K :=
  (universalSectionPivot (K := K) e).det * (sectionTransverseMatrix e u d F).det

lemma sectionHomogeneousPoint_degree {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) (j : Fin (n+1)) :
    (sectionHomogeneousPoint e u j).totalDegree ≤ k := by
  refine Fin.cases ?_ (fun j => ?_) j
  · exact universalSectionPivot_degree e
  · exact sectionCramerVector_degree e u j

lemma pderiv_totalDegree_le_pred_of_le {K σ : Type} [CommRing K] [IsDomain K]
    (p : MvPolynomial σ K) (d : ℕ) (hp : p.totalDegree ≤ d) (j : σ) :
    (MvPolynomial.pderiv j p).totalDegree ≤ d-1 := by
  by_cases hh : MvPolynomial.pderiv j p = 0
  · simp [hh]
  · have hh' := totalDegree_pderiv_lt p j hh
    omega

lemma sectionTransversalityPolynomial_degree {K : Type} [Field K] [CharZero K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (u : Fin r → K) (d : ℕ)
    (F : Fin r → MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d) :
    (sectionTransversalityPolynomial e u d F).totalDegree ≤ k * (r*(d-1)+2) := by
  classical
  have hp (i : Fin r) (j : Fin n) : (MvPolynomial.pderiv j (F i)).totalDegree ≤ d-1 :=
    pderiv_totalDegree_le_pred_of_le (F i) d (hF i) j
  let deg : (Fin r ⊕ Fin k) → ℕ := Sum.elim (fun _ => k*(d-1)) (fun _ => 1)
  have hrow (i j : Fin r ⊕ Fin k) : (sectionTransverseMatrix e u d F i j).totalDegree ≤ deg i := by
    cases i with
    | inl a =>
      have hh := totalDegree_eval₂_bounded_general (RingHom.id K) (sectionHomogeneousPoint e u) k
        (sectionHomogeneousPoint_degree e u) (homogenizeAll (d-1) (MvPolynomial.pderiv (e j) (F a)))
      have hhom := homogenizeAll_homogeneous (MvPolynomial.pderiv (e j) (F a)) (d-1) (hp a (e j))
      have hh' := hh.trans (Nat.mul_le_mul_left k hhom.totalDegree_le)
      simpa only [sectionTransverseMatrix,Sum.elim_inl,deg,RingHom.comp_id] using hh'
    | inr a => simp [sectionTransverseMatrix,deg,universalSectionMatrix]
  have hdet := totalDegree_determinant_le_row_bound (sectionTransverseMatrix e u d F) deg hrow
  have hsum : (∑ i, deg i) = r*(k*(d-1))+k := by simp [deg,Fintype.sum_sum_type]
  rw [hsum] at hdet
  exact (MvPolynomial.totalDegree_mul _ _).trans ((Nat.add_le_add (universalSectionPivot_degree e) hdet).trans_eq (by ring))

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def splitSectionPolynomials {K : Type} [Field K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K) (b : Fin k → K) :
    (Fin r ⊕ Fin k) → MvPolynomial (Fin r) K :=
  Sum.elim MvPolynomial.X (fun i => MvPolynomial.C ((B⁻¹*ᵥb) i) -
    ∑ j, MvPolynomial.C ((B⁻¹*C) i j) * MvPolynomial.X j)

lemma splitSectionPolynomials_eval {K : Type} [Field K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K) (b : Fin k → K) (u : Fin r → K) :
    (fun j => MvPolynomial.eval u (splitSectionPolynomials B C b j)) = splitAffineParam B C b u := by
  classical
  funext j
  cases j with
  | inl j => simp [splitSectionPolynomials,splitAffineParam]
  | inr j =>
    simp only [splitSectionPolynomials,Sum.elim_inr,MvPolynomial.eval_sub,MvPolynomial.eval_C,
      MvPolynomial.eval_sum,MvPolynomial.eval_mul,MvPolynomial.eval_X,splitAffineParam]
    rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec]
    rfl

lemma splitSectionPolynomials_pderiv {K : Type} [Field K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K) (b : Fin k → K) (j : Fin r)
    (a : Fin r ⊕ Fin k) :
    MvPolynomial.pderiv j (splitSectionPolynomials B C b a) =
      MvPolynomial.C (Sum.elim (fun i => if i=j then 1 else 0) (fun i => -(B⁻¹*C) i j) a) := by
  classical
  cases a with
  | inl i =>
    simp [splitSectionPolynomials,MvPolynomial.pderiv_X,Pi.single_apply,eq_comm,apply_ite]
  | inr i =>
    simp [splitSectionPolynomials,MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X,Pi.single_apply,apply_ite,mul_ite,ite_mul,eq_comm]

end APSCounting893.Main
end Component_21

section Component_22
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma eval_substitution_general {K ι κ : Type} [Field K]
    (P : ι → MvPolynomial κ K) (f : MvPolynomial ι K) (u : κ → K) :
    eval u (MvPolynomial.aeval P f) = eval (fun j => eval u (P j)) f := by
  have he : (eval u).comp (MvPolynomial.aeval P).toRingHom = eval (fun j => eval u (P j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro j; simp
  exact RingHom.congr_fun he f

lemma splitSection_jacobian_eval {K : Type} [Field K] [CharZero K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K) (b : Fin k → K)
    (F : Fin r → MvPolynomial (Fin r ⊕ Fin k) K) (u : Fin r → K) (i j : Fin r) :
    eval u (pderiv j (MvPolynomial.aeval (splitSectionPolynomials B C b) (F i))) =
      eval (splitAffineParam B C b u) (pderiv (Sum.inl j) (F i)) -
        ∑ l : Fin k, eval (splitAffineParam B C b u) (pderiv (Sum.inr l) (F i)) * (B⁻¹*C) l j := by
  classical
  rw [pderiv_aeval_chain]
  simp only [map_sum,map_mul]
  simp_rw [splitSectionPolynomials_pderiv,MvPolynomial.eval_C,eval_substitution_general,
    splitSectionPolynomials_eval]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  simp [mul_ite,Finset.sum_neg_distrib,← sub_eq_add_neg]

lemma splitSection_jacobian_determinant {K : Type} [Field K] [CharZero K] {r k : ℕ}
    (B : Matrix (Fin k) (Fin k) K) (C : Matrix (Fin k) (Fin r) K) (b : Fin k → K)
    (hB : B.det ≠ 0) (F : Fin r → MvPolynomial (Fin r ⊕ Fin k) K) (u : Fin r → K) :
    (Matrix.fromBlocks
      (fun i j => eval (splitAffineParam B C b u) (pderiv (Sum.inl j) (F i)))
      (fun i j => eval (splitAffineParam B C b u) (pderiv (Sum.inr j) (F i))) C B).det =
      B.det * (Matrix.of (fun i j => eval u
        (pderiv j (MvPolynomial.aeval (splitSectionPolynomials B C b) (F i))))).det := by
  classical
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [Matrix.det_fromBlocks₂₂,Matrix.invOf_eq_nonsing_inv]
  congr 1
  congr 1
  ext i j
  simp only [Matrix.of_apply,Matrix.sub_apply]
  rw [splitSection_jacobian_eval]
  rw [Matrix.mul_assoc]
  rfl

end APSCounting893.Main
end Component_22

section Component_23
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma coordinateSectionSample_homogeneousPoint {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) :
    (fun a => eval (coordinateSectionSample e x)
      (sectionHomogeneousPoint e (fun j => x (e (Sum.inl j))) a)) = Fin.cons 1 x := by
  funext a
  refine Fin.cases ?_ (fun j => ?_) a
  · exact coordinateSectionSample_pivot_det e x
  · exact coordinateSectionSample_cramerPoint e x j

lemma eval_homogenize_at_one {K : Type} [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) K) (d : ℕ) (hd : p.totalDegree ≤ d) (x : Fin n → K) :
    eval (Fin.cons 1 x) (homogenizeAll d p) = eval x p := by
  have he : (fun i : Fin (n+1) => Fin.cases (1 : K) x i) = Fin.cons 1 x := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  simpa only [one_mul,one_pow,MvPolynomial.eval₂_id,he] using
    eval_homogenize_scaled (RingHom.id K) p d hd 1 x

lemma coordinateSectionSample_substitution {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K)
    (p : MvPolynomial (Fin n) K) (d : ℕ) (hd : p.totalDegree ≤ d) :
    eval (coordinateSectionSample e x)
      (MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e (fun j => x (e (Sum.inl j))))
        (homogenizeAll d p)) = eval x p := by
  change eval (coordinateSectionSample e x)
    (MvPolynomial.aeval (sectionHomogeneousPoint e (fun j => x (e (Sum.inl j)))) (homogenizeAll d p)) = _
  rw [eval_substitution_general,coordinateSectionSample_homogeneousPoint,eval_homogenize_at_one p d hd]

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def evaluatedSectionPoint {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K) : Fin n → K :=
  fun j => splitAffineParam (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s) u (e.symm j)

lemma eval_sectionHomogeneousPoint {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (hB : (evaluatedSectionPivot e s).det ≠ 0) :
    (fun j => eval s (sectionHomogeneousPoint e u j)) =
      Fin.cases (evaluatedSectionPivot e s).det
        (fun j => (evaluatedSectionPivot e s).det * evaluatedSectionPoint e s u j) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact eval_universalSectionPivot_det e s
  · exact eval_sectionCramerVector e s u hB j

lemma eval_sectionHomogeneousSubstitution {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (hB : (evaluatedSectionPivot e s).det ≠ 0)
    (p : MvPolynomial (Fin n) K) (d : ℕ) (hd : p.totalDegree ≤ d) :
    eval s (MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e u) (homogenizeAll d p)) =
      (evaluatedSectionPivot e s).det ^ d * eval (evaluatedSectionPoint e s u) p := by
  change eval s (MvPolynomial.aeval (sectionHomogeneousPoint e u) (homogenizeAll d p)) = _
  rw [eval_substitution_general,eval_sectionHomogeneousPoint e s u hB]
  simpa only [MvPolynomial.eval₂_id] using
    eval_homogenize_scaled (RingHom.id K) p d hd (evaluatedSectionPivot e s).det (evaluatedSectionPoint e s u)

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def sectionCombinedJacobian {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (F : Fin r → MvPolynomial (Fin n) K) : Matrix (Fin r ⊕ Fin k) (Fin r ⊕ Fin k) K :=
  Matrix.fromBlocks
    (fun i j => eval (evaluatedSectionPoint e s u) (pderiv (e (Sum.inl j)) (F i)))
    (fun i j => eval (evaluatedSectionPoint e s u) (pderiv (e (Sum.inr j)) (F i)))
    (evaluatedSectionFree e s) (evaluatedSectionPivot e s)

lemma sectionTransverseMatrix_evaluation {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (hB : (evaluatedSectionPivot e s).det ≠ 0) (d : ℕ)
    (F : Fin r → MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d) :
    (sectionTransverseMatrix e u d F).map (eval s) =
      Matrix.diagonal (Sum.elim (fun _ : Fin r => (evaluatedSectionPivot e s).det ^ (d-1)) (fun _ : Fin k => 1)) *
        sectionCombinedJacobian e s u F := by
  classical
  ext i j
  rw [Matrix.diagonal_mul]
  cases i with
  | inl a =>
    cases j with
    | inl j =>
      change eval s (MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e u)
        (homogenizeAll (d-1) (pderiv (e (Sum.inl j)) (F a)))) = _
      exact eval_sectionHomogeneousSubstitution e s u hB _ _ (pderiv_totalDegree_le_pred_of_le (F a) d (hF a) _)
    | inr j =>
      change eval s (MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e u)
        (homogenizeAll (d-1) (pderiv (e (Sum.inr j)) (F a)))) = _
      exact eval_sectionHomogeneousSubstitution e s u hB _ _ (pderiv_totalDegree_le_pred_of_le (F a) d (hF a) _)
  | inr a =>
    cases j with
    | inl j =>
      change eval s (universalSectionMatrix (K := K) a (e (Sum.inl j))) = 1 * _
      rw [one_mul]
      rfl
    | inr j =>
      change eval s (universalSectionMatrix (K := K) a (e (Sum.inr j))) = 1 * _
      rw [one_mul]
      rfl

lemma sectionCombinedJacobian_det_ne_zero_of_certificate {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (d : ℕ) (F : Fin r → MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hcert : eval s (sectionTransversalityPolynomial e u d F) ≠ 0) :
    (evaluatedSectionPivot e s).det ≠ 0 ∧ (sectionCombinedJacobian e s u F).det ≠ 0 := by
  classical
  rw [sectionTransversalityPolynomial,map_mul] at hcert
  have hB : (evaluatedSectionPivot e s).det ≠ 0 := by
    rw [← eval_universalSectionPivot_det]
    exact left_ne_zero_of_mul hcert
  refine ⟨hB,?_⟩
  have hT := right_ne_zero_of_mul hcert
  intro hzero
  apply hT
  rw [RingHom.map_det]
  change ((sectionTransverseMatrix e u d F).map (eval s)).det = 0
  rw [sectionTransverseMatrix_evaluation e s u hB d F hF,Matrix.det_mul,hzero,mul_zero]

end APSCounting893.Main
end Component_25

section Component_26
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def evaluatedSectionPolynomials {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) : Fin n → MvPolynomial (Fin r) K :=
  fun j => splitSectionPolynomials (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s) (e.symm j)

lemma section_restriction_independent_of_certificate {K : Type} [Field K] [CharZero K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (u : Fin r → K)
    (d : ℕ) (F : Fin r → MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hcert : eval s (sectionTransversalityPolynomial e u d F) ≠ 0) :
    AlgebraicIndependent K (fun i => MvPolynomial.aeval (evaluatedSectionPolynomials e s) (F i)) := by
  classical
  obtain ⟨hB,hJ⟩ := sectionCombinedJacobian_det_ne_zero_of_certificate e s u d F hF hcert
  let B := evaluatedSectionPivot e s
  let C := evaluatedSectionFree e s
  let b := evaluatedSectionRhs s
  let G : Fin r → MvPolynomial (Fin r ⊕ Fin k) K := fun i => MvPolynomial.rename e.symm (F i)
  have hpartials (i : Fin r) (j : Fin r ⊕ Fin k) :
      pderiv j (G i) = MvPolynomial.rename e.symm (pderiv (e j) (F i)) := by
    have hh := MvPolynomial.pderiv_rename e.symm.injective (e j) (F i)
    simpa only [e.symm_apply_apply,G] using hh
  have heval (p : MvPolynomial (Fin n) K) :
      eval (splitAffineParam B C b u) (MvPolynomial.rename e.symm p) = eval (evaluatedSectionPoint e s u) p := by
    rw [MvPolynomial.eval_rename]
    rfl
  have hmatrix : Matrix.fromBlocks
      (fun i j => eval (splitAffineParam B C b u) (pderiv (Sum.inl j) (G i)))
      (fun i j => eval (splitAffineParam B C b u) (pderiv (Sum.inr j) (G i))) C B = sectionCombinedJacobian e s u F := by
    ext i j
    cases i <;> cases j <;> simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,sectionCombinedJacobian,hpartials,heval,B,C]
  have hh := splitSection_jacobian_determinant B C b hB G u
  rw [hmatrix] at hh
  have hdetAt : (Matrix.of (fun i j => eval u
      (pderiv j (MvPolynomial.aeval (splitSectionPolynomials B C b) (G i))))).det ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hh
    exact hJ hh
  have hdet : (Matrix.of (fun i j => pderiv j
      (MvPolynomial.aeval (splitSectionPolynomials B C b) (G i)))).det ≠ 0 := by
    intro hz
    apply hdetAt
    have he := congrArg (eval u) hz
    rw [map_zero,RingHom.map_det] at he
    exact he
  have hInd := (jacobian_independence_criterion (fun i =>
    MvPolynomial.aeval (splitSectionPolynomials B C b) (G i))).mpr ⟨id,Function.injective_id,hdet⟩
  have hfun : (fun i => MvPolynomial.aeval (splitSectionPolynomials B C b) (G i)) =
      fun i => MvPolynomial.aeval (evaluatedSectionPolynomials e s) (F i) := by
    funext i
    dsimp only [G]
    rw [MvPolynomial.aeval_rename]
    rfl
  rw [hfun] at hInd
  exact hInd

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def splitRationalSectionParameter {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (B : Matrix (Fin k) (Fin k) ℚ)
    (C : Matrix (Fin k) (Fin r) ℚ) (b : Fin k → ℚ) : SectionParameter n r :=
  (fun j a => Sum.elim (fun i => if i=a then 1 else 0) (fun i => -(B⁻¹*C) i a) (e.symm j),
   fun j => Sum.elim (fun _ => 0) (fun i => (B⁻¹*ᵥb) i) (e.symm j))

lemma parameterMap_splitRationalSectionParameter {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (B : Matrix (Fin k) (Fin k) ℚ)
    (C : Matrix (Fin k) (Fin r) ℚ) (b : Fin k → ℚ) (hB : B.det ≠ 0) :
    parameterMap (splitRationalSectionParameter e B C b) =
      fun j => splitSectionPolynomials (B.map (algebraMap ℚ ℂ)) (C.map (algebraMap ℚ ℂ))
        (fun i => (b i : ℂ)) (e.symm j) := by
  classical
  let f : ℚ →+* ℂ := algebraMap ℚ ℂ
  have hInv := map_matrix_inverse_of_det_ne_zero f B hB
  have hlinear : (B⁻¹*C).map f = (B.map f)⁻¹*C.map f := by rw [Matrix.map_mul,hInv]
  have htrans : (fun i => f ((B⁻¹*ᵥb) i)) = (B.map f)⁻¹*ᵥ(fun i => f (b i)) := by
    rw [ringHom_map_mulVec,hInv]
  funext j
  cases hj : e.symm j with
  | inl a =>
    simp [parameterMap,splitRationalSectionParameter,hj,splitSectionPolynomials,apply_ite,ite_mul]
  | inr a =>
    simp only [parameterMap,splitRationalSectionParameter,hj,Sum.elim_inr,splitSectionPolynomials]
    change MvPolynomial.C (((B⁻¹*ᵥb) a : ℚ) : ℂ) +
      (∑ j, MvPolynomial.C ((-(B⁻¹*C) a j : ℚ) : ℂ) * MvPolynomial.X j) = _
    have ht := congrFun htrans a
    have hl (j : Fin r) := congrFun (congrFun hlinear a) j
    simp only [Matrix.map_apply,f,eq_ratCast] at ht hl
    rw [ht]
    simp only [splitSectionPolynomials,Sum.elim_inr,Rat.cast_neg,map_neg,neg_mul,Finset.sum_neg_distrib]
    have he (j : Fin r) : (((B⁻¹*C) a j : ℚ) : ℂ) = ((B.map (algebraMap ℚ ℂ))⁻¹*C.map (algebraMap ℚ ℂ)) a j := hl j
    simp only [he]
    exact (sub_eq_add_neg _ _).symm

end APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma evaluatedSectionPivot_map {K L : Type} [Field K] [Field L] {n r k : ℕ}
    (f : K →+* L) (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) :
    evaluatedSectionPivot e (fun a => f (s a)) = (evaluatedSectionPivot e s).map f := by
  ext i j
  simp [evaluatedSectionPivot,universalSectionPivot,universalSectionMatrix,Matrix.map_apply,Matrix.submatrix_apply]

lemma evaluatedSectionFree_map {K L : Type} [Field K] [Field L] {n r k : ℕ}
    (f : K →+* L) (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) :
    evaluatedSectionFree e (fun a => f (s a)) = (evaluatedSectionFree e s).map f := by
  ext i j
  simp [evaluatedSectionFree,universalSectionFree,universalSectionMatrix,Matrix.map_apply,Matrix.submatrix_apply]

lemma evaluatedSectionRhs_map {K L : Type} [Field K] [Field L] {n k : ℕ}
    (f : K →+* L) (s : SectionCoefficientLabels n k → K) :
    evaluatedSectionRhs (fun a => f (s a)) = fun i => f (evaluatedSectionRhs s i) := by
  funext i
  simp [evaluatedSectionRhs,universalSectionRhs]

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma evaluatedSection_blocks_equations {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) (x : Fin n → K) :
    (∀ i : Fin k, ∑ j : Fin n, s (i,j.castSucc) * x j = s (i,Fin.last n)) ↔
      evaluatedSectionFree e s *ᵥ (fun j => x (e (Sum.inl j))) +
        evaluatedSectionPivot e s *ᵥ (fun j => x (e (Sum.inr j))) = evaluatedSectionRhs s := by
  classical
  have hsum (i : Fin k) : (∑ j : Fin n, s (i,j.castSucc) * x j) =
      (∑ j : Fin r, s (i,(e (Sum.inl j)).castSucc) * x (e (Sum.inl j))) +
        ∑ j : Fin k, s (i,(e (Sum.inr j)).castSucc) * x (e (Sum.inr j)) := by
    have hh := Equiv.sum_comp e (fun j => s (i,j.castSucc) * x j)
    simpa only [Fintype.sum_sum_type] using hh.symm
  have hentry (i : Fin k) :
      (evaluatedSectionFree e s *ᵥ (fun j => x (e (Sum.inl j))) +
        evaluatedSectionPivot e s *ᵥ (fun j => x (e (Sum.inr j)))) i = ∑ j : Fin n, s (i,j.castSucc) * x j := by
    rw [hsum]
    simp [evaluatedSectionFree,evaluatedSectionPivot,universalSectionFree,universalSectionPivot,
      universalSectionMatrix,Matrix.mulVec,dotProduct]
  constructor
  · intro h
    funext i
    rw [hentry,h i]
    simp [evaluatedSectionRhs,universalSectionRhs]
  · intro h i
    have hh := congrFun h i
    rw [hentry] at hh
    simpa [evaluatedSectionRhs,universalSectionRhs] using hh

lemma evaluatedSectionPoint_range {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K)
    (hB : (evaluatedSectionPivot e s).det ≠ 0) :
    Set.range (evaluatedSectionPoint e s) =
      {x : Fin n → K | ∀ i : Fin k, ∑ j : Fin n, s (i,j.castSucc) * x j = s (i,Fin.last n)} := by
  classical
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    apply (evaluatedSection_blocks_equations e s _).mpr
    have hh : splitAffineParam (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s) u ∈
        Set.range (splitAffineParam (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s)) := ⟨u,rfl⟩
    rw [splitAffineParam_range _ _ _ hB] at hh
    simpa only [Set.mem_setOf_eq,evaluatedSectionPoint,e.symm_apply_apply,Function.comp_def] using hh
  · intro hx
    have hh := (evaluatedSection_blocks_equations e s x).mp hx
    have hx' : (fun j : Fin r ⊕ Fin k => x (e j)) ∈
        Set.range (splitAffineParam (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s)) := by
      rw [splitAffineParam_range _ _ _ hB]
      exact hh
    obtain ⟨u,hu⟩ := hx'
    refine ⟨u,?_⟩
    funext j
    have hj := congrFun hu (e.symm j)
    simpa only [e.apply_symm_apply,evaluatedSectionPoint] using hj

lemma evaluatedSectionPoint_injective {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) :
    Function.Injective (evaluatedSectionPoint e s) := by
  intro u v h
  funext j
  have hh := congrFun h (e (Sum.inl j))
  simpa only [evaluatedSectionPoint,e.symm_apply_apply,splitAffineParam,Sum.elim_inl] using hh

end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (imageClosure F) = RingHom.ker (MvPolynomial.aeval F).toRingHom := by
  rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
  rfl

noncomputable def imageCoordinateAlgebraMap {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : CoordinateRing (imageClosure F) →ₐ[K] MvPolynomial (Fin n) K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval F) (fun p hp => by
    rw [imageClosure_vanishingIdeal_eq_kernel] at hp
    exact hp)

lemma imageCoordinateAlgebraMap_mk {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (p : Polynomials K m) :
    imageCoordinateAlgebraMap F (Ideal.Quotient.mk (vanishingIdeal K (imageClosure F)) p) =
      MvPolynomial.aeval F p := rfl

lemma imageCoordinateAlgebraMap_injective {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) : Function.Injective (imageCoordinateAlgebraMap F) := by
  apply (injective_iff_map_eq_zero (imageCoordinateAlgebraMap F).toRingHom).mpr
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [imageClosure_vanishingIdeal_eq_kernel]
  change MvPolynomial.aeval F p = 0
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ p) = 0 at hx
  rw [imageCoordinateAlgebraMap_mk] at hx
  exact hx

lemma imageCoordinateAlgebraMap_coordinate {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) (j : Fin m) :
    imageCoordinateAlgebraMap F (coordinate (imageClosure F) j) = F j := by
  change imageCoordinateAlgebraMap F (Ideal.Quotient.mk _ (MvPolynomial.X j)) = F j
  rw [imageCoordinateAlgebraMap_mk,MvPolynomial.aeval_X]

end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma prime_quotient_dimension_lower_of_independent {m r : ℕ}
    (P : Ideal (MvPolynomial (Fin (m+1)) ℂ)) [P.IsPrime]
    (v : Fin r → MvPolynomial (Fin (m+1)) ℂ ⧸ P) (hv : AlgebraicIndependent ℂ v) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin (m+1)) ℂ ⧸ P) := by
  classical
  let A := MvPolynomial (Fin (m+1)) ℂ ⧸ P
  let L := FractionRing A
  letI : Algebra.EssFiniteType A L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  letI : Algebra.EssFiniteType ℂ L := Algebra.EssFiniteType.comp ℂ A L
  let f : A →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ A L
  have hfield := hv.map' (f := f) (IsFractionRing.injective A L)
  have hcard := hfield.cardinalMk_le_trdeg
  have hfinite := trdeg_lt_aleph0 ℂ L
  have hnat := Cardinal.toNat_le_toNat hcard hfinite
  have hn : r ≤ (Algebra.trdeg ℂ L).toNat := by simpa using hnat
  rw [OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P]
  exact_mod_cast hn

end APSCounting893.Main
end Component_31

section Component_32
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma image_dimension_lower_of_independent_coordinates {n m r : ℕ}
    (F : PolynomialMap ℂ n (m+1)) (g : Fin r → Fin (m+1))
    (hF : AlgebraicIndependent ℂ (F ∘ g)) :
    ((r : ℕ∞) : WithBot ℕ∞) ≤ RSCapacity.algDim (imageClosure F) := by
  classical
  let P := vanishingIdeal ℂ (imageClosure F)
  letI : P.IsPrime := irreducibleAffine_ideal_prime (irreducibleAffine_imageClosure F)
  have hcoord : AlgebraicIndependent ℂ (fun i => coordinate (imageClosure F) (g i)) := by
    apply AlgebraicIndependent.of_comp (imageCoordinateAlgebraMap F)
    have he : (imageCoordinateAlgebraMap F ∘ (fun i => coordinate (imageClosure F) (g i))) = F ∘ g := by
      funext i
      exact imageCoordinateAlgebraMap_coordinate F (g i)
    rw [he]
    exact hF
  exact prime_quotient_dimension_lower_of_independent P _ hcoord

end APSCounting893.Main
end Component_32

section Component_33
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma closed_subset_eq_of_dimension {K : Type} [Field K] {m r : ℕ}
    (X Y : Set (Affine K m)) (hX : RSCapacity.IsAlgSet X) (hY : IrreducibleAffine Y)
    (hXY : X ⊆ Y) (hYdim : RSCapacity.algDim Y = ((r : ℕ∞) : WithBot ℕ∞))
    (hXdim : ((r : ℕ∞) : WithBot ℕ∞) ≤ RSCapacity.algDim X) : X = Y := by
  classical
  let I := vanishingIdeal K Y
  let J := vanishingIdeal K X
  have hIJ : I ≤ J := vanishingIdeal_anti_mono hXY
  have heq : I = J := by
    by_contra hne
    have hlt : I < J := lt_of_le_of_ne hIJ hne
    obtain ⟨p,hpJ,hpI⟩ := SetLike.exists_of_lt hlt
    letI : I.IsPrime := irreducibleAffine_ideal_prime hY
    let f : (Polynomials K m ⧸ I) →+* (Polynomials K m ⧸ J) := Ideal.Quotient.factor hIJ
    have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
    have hpn : Ideal.Quotient.mk I p ≠ 0 := fun h => hpI (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hzero : f (Ideal.Quotient.mk I p) = 0 := by
      rw [Ideal.Quotient.factor_mk,Ideal.Quotient.eq_zero_iff_mem]
      exact hpJ
    have hd := ringKrullDim_succ_le_of_surjective f hf (mem_nonZeroDivisors_iff_ne_zero.mpr hpn) hzero
    change ringKrullDim (Polynomials K m ⧸ I) = ((r : ℕ∞) : WithBot ℕ∞) at hYdim
    change ((r : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (Polynomials K m ⧸ J) at hXdim
    have hh := (add_le_add hXdim le_rfl).trans hd
    rw [hYdim] at hh
    have hbad : r+1 ≤ r := by exact_mod_cast hh
    omega
  rw [isAlgSet_eq_zeroLocus hX,isAlgSet_eq_zeroLocus hY.2.1]
  exact congrArg (MvPolynomial.zeroLocus K) heq.symm

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_compose_subset {K : Type} [Field K] {n a m : ℕ}
    (P : PolynomialMap K a n) (F : PolynomialMap K n m) :
    imageClosure (composePolynomialMap P F) ⊆ imageClosure F := by
  apply MvPolynomial.zeroLocus_anti_mono
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro y ⟨x,rfl⟩
  exact ⟨evaluate P x,(evaluate_composePolynomialMap P F x).symm⟩

lemma imageClosure_section_eq_of_independent_coordinates {n a m r : ℕ}
    (P : PolynomialMap ℂ a n) (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (g : Fin r → Fin (m+1))
    (hG : AlgebraicIndependent ℂ ((composePolynomialMap P F) ∘ g)) :
    imageClosure (composePolynomialMap P F) = imageClosure F := by
  apply closed_subset_eq_of_dimension
  · exact (irreducibleAffine_imageClosure _).2.1
  · exact irreducibleAffine_imageClosure F
  · exact imageClosure_compose_subset P F
  · exact hdim
  · exact image_dimension_lower_of_independent_coordinates _ g hG

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

noncomputable def rationalSectionParameter {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → ℚ) : SectionParameter n r :=
  splitRationalSectionParameter e (evaluatedSectionPivot e s) (evaluatedSectionFree e s) (evaluatedSectionRhs s)

lemma parameterMap_rationalSectionParameter {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → ℚ)
    (hB : (evaluatedSectionPivot e (fun a => (s a : ℂ))).det ≠ 0) :
    parameterMap (rationalSectionParameter e s) = evaluatedSectionPolynomials e (fun a => (s a : ℂ)) := by
  have hBp : evaluatedSectionPivot e (fun a => (s a : ℂ)) =
      (evaluatedSectionPivot e s).map (algebraMap ℚ ℂ) := by
    simpa only [eq_ratCast] using evaluatedSectionPivot_map (algebraMap ℚ ℂ) e s
  have hCp : evaluatedSectionFree e (fun a => (s a : ℂ)) =
      (evaluatedSectionFree e s).map (algebraMap ℚ ℂ) := by
    simpa only [eq_ratCast] using evaluatedSectionFree_map (algebraMap ℚ ℂ) e s
  have hbp : evaluatedSectionRhs (fun a => (s a : ℂ)) =
      fun i => ((evaluatedSectionRhs s i : ℚ) : ℂ) := by
    simpa only [eq_ratCast] using evaluatedSectionRhs_map (algebraMap ℚ ℂ) s
  have hQ : (evaluatedSectionPivot e s).det ≠ 0 := by
    intro hz
    apply hB
    rw [hBp]
    have hh := (algebraMap ℚ ℂ).map_det (evaluatedSectionPivot e s)
    change (algebraMap ℚ ℂ) ((evaluatedSectionPivot e s).det) =
      ((evaluatedSectionPivot e s).map (algebraMap ℚ ℂ)).det at hh
    rw [← hh,hz,map_zero]
  rw [rationalSectionParameter,parameterMap_splitRationalSectionParameter e _ _ _ hQ]
  unfold evaluatedSectionPolynomials
  rw [hBp,hCp,hbp]

lemma evaluate_evaluatedSectionPolynomials {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (s : SectionCoefficientLabels n k → K) :
    evaluate (evaluatedSectionPolynomials e s) = evaluatedSectionPoint e s := by
  funext u j
  exact congrFun (splitSectionPolynomials_eval (evaluatedSectionPivot e s)
    (evaluatedSectionFree e s) (evaluatedSectionRhs s) u) (e.symm j)

lemma rationalSectionParameter_parametrizes {n m r : ℕ}
    (e : (Fin r ⊕ Fin (n-r)) ≃ Fin n) (s : ReductionLabels n m r → ℚ)
    (hB : (evaluatedSectionPivot e (fun a => (s (Sum.inl a) : ℂ))).det ≠ 0) :
    ParametrizesSection s (rationalSectionParameter e (fun a => s (Sum.inl a))) := by
  unfold ParametrizesSection
  rw [parameterMap_rationalSectionParameter e _ hB,evaluate_evaluatedSectionPolynomials]
  exact ⟨evaluatedSectionPoint_injective e _, evaluatedSectionPoint_range e _ hB⟩

lemma selectedSectionParameter_parametrizes_of_exists {n m r : ℕ}
    (s : ReductionLabels n m r → ℚ) (h : ∃ p, ParametrizesSection s p) :
    ParametrizesSection s (selectedSectionParameter s) := by
  exact Classical.epsilon_spec h

lemma imageClosure_parameterMap_eq_of_parametrizes {n m r t : ℕ}
    (s : ReductionLabels n m r → ℚ) (p q : SectionParameter n r)
    (hp : ParametrizesSection s p) (hq : ParametrizesSection s q) (F : PolynomialMap ℂ n t) :
    imageClosure (composePolynomialMap (parameterMap p) F) =
      imageClosure (composePolynomialMap (parameterMap q) F) := by
  have hr : Set.range (evaluate (composePolynomialMap (parameterMap p) F)) =
      Set.range (evaluate (composePolynomialMap (parameterMap q) F)) := by
    simp only [funext (evaluate_composePolynomialMap (parameterMap p) F),
      funext (evaluate_composePolynomialMap (parameterMap q) F)]
    change Set.range (evaluate F ∘ evaluate (parameterMap p)) = Set.range (evaluate F ∘ evaluate (parameterMap q))
    rw [Set.range_comp,Set.range_comp,hp.2,hq.2]
  exact congrArg RSCapacity.zClosure hr

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma sectionTransversalityPolynomial_coordinate_eval {K : Type} [Field K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (x : Fin n → K) (d : ℕ)
    (F : Fin r → MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d) :
    eval (coordinateSectionSample e x)
      (sectionTransversalityPolynomial e (fun j => x (e (Sum.inl j))) d F) =
      (Matrix.of (fun i j => eval x (pderiv (e (Sum.inl j)) (F i)))).det := by
  classical
  let u := fun j => x (e (Sum.inl j))
  let Jf : Matrix (Fin r) (Fin r) K := fun i j => eval x (pderiv (e (Sum.inl j)) (F i))
  let Jp : Matrix (Fin r) (Fin k) K := fun i j => eval x (pderiv (e (Sum.inr j)) (F i))
  have he : (sectionTransverseMatrix e u d F).map (eval (coordinateSectionSample e x)) =
      Matrix.fromBlocks Jf Jp 0 1 := by
    ext i j
    cases i with
    | inl a =>
      cases j with
      | inl j =>
        change eval (coordinateSectionSample e x)
          (MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e u)
            (homogenizeAll (d-1) (pderiv (e (Sum.inl j)) (F a)))) = _
        exact coordinateSectionSample_substitution e x _ _
          (pderiv_totalDegree_le_pred_of_le (F a) d (hF a) _)
      | inr j =>
        change eval (coordinateSectionSample e x)
          (MvPolynomial.eval₂Hom MvPolynomial.C (sectionHomogeneousPoint e u)
            (homogenizeAll (d-1) (pderiv (e (Sum.inr j)) (F a)))) = _
        exact coordinateSectionSample_substitution e x _ _
          (pderiv_totalDegree_le_pred_of_le (F a) d (hF a) _)
    | inr a =>
      cases j with
      | inl j =>
        exact congrFun (congrFun (coordinateSectionSample_free e x) a) j
      | inr j =>
        exact congrFun (congrFun (coordinateSectionSample_pivot e x) a) j
  rw [sectionTransversalityPolynomial,map_mul,coordinateSectionSample_pivot_det,one_mul,RingHom.map_det]
  change ((sectionTransverseMatrix e u d F).map (eval (coordinateSectionSample e x))).det = _
  rw [he,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one]
  rfl

lemma sectionTransversalityPolynomial_ne_zero {K : Type} [Field K] [Infinite K] {n r k : ℕ}
    (e : (Fin r ⊕ Fin k) ≃ Fin n) (d : ℕ)
    (F : Fin r → MvPolynomial (Fin n) K) (hF : ∀ i, (F i).totalDegree ≤ d)
    (hminor : (Matrix.of (fun i j => pderiv (e (Sum.inl j)) (F i))).det ≠ 0) :
    ∃ u : Fin r → K, sectionTransversalityPolynomial e u d F ≠ 0 := by
  classical
  have hex : ∃ x : Fin n → K, eval x (Matrix.of (fun i j => pderiv (e (Sum.inl j)) (F i))).det ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hminor
    apply MvPolynomial.funext
    intro x
    simpa only [map_zero] using hh x
  obtain ⟨x,hx⟩ := hex
  refine ⟨fun j => x (e (Sum.inl j)),?_⟩
  intro hzero
  have hh := sectionTransversalityPolynomial_coordinate_eval e x d F hF
  rw [hzero,map_zero] at hh
  apply hx
  rw [RingHom.map_det]
  exact hh.symm

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
namespace APSCounting893.Main

lemma section_degree_bound_le_source (k r m d : ℕ) (hd : 1 ≤ d) (hrm : r < m) :
    k*(r*(d-1)+2) ≤ 2*k*d^m := by
  have hbasic (r : ℕ) : r*(d-1)+1 ≤ d^r := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ]
      have hdiff : d-1+1=d := Nat.sub_add_cancel hd
      have hp : 1 ≤ d^r := one_le_pow₀ hd
      have hprod := Nat.mul_le_mul_right (d-1) hp
      nlinarith
  have hpower : d^r ≤ d^m := Nat.pow_le_pow_right hd hrm.le
  have hpos : 1 ≤ d^r := one_le_pow₀ hd
  have hh : r*(d-1)+2 ≤ 2*d^m := by nlinarith [hbasic r]
  nlinarith

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_independent_image_coordinates {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ g : Fin r → Fin (m+1), Function.Injective g ∧ AlgebraicIndependent ℂ (F ∘ g) := by
  classical
  let S := MvPolynomial (Fin (m+1)) ℂ
  let R := MvPolynomial (Fin n) ℂ
  let P : Ideal S := RingHom.ker (MvPolynomial.aeval F).toRingHom
  letI : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s,hind,hcard⟩ := OAI.PiExponent.FormalInterpolation.mvPolynomial_exists_coordinate_transcendence_basis P
  have hDim := OAI.PiExponent.FormalInterpolation.mvPolynomial_quotient_dimension_eq_fraction_field_trdeg_toNat P
  have hP : vanishingIdeal ℂ (imageClosure F) = P := by
    rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
    rfl
  change ringKrullDim (S ⧸ vanishingIdeal ℂ (imageClosure F)) = ((r : ℕ∞) : WithBot ℕ∞) at hdim
  rw [hP] at hdim
  have htr : (Algebra.trdeg ℂ (FractionRing (S ⧸ P))).toNat = r := by
    exact_mod_cast hDim.symm.trans hdim
  have hsr : s.card = r := hcard.trans htr
  let f₀ : (S ⧸ P) →ₐ[ℂ] FractionRing (S ⧸ P) := IsScalarTower.toAlgHom ℂ (S ⧸ P) _
  have he (i : s) : f₀ (Ideal.Quotient.mk P (MvPolynomial.X i.1)) =
      algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := by
    dsimp only [f₀]
    rw [IsScalarTower.toAlgHom_apply,IsScalarTower.algebraMap_apply S (S ⧸ P) (FractionRing (S ⧸ P))]
    rfl
  have hquot : AlgebraicIndependent ℂ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1)) := by
    apply AlgebraicIndependent.of_comp f₀
    have hef : (f₀ ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => algebraMap S (FractionRing (S ⧸ P)) (MvPolynomial.X i.1) := funext he
    rw [hef]
    exact hind
  let f : (S ⧸ P) →ₐ[ℂ] R := Ideal.Quotient.liftₐ P (MvPolynomial.aeval F) (fun p hp => hp)
  have hfapp (p : S) : f (Ideal.Quotient.mk P p) = MvPolynomial.aeval F p := rfl
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f.toRingHom).mpr
    intro x hx
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change MvPolynomial.aeval F p = 0
    change f (Ideal.Quotient.mk P p) = 0 at hx
    rw [hfapp] at hx
    exact hx
  have hindF : AlgebraicIndependent ℂ (fun i : s => F i.1) := by
    have hh := hquot.map' hf
    have hefun : (f ∘ (fun i : s => Ideal.Quotient.mk P (MvPolynomial.X i.1))) =
        fun i : s => F i.1 := by
      funext i
      change f (Ideal.Quotient.mk P (MvPolynomial.X i.1)) = F i.1
      rw [hfapp,MvPolynomial.aeval_X]
    rw [hefun] at hh
    exact hh
  let e : Fin r ≃ s := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using hsr.symm)
  refine ⟨fun i => (e i).1,Subtype.val_injective.comp e.injective,?_⟩
  exact hindF.comp e e.injective

end APSCounting893.Main
end Component_38

section Component_39
set_option autoImplicit false
namespace APSCounting893.Main

lemma exists_sum_equiv_extending_injection {n r : ℕ} (g : Fin r → Fin n)
    (hg : Function.Injective g) :
    ∃ e : (Fin r ⊕ Fin (n-r)) ≃ Fin n, ∀ j, e (Sum.inl j) = g j := by
  classical
  let s : Set (Fin n) := Set.range g
  let e₁ : Fin r ≃ s := Equiv.ofInjective g hg
  have hscard : Fintype.card s = r := by simpa only [Fintype.card_fin] using (Fintype.card_congr e₁).symm
  have hcard : Fintype.card (sᶜ : Set (Fin n)) = n-r := by
    simpa only [Fintype.card_fin,hscard] using Fintype.card_compl_set s
  let e₂ : Fin (n-r) ≃ (sᶜ : Set (Fin n)) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let e := (Equiv.sumCongr e₁ e₂).trans (Equiv.Set.sumCompl s)
  refine ⟨e,?_⟩
  intro j
  rfl

end APSCounting893.Main
end Component_39

section Component_40
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma affine_section_certificate {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hrm : r < m+1)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ q : MvPolynomial (SectionCoefficientLabels n (n-r)) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ 2*(n-r)*(inputDegree F)^(m+1) ∧
      ∀ s : ReductionLabels n (m+1) r → ℚ,
        eval (fun a => (s (Sum.inl a) : ℂ)) q ≠ 0 →
        ParametrizesSection s (selectedSectionParameter s) ∧
        imageClosure (composePolynomialMap (parameterMap (selectedSectionParameter s)) F) = imageClosure F := by
  classical
  obtain ⟨g,hg,hgInd⟩ := exists_independent_image_coordinates F hdim
  obtain ⟨j,hj,hminor⟩ := (jacobian_independence_criterion (F ∘ g)).mp hgInd
  obtain ⟨e,he⟩ := exists_sum_equiv_extending_injection j hj
  have hminor' : (Matrix.of (fun i a => pderiv (e (Sum.inl a)) ((F ∘ g) i))).det ≠ 0 := by
    simpa only [he] using hminor
  have hdeg (i : Fin r) : ((F ∘ g) i).totalDegree ≤ inputDegree F := by
    exact (Finset.le_sup (f := fun a => (F a).totalDegree) (Finset.mem_univ (g i))).trans (le_max_right _ _)
  obtain ⟨u,hu⟩ := sectionTransversalityPolynomial_ne_zero e (inputDegree F) (F ∘ g) hdeg hminor'
  let q := sectionTransversalityPolynomial e u (inputDegree F) (F ∘ g)
  refine ⟨q,hu,(sectionTransversalityPolynomial_degree e u (inputDegree F) (F ∘ g) hdeg).trans ?_,?_⟩
  · exact section_degree_bound_le_source (n-r) r (m+1) (inputDegree F) (le_max_left _ _) hrm
  · intro s hs
    have hB := (sectionCombinedJacobian_det_ne_zero_of_certificate e (fun a => (s (Sum.inl a) : ℂ))
      u (inputDegree F) (F ∘ g) hdeg hs).1
    let p := rationalSectionParameter e (fun a => s (Sum.inl a))
    have hp : ParametrizesSection s p := rationalSectionParameter_parametrizes e s hB
    have hselected := selectedSectionParameter_parametrizes_of_exists s ⟨p,hp⟩
    refine ⟨hselected,?_⟩
    rw [imageClosure_parameterMap_eq_of_parametrizes s _ p hselected hp F]
    apply imageClosure_section_eq_of_independent_coordinates _ F hdim g
    have hind := section_restriction_independent_of_certificate e (fun a => (s (Sum.inl a) : ℂ))
      u (inputDegree F) (F ∘ g) hdeg hs
    have hfun : ((composePolynomialMap (parameterMap p) F) ∘ g) =
        fun i => MvPolynomial.aeval (evaluatedSectionPolynomials e (fun a => (s (Sum.inl a) : ℂ))) ((F ∘ g) i) := by
      funext i
      dsimp only [composePolynomialMap,Function.comp_def]
      rw [show p = rationalSectionParameter e (fun a => s (Sum.inl a)) from rfl,
        parameterMap_rationalSectionParameter e _ hB]
      rfl
    rw [hfun]
    exact hind

end APSCounting893.Main
end Component_40

open APSCounting893.Main
open MvPolynomial
theorem solution {n m r : ℕ} (F : PolynomialMap ℂ n (m+1))
    (hrm : r < m+1)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞)) :
    ∃ q : MvPolynomial ((Fin (n-r) × Fin (n+1))) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ 2*(n-r)*(inputDegree F)^(m+1) ∧
      ∀ s : ReductionLabels n (m+1) r → ℚ,
        eval (fun a => (s (Sum.inl a) : ℂ)) q ≠ 0 →
        ParametrizesSection s (selectedSectionParameter s) ∧
        imageClosure ((fun i => MvPolynomial.eval₂Hom MvPolynomial.C (parameterMap (selectedSectionParameter s)) (F i))) = imageClosure F := by
  exact affine_section_certificate F hrm hdim
