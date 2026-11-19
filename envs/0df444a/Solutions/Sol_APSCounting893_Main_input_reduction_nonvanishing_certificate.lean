-- Prove2me | solution 1 for APSCounting893.Main.input_reduction_nonvanishing_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:26:45.529093+00:00
-- url     : https://prove2.me/submissions/cbaa3f9a-72aa-4322-9eb0-51104601a680

import Definitions.Def_APSCounting893_Main_Geometry
import Theorems.Thm_APSCounting893_Main_affine_section_nonvanishing_certificate
import Theorems.Thm_APSCounting893_Main_output_projection_nonvanishing_certificate
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
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_vanishingIdeal_eq_kernel {K : Type} [Field K] [Infinite K] {n m : ℕ}
    (F : PolynomialMap K n m) :
    vanishingIdeal K (imageClosure F) = RingHom.ker (MvPolynomial.aeval F).toRingHom := by
  rw [imageClosure,vanishingIdeal_zClosure,image_vanishingIdeal_eq_kernel]
  rfl

end APSCounting893.Main
end Component_1

section Component_2
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

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main
lemma aeval_composePolynomialMap {K : Type} [Field K] {n m t : ℕ}
    (F : PolynomialMap K n m) (P : PolynomialMap K m t) (p : Polynomials K t) :
    MvPolynomial.aeval F (MvPolynomial.aeval P p) = MvPolynomial.aeval (composePolynomialMap F P) p := by
  have hh : composePolynomialMap F P = fun i => MvPolynomial.aeval F (P i) := by
    funext i
    simp only [composePolynomialMap,aeval_def,MvPolynomial.algebraMap_eq]
    rfl
  rw [hh]
  exact MvPolynomial.comp_aeval_apply P (MvPolynomial.aeval F) p

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma imageClosure_postcompose_congr {K : Type} [Field K] [Infinite K] {n a m t : ℕ}
    (F : PolynomialMap K n m) (G : PolynomialMap K a m) (P : PolynomialMap K m t)
    (h : imageClosure F = imageClosure G) :
    imageClosure (composePolynomialMap F P) = imageClosure (composePolynomialMap G P) := by
  have hI := congrArg (vanishingIdeal K) h
  rw [imageClosure_vanishingIdeal_eq_kernel,imageClosure_vanishingIdeal_eq_kernel] at hI
  have hk : RingHom.ker (MvPolynomial.aeval (R := K) (composePolynomialMap F P)).toRingHom =
      RingHom.ker (MvPolynomial.aeval (R := K) (composePolynomialMap G P)).toRingHom := by
    ext p
    change MvPolynomial.aeval (R := K) (composePolynomialMap F P) p = 0 ↔ MvPolynomial.aeval (R := K) (composePolynomialMap G P) p = 0
    rw [← aeval_composePolynomialMap,← aeval_composePolynomialMap]
    exact SetLike.ext_iff.mp hI (MvPolynomial.aeval P p)
  unfold imageClosure RSCapacity.zClosure
  rw [image_vanishingIdeal_eq_kernel,image_vanishingIdeal_eq_kernel]
  exact congrArg (zeroLocus K) hk

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def outputProjection {K : Type} [Field K] {m r : ℕ}
    (A : Fin (r+1) × Fin m → K) : PolynomialMap K m (r+1) :=
  fun i => ∑ j, MvPolynomial.C (A (i,j)) * MvPolynomial.X j

lemma outputProjection_composite {K : Type} [Field K] {n m r : ℕ}
    (F : PolynomialMap K n m) (A : Fin (r+1) × Fin m → K) (i : Fin (r+1)) :
    composePolynomialMap F (outputProjection A) i = ∑ j, MvPolynomial.C (A (i,j)) * F j := by
  classical
  simp [composePolynomialMap,outputProjection]


end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma reducedPolynomialMap_eq_identity {n r : ℕ} (F : PolynomialMap ℂ n (r+1))
    (s : ReductionLabels n (r+1) r → ℚ) :
    reducedPolynomialMap F s = composePolynomialMap (parameterMap (selectedSectionParameter s)) F := by
  simp [reducedPolynomialMap,composePolynomialMap]
  rfl

lemma reducedPolynomialMap_eq_projection {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (s : ReductionLabels n m r → ℚ) (hm : m ≠ r+1) :
    reducedPolynomialMap F s = composePolynomialMap
      (composePolynomialMap (parameterMap (selectedSectionParameter s)) F)
      (outputProjection (fun a => (s (Sum.inr a) : ℂ))) := by
  funext i
  rw [outputProjection_composite]
  simp only [reducedPolynomialMap,dif_neg hm,composePolynomialMap]

lemma input_certificate_from_sections_and_projection
    (n m r : ℕ) (F : PolynomialMap ℂ n m)
    (hnonconstant : ∀ i, 0 < (F i).totalDegree)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (hr : 1 ≤ r) (hrm : r < m) :
    ∃ p : MvPolynomial (Fin (Fintype.card (ReductionLabels n m r))) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ 2*(n-r)*inputDegree F^m+(r+1)*inputDegree F^r ∧
      ∀ s : ReductionLabels n m r → ℚ,
        eval (fun j => (s ((Fintype.equivFin (ReductionLabels n m r)).symm j) : ℂ)) p ≠ 0 → ReductionSucceeds F s := by
  classical
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  obtain ⟨q,hq,hqdeg,hsection⟩ := affine_section_nonvanishing_certificate F hrm hdim
  obtain ⟨p,hp,hpdeg,hprojection⟩ := output_projection_nonvanishing_certificate F (by omega) hrm hdim
  let q' : MvPolynomial (ReductionLabels n (m+1) r) ℂ := MvPolynomial.rename Sum.inl q
  let p' : MvPolynomial (ReductionLabels n (m+1) r) ℂ := MvPolynomial.rename Sum.inr p
  have hqp : q'*p' ≠ 0 := mul_ne_zero
    (fun hz => hq ((MvPolynomial.rename_injective _ Sum.inl_injective) hz))
    (fun hz => hp ((MvPolynomial.rename_injective _ Sum.inr_injective) hz))
  let e := Fintype.equivFin (ReductionLabels n (m+1) r)
  refine ⟨MvPolynomial.rename e (q'*p'),?_,?_,?_⟩
  · exact fun hz => hqp ((MvPolynomial.rename_injective _ e.injective) hz)
  · apply (MvPolynomial.totalDegree_rename_le e (q'*p')).trans
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add ((MvPolynomial.totalDegree_rename_le Sum.inl q).trans hqdeg) ((MvPolynomial.totalDegree_rename_le Sum.inr p).trans hpdeg))
  · intro s hs
    have hse : eval (fun a => (s a : ℂ)) (q'*p') ≠ 0 := by
      simpa only [MvPolynomial.eval_rename,Function.comp_def,e,Equiv.symm_apply_apply] using hs
    rw [map_mul] at hse
    have hqeval : eval (fun a => (s (Sum.inl a) : ℂ)) q ≠ 0 := by
      simpa only [q',MvPolynomial.eval_rename,Function.comp_def] using left_ne_zero_of_mul hse
    obtain ⟨hparam,hclosure⟩ := hsection s hqeval
    change imageClosure (composePolynomialMap (parameterMap (selectedSectionParameter s)) F) = imageClosure F at hclosure
    refine ⟨hparam,?_⟩
    change RSCapacity.algDim (imageClosure (reducedPolynomialMap F s)) = ((r : ℕ∞) : WithBot ℕ∞) ∧
      ((0 : Affine ℂ (m+1)) ∈ imageClosure F ↔ (0 : Affine ℂ (r+1)) ∈ imageClosure (reducedPolynomialMap F s))
    by_cases hm : m+1=r+1
    · have hmr : m=r := Nat.succ.inj hm
      subst m
      rw [reducedPolynomialMap_eq_identity,hclosure]
      exact ⟨hdim,Iff.rfl⟩
    · have hpeval : eval (fun a => (s (Sum.inr a) : ℂ)) p ≠ 0 := by
        simpa only [p',MvPolynomial.eval_rename,Function.comp_def] using right_ne_zero_of_mul hse
      obtain ⟨hpd,hpaps⟩ := hprojection (fun a => s (Sum.inr a)) hpeval
      have hpost := imageClosure_postcompose_congr
        (composePolynomialMap (parameterMap (selectedSectionParameter s)) F) F
        (outputProjection (fun a => (s (Sum.inr a) : ℂ))) hclosure
      have heq : imageClosure (reducedPolynomialMap F s) =
          imageClosure (fun i : Fin (r+1) => ∑ j : Fin (m+1), C (s (Sum.inr (i,j)) : ℂ)*F j) := by
        rw [reducedPolynomialMap_eq_projection F s hm,hpost]
        congr 1
        funext i
        exact outputProjection_composite F _ i
      rw [heq]
      exact ⟨hpd,hpaps⟩

end APSCounting893.Main
end Component_6

open APSCounting893.Main
theorem solution
    (n m r : ℕ) (F : PolynomialMap ℂ n m)
    (hnonconstant : ∀ i, 0 < (F i).totalDegree)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (hr : 1 ≤ r) (hrm : r < m) :
    ∃ p : MvPolynomial (Fin (Fintype.card (ReductionLabels n m r))) ℂ,
      p ≠ 0 ∧ p.totalDegree ≤ 2 * (n-r) * inputDegree F ^ m + (r+1) * inputDegree F ^ r ∧
      ∀ s : ReductionLabels n m r → ℚ,
        MvPolynomial.eval (fun j => (s ((Fintype.equivFin (ReductionLabels n m r)).symm j) : ℂ)) p ≠ 0 →
          ReductionSucceeds F s := by
  exact input_certificate_from_sections_and_projection n m r F hnonconstant hdim hr hrm
