-- Prove2me | solution 1 for Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c97e3ca3-c0a1-5c75-a6cb-ffc75b87f251

import Mathlib
import Theorems.Thm_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A') [GradedAlgebra 𝒜']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')

    (hφlin : φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))

    (hφdeg : ∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → ∀ t : S',
      φ (a ⊗ₜ t) ∈ ((𝒜' n).restrictScalars S).baseChange S')

    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom)))))
    :
    let A : Subalgebra S A' :=
      AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _)) ∧
      (∀ a ∈ A, ∀ n : ℕ, (DirectSum.decompose 𝒜' a n : A') ∈ A) := by
  intro A
  classical

  set φL : A' ⊗[S] S' ≃ₗ[S] S' ⊗[S] A' := φ.toLinearEquiv with hφL
  have φL_apply : ∀ x, φL x = φ x := fun _ => rfl

  have hlin : ∀ (s t : S'), φ (algebraMap S' A' s ⊗ₜ[S] t) = s ⊗ₜ[S] algebraMap S' A' t := by
    intro s t
    have := AlgHom.congr_fun hφlin (s ⊗ₜ[S] t)
    simpa [Algebra.TensorProduct.map_tmul] using this

  have hleft : ∀ (s : S') (y : S' ⊗[S] A'), (s ⊗ₜ[S] (1 : A')) * y = s • y := by
    intro s y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add y z hy hz => rw [mul_add, hy, hz, smul_add]
  have hright : ∀ (b : S') (y : S' ⊗[S] A'),
      ((1 : S') ⊗ₜ[S] algebraMap S' A' b) * y = (DistribSMul.toLinearMap S A' b).lTensor S' y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.lTensor_tmul]; simp [Algebra.smul_def]
    | add y z hy hz => rw [mul_add, hy, hz, map_add]

  have hφ₁ : ∀ (b : S') (x : A' ⊗[S] S'), φL (b • x) = b • φL x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      rw [φL_apply, φL_apply, TensorProduct.smul_tmul', Algebra.smul_def,
        show (algebraMap S' A' b * a) ⊗ₜ[S] t = (algebraMap S' A' b ⊗ₜ[S] (1 : S')) * (a ⊗ₜ[S] t) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        map_mul, hlin, map_one, hleft]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

  have hφ₂ : ∀ (b : S') (x : A' ⊗[S] S'),
      φL ((LinearMap.mulLeft S b).lTensor A' x) = (DistribSMul.toLinearMap S A' b).lTensor S' (φL x) := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a t =>
      rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, φL_apply, φL_apply,
        show a ⊗ₜ[S] (b * t) = ((1 : A') ⊗ₜ[S] b) * (a ⊗ₜ[S] t) by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul],
        map_mul, show (1 : A') = algebraMap S' A' 1 from (map_one _).symm, hlin, ← hright]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

  have agree_mapL : ∀ w : S' ⊗[S] (A' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom w = (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').lTensor S' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_mapR : ∀ w : (A' ⊗[S] S') ⊗[S] S',
      Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S') w = (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v s => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_commL : ∀ w : S' ⊗[S] (A' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A' S').toAlgHom w =
        (TensorProduct.comm S A' S').toLinearMap.lTensor S' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul s v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_commN : ∀ w : A' ⊗[S] (S' ⊗[S] S'),
      Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S' S').toAlgHom w =
        (TensorProduct.comm S S' S').toLinearMap.lTensor A' w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]; congr 1
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc1 : ∀ w : (S' ⊗[S] A') ⊗[S] S',
      (Algebra.TensorProduct.assoc S S S S' A' S') w = (TensorProduct.assoc S S' A' S') w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v s =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul t a => rfl
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc2 : ∀ w : (A' ⊗[S] S') ⊗[S] S',
      (Algebra.TensorProduct.assoc S S S A' S' S') w = (TensorProduct.assoc S A' S' S') w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v s =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul a t => rfl
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have agree_assoc2s : ∀ w : A' ⊗[S] (S' ⊗[S] S'),
      (Algebra.TensorProduct.assoc S S S A' S' S').symm w = (TensorProduct.assoc S A' S' S').symm w := by
    intro w
    apply (Algebra.TensorProduct.assoc S S S A' S' S').injective
    rw [AlgEquiv.apply_symm_apply, agree_assoc2, LinearEquiv.apply_symm_apply]

  have hcoc :
      (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').lTensor S' ∘ₗ
          (TensorProduct.assoc S S' A' S').toLinearMap ∘ₗ
          (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' =
        (TensorProduct.comm S A' S').toLinearMap.lTensor S' ∘ₗ
          (TensorProduct.assoc S S' A' S').toLinearMap ∘ₗ
          (φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A').rTensor S' ∘ₗ
          (TensorProduct.assoc S A' S' S').symm.toLinearMap ∘ₗ
          (TensorProduct.comm S S' S').toLinearMap.lTensor A' ∘ₗ
          (TensorProduct.assoc S A' S' S').toLinearMap := by
    apply LinearMap.ext
    intro w
    have key := AlgHom.congr_fun hφcoc w
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe] at key
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [← agree_mapR, ← agree_assoc1, ← agree_mapL, ← agree_assoc2, ← agree_commN, ← agree_assoc2s, ← agree_mapR,
      ← agree_assoc1, ← agree_commL]
    exact key

  obtain ⟨hbc, -⟩ := Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum S' φL hφ₁ hφ₂ hcoc
  have hEq : LinearMap.eqLocus ((φL : A' ⊗[S] S' →ₗ[S] S' ⊗[S] A') ∘ₗ (TensorProduct.mk S A' S').flip 1)
      (TensorProduct.mk S S' A' 1) = A.toSubmodule := by
    ext a
    simp only [LinearMap.mem_eqLocus, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, Subalgebra.mem_toSubmodule]
    show φ (a ⊗ₜ[S] 1) = (1 : S') ⊗ₜ[S] a ↔ a ∈ A
    rw [AlgHom.mem_equalizer]
    rfl
  rw [hEq] at hbc
  refine ⟨?_, ?_⟩
  ·
    have hfun : ∀ x : S' ⊗[S] ↥A,
        Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _) x = hbc.equiv x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
        rw [Algebra.TensorProduct.lift_tmul]
        erw [IsBaseChange.equiv_tmul]
        rw [Algebra.smul_def]
        rfl
      | add x y hx hy => rw [map_add, hx, hy]; erw [map_add]
    have : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _) :
        S' ⊗[S] ↥A → A') = hbc.equiv := funext hfun
    rw [this]
    exact hbc.equiv.bijective
  ·
    intro a ha n

    let π : A' →ₗ[S] A' :=
      { toFun := fun x => (DirectSum.decompose 𝒜' x n : A')
        map_add' := fun x y => by simp [DirectSum.decompose_add]
        map_smul' := fun s x => by
          rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul S' s x, ← IsScalarTower.algebraMap_smul S' s]
          rw [DirectSum.decompose_smul]; rfl }
    have hπ : ∀ x, π x = (DirectSum.decompose 𝒜' x n : A') := fun _ => rfl

    have hπm : ∀ (m : ℕ) (y : S' ⊗[S] A'), y ∈ ((𝒜' m).restrictScalars S).baseChange S' →
        π.baseChange S' y = if m = n then y else 0 := by
      intro m y hy
      rw [Submodule.baseChange_eq_span] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        replace hx : x ∈ 𝒜' m := hx
        rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul, hπ]
        by_cases hmn : m = n
        · subst hmn; rw [if_pos rfl, DirectSum.decompose_of_mem_same 𝒜' hx]
        · rw [if_neg hmn, DirectSum.decompose_of_mem_ne 𝒜' hx hmn, TensorProduct.tmul_zero]
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz]; split_ifs <;> simp
      | smul s y _ hy => rw [map_smul, hy]; split_ifs <;> simp

    have hinv : φ (a ⊗ₜ[S] 1) = (1 : S') ⊗ₜ[S] a := (AlgHom.mem_equalizer _ _ a).mp ha
    have hsum : a = ∑ m ∈ (DirectSum.decompose 𝒜' a).support, (DirectSum.decompose 𝒜' a m : A') :=
      (DirectSum.sum_support_decompose 𝒜' a).symm
    have hL : π.baseChange S' (φ (a ⊗ₜ[S] 1)) = φ ((DirectSum.decompose 𝒜' a n : A') ⊗ₜ[S] 1) := by
      conv_lhs => rw [hsum]
      rw [TensorProduct.sum_tmul, map_sum, map_sum]
      rw [Finset.sum_congr rfl (fun m _ => hπm m _ (hφdeg m _ (Subtype.mem _) 1))]
      rw [Finset.sum_ite_eq']
      split_ifs with hn
      · rfl
      · rw [DFinsupp.notMem_support_iff.mp hn]; simp
    have hR : π.baseChange S' ((1 : S') ⊗ₜ[S] a) = (1 : S') ⊗ₜ[S] (DirectSum.decompose 𝒜' a n : A') := by
      rw [LinearMap.baseChange_tmul, hπ]
    apply (AlgHom.mem_equalizer _ _ _).mpr
    show φ ((DirectSum.decompose 𝒜' a n : A') ⊗ₜ[S] 1) = (1 : S') ⊗ₜ[S] (DirectSum.decompose 𝒜' a n : A')
    rw [← hL, ← hR, hinv]

end S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
end P2MW
export P2MW.S_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle (solution)
