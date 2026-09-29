-- Prove2me | solution 1 for AutomorphicForm.linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/38814f96-5ce5-541c-9f11-1e35e888a865

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    {κ : Type} [Fintype κ] (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x)) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    LinearIndependent ℝ (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1))) ∧
    (Submodule.span ℝ (Set.range (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ =>
        (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1)))) :
        Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
      {X | X * ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        ((Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} := by
  classical
  letI algR : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI algE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  set δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
    Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) c with hδ
  set f : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
    fun p => (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1)) with hf
  show LinearIndependent ℝ f ∧
    (Submodule.span ℝ (Set.range f) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
      {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
          X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)}
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L

  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
      K L (InfiniteAdeleRing K) σ δ₀ c κ x hx hspan

  let eR : InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
    AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) (fun r =>
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _)
  let β : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (InfiniteAdeleRing K) :=
    (mixedEmbedding.latticeBasis K).map eR.symm.toLinearEquiv
  have hβ : ∀ a, β a = algebraMap K (InfiniteAdeleRing K) (integralBasis K a) := by
    intro a
    simp only [β, Module.Basis.map_apply, mixedEmbedding.latticeBasis_apply]
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

  have hsm : ∀ (r : ℝ) (l : L) (k : InfiniteAdeleRing K),
      r • (l ⊗ₜ[K] k : L ⊗[K] InfiniteAdeleRing K) = l ⊗ₜ[K] (r • k) := by
    intro r l k
    rw [Algebra.smul_def, Algebra.smul_def]
    change ((1 : L) ⊗ₜ[K] algebraMap ℝ (InfiniteAdeleRing K) r) * (l ⊗ₜ[K] k) =
      l ⊗ₜ[K] (algebraMap ℝ (InfiniteAdeleRing K) r * k)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

  have hcomb : ∀ r : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ → ℝ,
      ∑ p, r p • f p = ∑ i, (x i).map (fun l : L => l ⊗ₜ[K] (∑ a, r (a, i) • β a)) := by
    intro r
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext j k
    simp only [Matrix.sum_apply, Matrix.smul_apply, hf, Matrix.map_apply, TensorProduct.tmul_sum, hsm, hβ]
  refine ⟨?_, ?_⟩
  ·
    rw [Fintype.linearIndependent_iff]
    intro r hr
    rw [hcomb] at hr
    have hk : (fun i => ∑ a, r (a, i) • β a) = 0 := by
      apply e.injective
      apply Subtype.ext
      rw [he, he, hr]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      ext j k
      simp only [Matrix.map_apply, Pi.zero_apply, TensorProduct.tmul_zero, Matrix.zero_apply]
    intro p
    have hp := congr_fun hk p.2
    exact (Fintype.linearIndependent_iff.1 β.linearIndependent (fun a => r (a, p.2)) hp) p.1
  · apply Set.Subset.antisymm
    ·
      let S' : Submodule ℝ (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
        { carrier := AutomorphicForm.twistedCommutant K L (InfiniteAdeleRing K) σ δ
          add_mem' := fun hX hY => Subalgebra.add_mem _ hX hY
          zero_mem' := Subalgebra.zero_mem _
          smul_mem' := fun r X hX => by
            have : r • X = (Algebra.TensorProduct.includeRight (R := K) (A := L)
                (algebraMap ℝ (InfiniteAdeleRing K) r)) • X := by
              ext j k
              simp only [Matrix.smul_apply]
              rw [Algebra.smul_def]
              rfl
            rw [this]
            exact AutomorphicForm.includeRight_smul_mem_twistedCommutant δ hX _ }
      have hle : Submodule.span ℝ (Set.range f) ≤ S' := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨p, rfl⟩
        show f p ∈ AutomorphicForm.twistedCommutant K L (InfiniteAdeleRing K) σ δ
        have hfp : f p = ((e (Pi.single p.2 (β p.1)) : AutomorphicForm.twistedCommutant K L (InfiniteAdeleRing K) σ δ) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
          rw [he]
          ext j k
          simp only [hf, Matrix.map_apply, Matrix.sum_apply, Pi.single_apply, hβ]
          rw [Finset.sum_eq_single p.2]
          · rw [if_pos rfl]
          · intro i _ hi
            rw [if_neg hi, TensorProduct.tmul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hfp]
        exact Subtype.prop _
      exact hle
    · intro X hX
      obtain ⟨a, ha⟩ := e.surjective ⟨X, hX⟩
      have hXa : X = ∑ i, (x i).map (fun l : L => l ⊗ₜ[K] a i) := by
        rw [← he a, ha]
      have hX' : X = ∑ p, (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ => β.repr (a p.2) p.1) p • f p := by
        rw [hcomb, hXa]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 2
        funext l
        rw [β.sum_repr (a i)]
      rw [hX']
      exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

end S_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor
end P2MW
export P2MW.S_AutomorphicForm_linearIndependent_and_coe_span_map_tmul_integralBasis_eq_setOf_mul_eq_mul_map_sigmaTensor (solution)
