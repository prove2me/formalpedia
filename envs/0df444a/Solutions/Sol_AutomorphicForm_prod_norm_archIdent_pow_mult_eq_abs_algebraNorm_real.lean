-- Prove2me | solution 1 for AutomorphicForm.prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6684c566-a20b-5c13-9338-70654da623fb

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Theorems.Thm_AutomorphicForm_moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det
import Theorems.Thm_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal NNReal Pointwise TensorProduct TensorProduct.RightActions

namespace ArchModuleDict

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

@[reducible] noncomputable def algRK : Algebra ℝ (InfiniteAdeleRing K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

@[reducible] noncomputable def algRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

noncomputable def algEquivK :
    letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
    InfiniteAdeleRing K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRK K
  AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) (fun r => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _)

theorem distribHaarChar_eq_abs_norm {E : Type*} [CommRing E] [Algebra ℝ E] [Module.Finite ℝ E]
    [TopologicalSpace E] [IsTopologicalRing E] [T2Space E] [ContinuousSMul ℝ E] [LocallyCompactSpace E]
    (u : Eˣ) : (distribHaarChar E u : ℝ) = |Algebra.norm ℝ (u : E)| := by
  classical
  borelize E
  haveI : IsTopologicalAddGroup E := inferInstance
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts E))
  let μ : Measure E := Measure.addHaarMeasure K₀

  let n := Module.finrank ℝ E
  let b := Module.finBasis ℝ E
  let φ : E ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let ψ : E ≃ᵐ (Fin n → ℝ) := φ.toHomeomorph.toMeasurableEquiv
  have hψ : ∀ x, ψ x = φ x := fun _ => rfl
  let ν : Measure (Fin n → ℝ) := Measure.map φ μ
  haveI : ν.IsAddHaarMeasure := φ.isAddHaarMeasure_map μ
  have hν : ∀ B : Set E, ν (φ '' B) = μ B := by
    intro B
    have : Measure.map ψ μ (ψ '' B) = μ B := by
      rw [MeasurableEquiv.map_apply, ψ.preimage_image]
    simp [ν, hψ] at this
    exact this

  let ℓ : E →ₗ[ℝ] E := Algebra.lmul ℝ E (u : E)
  have hℓ : ∀ x, ℓ x = (u : E) * x := fun _ => rfl
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (φ : E →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ ℓ ∘ₗ (φ.symm : (Fin n → ℝ) →ₗ[ℝ] E)
  have hdetf : LinearMap.det f = Algebra.norm ℝ (u : E) := by
    rw [Algebra.norm_apply]
    exact LinearMap.det_conj ℓ φ.toLinearEquiv
  have hf : ∀ x : E, f (φ x) = φ (ℓ x) := by
    intro x
    simp [f]

  have key : ∀ s : Set E, μ ((u : Eˣ) • s) = ENNReal.ofReal |Algebra.norm ℝ (u : E)| * μ s := by
    intro s
    have h1 : (u : Eˣ) • s = ℓ '' s := by
      ext x; simp [Set.mem_smul_set, hℓ, Units.smul_def]
    have h2 : φ '' (ℓ '' s) = f '' (φ '' s) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun x _ => (hf x).symm
    rw [h1, ← hν (ℓ '' s), h2, Measure.addHaar_image_linearMap ν f (φ '' s), hdetf, hν]
  have hK0 : μ (K₀ : Set E) ≠ 0 := by
    rw [show μ (K₀ : Set E) = 1 from Measure.addHaarMeasure_self]; exact one_ne_zero
  have hKtop : μ (K₀ : Set E) ≠ ∞ := by
    rw [show μ (K₀ : Set E) = 1 from Measure.addHaarMeasure_self]; exact ENNReal.one_ne_top
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (g := u) hK0 hKtop
    (r := (|Algebra.norm ℝ (u : E)|).toNNReal) (by rw [key]; rfl)
  rw [this]
  exact Real.coe_toNNReal _ (abs_nonneg _)

theorem distribHaarChar_units_map_eq {E F : Type*} [CommRing E] [CommRing F]
    [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalRing E] [IsTopologicalRing F]
    [LocallyCompactSpace E] [LocallyCompactSpace F] [T2Space E] [T2Space F]
    (e : E ≃+* F) (he : Continuous e) (hes : Continuous e.symm) (u : Eˣ) :
    distribHaarChar F (Units.map e.toRingHom.toMonoidHom u) = distribHaarChar E u := by
  classical
  borelize E
  borelize F
  haveI : IsTopologicalAddGroup E := inferInstance
  haveI : IsTopologicalAddGroup F := inferInstance
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts E))
  let μ : Measure E := Measure.addHaarMeasure K₀
  let ea : E ≃+ F := e.toAddEquiv
  let ν : Measure F := Measure.map ea μ
  haveI hν : ν.IsAddHaarMeasure := ea.isAddHaarMeasure_map μ he hes
  let H : E ≃ₜ F := { toEquiv := e.toEquiv, continuous_toFun := he, continuous_invFun := hes }
  let ψ : E ≃ᵐ F := H.toMeasurableEquiv
  have hψ : ∀ x, ψ x = e x := fun _ => rfl
  have hν_apply : ∀ B : Set E, ν (e '' B) = μ B := by
    intro B
    have : Measure.map ψ μ (ψ '' B) = μ B := by
      rw [MeasurableEquiv.map_apply, ψ.preimage_image]
    have h1 : (ψ : E → F) = e := funext hψ
    simpa [ν, ea, h1] using this
  haveI : ν.Regular := Measure.Regular.map H
  set u' := Units.map e.toRingHom.toMonoidHom u with hu'
  have key : ν (u' • (e '' (K₀ : Set E))) = (distribHaarChar E u) * ν (e '' (K₀ : Set E)) := by
    have hset : u' • (e '' (K₀ : Set E)) = e '' ((u : Eˣ) • (K₀ : Set E)) := by
      ext y
      simp only [Set.mem_smul_set, Set.mem_image, hu', Units.smul_def, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨(u : E) * x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨e x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
    rw [hset, hν_apply, hν_apply, distribHaarChar_mul]
  have hK0 : ν (e '' (K₀ : Set E)) ≠ 0 := by
    rw [hν_apply, show μ (K₀ : Set E) = 1 from Measure.addHaarMeasure_self]; exact one_ne_zero
  have hKtop : ν (e '' (K₀ : Set E)) ≠ ∞ := by
    rw [hν_apply, show μ (K₀ : Set E) = 1 from Measure.addHaarMeasure_self]; exact ENNReal.one_ne_top
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) hK0 hKtop key

end ArchModuleDict

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (z : L ⊗[K] InfiniteAdeleRing K) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    ∏ w : InfinitePlace L, ‖AutomorphicForm.archIdent K L z w‖ ^ w.mult = |Algebra.norm ℝ z| := by
  classical
  letI iRK : Algebra ℝ (InfiniteAdeleRing K) :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
      (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
  letI iRE : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
      (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
  show ∏ w : InfinitePlace L, ‖AutomorphicForm.archIdent K L z w‖ ^ w.mult = |Algebra.norm ℝ z|
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensor K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  obtain ⟨hST, hfinK, hfinE, hcalg, hsmul, hnorm, -⟩ :=
    AutomorphicForm.moduleFinite_and_continuousSMul_real_tensor_infiniteAdeleRing_and_continuous_algebraNorm_det K L
  haveI := hfinE
  haveI := hsmul

  have he : Continuous (AutomorphicForm.archIdentEquiv K L) := (AutomorphicForm.archIdentHomeomorph K L).continuous
  have hes : Continuous (AutomorphicForm.archIdentEquiv K L).symm :=
    (AutomorphicForm.archIdentHomeomorph K L).symm.continuous
  by_cases hz : IsUnit z
  · obtain ⟨u, rfl⟩ := hz
    have h1 := ArchModuleDict.distribHaarChar_eq_abs_norm (E := L ⊗[K] InfiniteAdeleRing K) u
    have h2 := ArchModuleDict.distribHaarChar_units_map_eq (AutomorphicForm.archIdentEquiv K L) he hes u
    letI : MeasurableSpace (InfiniteAdeleRing L) := borel _
    haveI : BorelSpace (InfiniteAdeleRing L) := ⟨rfl⟩
    have h3 := NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult L
      (Units.map (AutomorphicForm.archIdentEquiv K L).toRingHom.toMonoidHom u)
    rw [h2, h1] at h3
    rw [h3]
    rfl
  ·
    have hN : Algebra.norm ℝ z = 0 := by
      by_contra h
      apply hz
      rw [Algebra.norm_apply] at h
      let e := LinearMap.equivOfDetNeZero (Algebra.lmul ℝ (L ⊗[K] InfiniteAdeleRing K) z) h
      have hee : ∀ y, e y = z * y := fun _ => rfl
      obtain ⟨y, hy⟩ : ∃ y, z * y = 1 := ⟨e.symm 1, by rw [← hee, LinearEquiv.apply_symm_apply]⟩
      exact ⟨⟨z, y, hy, mul_eq_one_comm.mp hy⟩, rfl⟩
    have hz' : ¬ IsUnit (AutomorphicForm.archIdent K L z) := by
      intro h
      apply hz
      have := h.map (AutomorphicForm.archIdentEquiv K L).symm
      rwa [← AutomorphicForm.archIdentEquiv_apply, RingEquiv.symm_apply_apply] at this
    have := NumberField.InfiniteAdeleRing.norm_eq_zero_of_not_isUnit hz'
    rw [NumberField.InfiniteAdeleRing.norm_def] at this
    rw [this, hN, abs_zero]

end S_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real
end P2MW
export P2MW.S_AutomorphicForm_prod_norm_archIdent_pow_mult_eq_abs_algebraNorm_real (solution)
