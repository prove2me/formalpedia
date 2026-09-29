-- Prove2me | solution 1 for AutomorphicForm.ideleNorm_det_sigmaAdelicAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9f6a4904-f6aa-5b40-a6ec-fd38c4db13d2

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ideleNorm_det_sigmaAdelicAct

set_option autoImplicit false

open NumberField

namespace IdeleNormDetGalSol

open MeasureTheory MeasureTheory.Measure
open scoped Pointwise

private theorem distribHaarChar_map_ringEquiv {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A] [ContinuousConstSMul Aˣ A]
    (a : A ≃+* A) (ha : Continuous a) (ha' : Continuous a.symm) (u : Aˣ) :
    distribHaarChar A (Units.map a.toRingHom.toMonoidHom u) = distribHaarChar A u := by
  letI : MeasurableSpace A := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts A) := inferInstance
  set μ : Measure A := addHaarMeasure K with hμ
  set ν : Measure A := μ.map a.symm with hν
  haveI : ν.IsAddHaarMeasure := a.symm.toAddEquiv.isAddHaarMeasure_map μ ha' ha
  haveI : ν.Regular := Regular.map (Homeomorph.mk a.symm.toEquiv ha' ha)
  have hmeas : Measurable (a.symm : A → A) := ha'.measurable
  have hνapp : ∀ s : Set A, MeasurableSet s → ν s = μ (a '' s) := by
    intro s hs
    rw [hν, Measure.map_apply hmeas hs]
    congr 1
    ext x
    constructor
    · intro hx
      exact ⟨a.symm x, hx, a.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hK0 : μ K ≠ 0 := by
    rw [hμ, addHaarMeasure_self]; exact one_ne_zero
  have hKtop : μ K ≠ ⊤ := by
    rw [hμ, addHaarMeasure_self]; exact ENNReal.one_ne_top
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hK0 hKtop ?_
  set T : Set A := a.symm '' K with hT
  have hTc : IsCompact T := K.isCompact.image ha'
  have haT : a '' T = K := by
    rw [hT, ← Set.image_comp]
    simp
  have hset : (Units.map a.toRingHom.toMonoidHom u) • (K : Set A) = a '' (u • T) := by
    rw [← haT]
    ext x
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨u • t, ⟨t, ht, rfl⟩, by simp [Units.smul_def, map_mul]⟩
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨a t, ⟨t, ht, rfl⟩, by simp [Units.smul_def, map_mul]⟩
  rw [hset, ← hνapp _ (hTc.smul u).measurableSet, ← distribHaarChar_mul ν u T,
    hνapp _ hTc.measurableSet, haT]

private theorem det_sigmaAdelicAct (F E : Type) [Field F] [Field E] [NumberField E] [Algebra F E]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E) (σ : E ≃ₐ[F] E)
    (x : Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 E) E)) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.sigmaAdelicAct F E D σ x) =
      Units.map (D.act σ).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det x) := by
  ext
  simp [AutomorphicForm.sigmaAdelicAct, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]

private theorem continuous_act_symm (F E : Type) [Field F] [Field E] [NumberField E]
    [Algebra F E] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E) (σ : E ≃ₐ[F] E) :
    Continuous (D.act σ).symm := by
  have h := D.continuous_act σ⁻¹
  rw [map_inv] at h
  exact h

end IdeleNormDetGalSol

open AutomorphicForm in
theorem solution (F E : Type) [Field F] [Field E]
    [NumberField E] [Algebra F E] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 E) F E)
    (σ : E ≃ₐ[F] E) :
    ∀ x, NumberField.TateGlobal.ideleNorm E
        (Matrix.GeneralLinearGroup.det (sigmaAdelicAct F E D σ x)) =
      NumberField.TateGlobal.ideleNorm E (Matrix.GeneralLinearGroup.det x) := by
  intro x
  simp only [NumberField.TateGlobal.ideleNorm, IdeleNormDetGalSol.det_sigmaAdelicAct,
    IdeleNormDetGalSol.distribHaarChar_map_ringEquiv (D.act σ) (D.continuous_act σ)
      (IdeleNormDetGalSol.continuous_act_symm F E D σ)]

end S_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
end P2MW
export P2MW.S_AutomorphicForm_ideleNorm_det_sigmaAdelicAct (solution)
