-- Prove2me | solution 1 for AutomorphicForm.isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/bc1dea74-e3ca-54d9-9a3a-b707d371a93d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel IsSectionFnOn IsOrbitalIntegralOn"
namespace OrbitalTransportRingEquivSol
p2m_open "AutomorphicForm"

open MeasureTheory

section GLTwo

variable {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

omit [IsTopologicalRing A] [IsTopologicalRing B] in
theorem continuous_glMap (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
theorem map_symm_map (e : A ≃+* B) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.map e.symm.toRingHom (Matrix.GeneralLinearGroup.map e.toRingHom g) = g := by
  ext i j
  simp

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in
theorem map_map_symm (e : A ≃+* B) (g' : GL (Fin 2) B) :
    Matrix.GeneralLinearGroup.map e.toRingHom (Matrix.GeneralLinearGroup.map e.symm.toRingHom g') = g' := by
  ext i j
  simp

omit [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace B] [IsTopologicalRing B] in

theorem conj_map (e : A ≃+* B) (γ x : GL (Fin 2) A) :
    (Matrix.GeneralLinearGroup.map e.toRingHom x)⁻¹ * Matrix.GeneralLinearGroup.map e.toRingHom γ *
        Matrix.GeneralLinearGroup.map e.toRingHom x =
      Matrix.GeneralLinearGroup.map e.toRingHom (x⁻¹ * γ * x) := by
  rw [map_mul, map_mul, map_inv]

def glHomeo (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) : GL (Fin 2) A ≃ₜ GL (Fin 2) B where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv := map_symm_map e
  right_inv := map_map_symm e
  continuous_toFun := continuous_glMap e.toRingHom he
  continuous_invFun := continuous_glMap e.symm.toRingHom he'

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel

theorem borelSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

theorem borelSpace_centralizer (R : Type) [CommRing R] [TopologicalSpace R] (γ : GL (Fin 2) R) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) := ⟨rfl⟩

attribute [local instance] borelSpace_gl borelSpace_centralizer

omit [IsTopologicalRing A] in

theorem isSectionFnOn_comp (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (γ : GL (Fin 2) A) (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))))
    (τ' : Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B))))
    (hτ : Measure.map (fun t : Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
        Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (f : GL (Fin 2) A → ℂ) (w : GL (Fin 2) A → ℝ) (hw : IsSectionFnOn A γ τ f w) :
    IsSectionFnOn B (Matrix.GeneralLinearGroup.map e.toRingHom γ) τ'
      (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) (w ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) := by
  obtain ⟨hw0, hwm, hws, hw1⟩ := hw
  have hcont : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom) := continuous_glMap _ he
  have hcont' : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom) :=
    continuous_glMap _ he'
  refine ⟨fun x => hw0 _, hwm.comp hcont'.measurable, hws.comp_homeomorph (glHomeo e he he').symm, ?_⟩
  intro x' hx'
  obtain ⟨x, rfl⟩ : ∃ x, Matrix.GeneralLinearGroup.map e.toRingHom x = x' :=
    ⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom x', map_map_symm e x'⟩
  have hne : f (x⁻¹ * γ * x) ≠ 0 := by
    simpa only [Function.comp_apply, conj_map, map_symm_map] using hx'

  set g : GL (Fin 2) B → ℝ := fun y =>
    w (Matrix.GeneralLinearGroup.map e.symm.toRingHom (y * Matrix.GeneralLinearGroup.map e.toRingHom x)) with hg_def
  have hg : Measurable g := hwm.comp (hcont'.comp (continuous_id.mul continuous_const)).measurable
  have hval : Measurable (fun t' : Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t' : GL (Fin 2) B)) :=
    continuous_subtype_val.measurable
  have hval' : Measurable (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
      Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) :=
    (hcont.comp continuous_subtype_val).measurable
  calc ∫ t', (w ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom)
          ((t' : GL (Fin 2) B) * Matrix.GeneralLinearGroup.map e.toRingHom x) ∂τ'
      = ∫ t', g (t' : GL (Fin 2) B) ∂τ' := rfl
    _ = ∫ y, g y ∂(Measure.map (fun t' : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t' : GL (Fin 2) B)) τ') :=
        (integral_map hval.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂(Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) := by rw [hτ]
    _ = ∫ t, g (Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) ∂τ :=
        integral_map hval'.aemeasurable hg.aestronglyMeasurable
    _ = ∫ t, w ((t : GL (Fin 2) A) * x) ∂τ := by
        congr 1
        funext t
        simp only [hg_def]
        rw [← map_mul, map_symm_map]
    _ = 1 := hw1 x hne

omit [IsTopologicalRing A] in

theorem main (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : Measure (GL (Fin 2) A)) (γ : GL (Fin 2) A)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))))
    (τ' : Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B))))
    (hτ : Measure.map (fun t : Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
        Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (f : GL (Fin 2) A → ℂ) (I : ℂ) (h : IsOrbitalIntegralOn A μ γ τ f I) :
    IsOrbitalIntegralOn B (Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
      (Matrix.GeneralLinearGroup.map e.toRingHom γ) τ'
      (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I := by
  obtain ⟨w, hw, hI⟩ := h
  refine ⟨w ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom,
    isSectionFnOn_comp e he he' γ τ τ' hτ f w hw, ?_⟩
  have hme : MeasurableEmbedding (Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom) :=
    (glHomeo e he he').measurableEmbedding
  rw [hI]
  refine ((hme.integral_map _).trans ?_).symm
  congr 1
  funext x
  simp only [Function.comp_apply, conj_map, map_symm_map]

end GLTwo

end AutomorphicForm.OrbitalTransportRingEquivSol

end

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (γ : GL (Fin 2) A)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)))
      (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hτ : letI := glBorelOf B; letI := centralizerBorel A γ;
      letI := centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ);
      Measure.map (fun t : Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (f : GL (Fin 2) A → ℂ) (I : ℂ) (h : IsOrbitalIntegralOn A μ γ τ f I) :
    IsOrbitalIntegralOn B
      (@Measure.map _ _ (glBorelOf A) (glBorelOf B) (Matrix.GeneralLinearGroup.map e.toRingHom) μ)
      (Matrix.GeneralLinearGroup.map e.toRingHom γ) τ'
      (f ∘ Matrix.GeneralLinearGroup.map e.symm.toRingHom) I :=
  AutomorphicForm.OrbitalTransportRingEquivSol.main e he he' μ γ τ τ' hτ f I h

end S_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv
end P2MW
export P2MW.S_AutomorphicForm_isOrbitalIntegralOn_map_generalLinearGroup_map_of_ringEquiv (solution)
