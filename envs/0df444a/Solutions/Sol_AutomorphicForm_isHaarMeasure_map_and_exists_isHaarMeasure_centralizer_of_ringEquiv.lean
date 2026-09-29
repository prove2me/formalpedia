-- Prove2me | solution 1 for AutomorphicForm.isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/472d1bb7-33cd-5aa1-a75e-6f011063a1d1

import Mathlib.Topology.Algebra.Group.Units
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel"
namespace HaarTransportRingEquivSol
p2m_open "AutomorphicForm"

open MeasureTheory

section Generic

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_mem_centralizer (e : G ≃ₜ* H) (γ : G) (t : Subgroup.centralizer ({γ} : Set G)) :
    e (t : G) ∈ Subgroup.centralizer ({e γ} : Set H) := by
  have ht : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have h : e ((t : G) * γ) = e (γ * t) := congrArg e ht
  rw [map_mul, map_mul] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 h

theorem symm_map_mem_centralizer (e : G ≃ₜ* H) (γ : G) (t' : Subgroup.centralizer ({e γ} : Set H)) :
    e.symm (t' : H) ∈ Subgroup.centralizer ({γ} : Set G) := by
  have ht : (t' : H) * e γ = e γ * t' := Subgroup.mem_centralizer_singleton_iff.1 t'.2
  have h : e.symm ((t' : H) * e γ) = e.symm (e γ * t') := congrArg e.symm ht
  rw [map_mul, map_mul, e.symm_apply_apply] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 h

def centralizerCongr (e : G ≃ₜ* H) (γ : G) :
    Subgroup.centralizer ({γ} : Set G) ≃ₜ* Subgroup.centralizer ({e γ} : Set H) where
  toFun t := ⟨e t, map_mem_centralizer e γ t⟩
  invFun t' := ⟨e.symm t', symm_map_mem_centralizer e γ t'⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk (map_mem_centralizer e γ)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk (symm_map_mem_centralizer e γ)

@[scoped simp] theorem coe_centralizerCongr_apply (e : G ≃ₜ* H) (γ : G)
    (t : Subgroup.centralizer ({γ} : Set G)) : ((centralizerCongr e γ t : _) : H) = e t := rfl

@[scoped simp] theorem coe_centralizerCongr_symm_apply (e : G ≃ₜ* H) (γ : G)
    (t' : Subgroup.centralizer ({e γ} : Set H)) :
    (((centralizerCongr e γ).symm t' : _) : G) = e.symm t' := rfl

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]

theorem exists_isHaarMeasure_centralizer_map_eq (e : G ≃ₜ* H) (γ : G) (γ' : H) (hγ : e γ = γ')
    [MeasurableSpace (Subgroup.centralizer ({γ} : Set G))]
    [BorelSpace (Subgroup.centralizer ({γ} : Set G))]
    [MeasurableSpace (Subgroup.centralizer ({γ'} : Set H))]
    [BorelSpace (Subgroup.centralizer ({γ'} : Set H))]
    (τ' : Measure (Subgroup.centralizer ({γ'} : Set H))) [τ'.IsHaarMeasure] :
    ∃ τ : Measure (Subgroup.centralizer ({γ} : Set G)), τ.IsHaarMeasure ∧
      Measure.map (fun t' : Subgroup.centralizer ({γ'} : Set H) => (t' : H)) τ' =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set G) => e (t : G)) τ := by
  subst hγ
  refine ⟨Measure.map (centralizerCongr e γ).symm τ',
    (centralizerCongr e γ).symm.isHaarMeasure_map τ', ?_⟩
  have hm1 : Measurable (fun t : Subgroup.centralizer ({γ} : Set G) => e (t : G)) :=
    (e.continuous.comp continuous_subtype_val).measurable
  have hm2 : Measurable
      ((centralizerCongr e γ).symm : Subgroup.centralizer ({e γ} : Set H) → Subgroup.centralizer ({γ} : Set G)) :=
    (centralizerCongr e γ).symm.continuous.measurable
  rw [Measure.map_map hm1 hm2]
  congr 1
  funext t'
  simp

end Generic

section GLTwo

variable {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

def matEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    Matrix (Fin 2) (Fin 2) A ≃ₜ* Matrix (Fin 2) (Fin 2) B :=
  { e.mapMatrix.toMulEquiv with
    continuous_toFun :=
      (continuous_id.matrix_map he : Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map e)
    continuous_invFun :=
      (continuous_id.matrix_map he' : Continuous fun m : Matrix (Fin 2) (Fin 2) B => m.map e.symm) }

def glEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) : GL (Fin 2) A ≃ₜ* GL (Fin 2) B :=
  Units.mapContinuousMulEquiv (matEquiv e he he')

omit [IsTopologicalRing A] [IsTopologicalRing B] in
theorem glEquiv_apply (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) (g : GL (Fin 2) A) :
    glEquiv e he he' g = Matrix.GeneralLinearGroup.map e.toRingHom g := by
  ext i j
  rfl

omit [IsTopologicalRing A] [IsTopologicalRing B] in
theorem coe_glEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    (⇑(glEquiv e he he') : GL (Fin 2) A → GL (Fin 2) B) = Matrix.GeneralLinearGroup.map e.toRingHom :=
  funext (glEquiv_apply e he he')

attribute [local instance 10000] AutomorphicForm.glBorelOf AutomorphicForm.centralizerBorel

theorem borelSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

theorem borelSpace_centralizer (R : Type) [CommRing R] [TopologicalSpace R] (γ : GL (Fin 2) R) :
    BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) R))) := ⟨rfl⟩

attribute [local instance] borelSpace_gl borelSpace_centralizer

theorem main (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : Measure (GL (Fin 2) A)) (hμ : μ.IsHaarMeasure) (γ : GL (Fin 2) A)
    (τ' : Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B))))
    (hτ' : τ'.IsHaarMeasure) :
    (Measure.map (Matrix.GeneralLinearGroup.map e.toRingHom) μ).IsHaarMeasure ∧
      ∃ τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))), τ.IsHaarMeasure ∧
        Measure.map (fun t : Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
          Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
            Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ := by
  haveI := hμ
  haveI := hτ'
  refine ⟨?_, ?_⟩
  · rw [← coe_glEquiv e he he']
    exact (glEquiv e he he').isHaarMeasure_map μ
  · obtain ⟨τ, hτ, hmap⟩ := exists_isHaarMeasure_centralizer_map_eq (glEquiv e he he') γ
      (Matrix.GeneralLinearGroup.map e.toRingHom γ) (glEquiv_apply e he he' γ) τ'
    refine ⟨τ, hτ, hmap.trans ?_⟩
    exact congrArg (fun F : GL (Fin 2) A → GL (Fin 2) B =>
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => F (t : GL (Fin 2) A)) τ)
      (coe_glEquiv e he he')

end GLTwo

end AutomorphicForm.HaarTransportRingEquivSol
p2m_reactivate "P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.AutomorphicForm P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.AutomorphicForm.HaarTransportRingEquivSol"
p2m_reactivate "P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.AutomorphicForm P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.AutomorphicForm.HaarTransportRingEquivSol"

p2m_open "MeasureTheory AutomorphicForm P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm)
    (μ : @Measure (GL (Fin 2) A) (glBorelOf A)) (hμ : @Measure.IsHaarMeasure _ _ _ (glBorelOf A) μ)
    (γ : GL (Fin 2) A)
    (τ' : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)))
      (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ)) τ') :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf B)
        (@Measure.map _ _ (glBorelOf A) (glBorelOf B) (Matrix.GeneralLinearGroup.map e.toRingHom) μ) ∧
      ∃ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel A γ) τ ∧
        (letI := glBorelOf B; letI := centralizerBorel A γ;
          letI := centralizerBorel B (Matrix.GeneralLinearGroup.map e.toRingHom γ);
          Measure.map (fun t : Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) B)) => (t : GL (Fin 2) B)) τ' =
            Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
              Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) :=
  AutomorphicForm.HaarTransportRingEquivSol.main e he he' μ hμ γ τ' hτ'

end S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv
end P2MW
export P2MW.S_AutomorphicForm_isHaarMeasure_map_and_exists_isHaarMeasure_centralizer_of_ringEquiv (solution)
