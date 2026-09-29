-- Prove2me | solution 1 for AutomorphicForm.exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/40942c22-77a1-5768-9139-a773c637efc5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport

set_option autoImplicit false

open NumberField MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

namespace TrivialTwist

section Congruence

variable {R R' : Type*} [CommRing R] [CommRing R'] [TopologicalSpace R] [TopologicalSpace R']
  [IsTopologicalRing R] [IsTopologicalRing R']

private theorem continuous_glMap (f : R →+* R') (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  have hmap : Continuous fun m : Matrix (Fin 2) (Fin 2) R => m.map f := continuous_id.matrix_map hf
  refine Units.continuous_iff.mpr ⟨hmap.comp Units.continuous_val, ?_⟩
  have h : (fun g : GL (Fin 2) R => ((Matrix.GeneralLinearGroup.map (n := Fin 2) f g)⁻¹ : GL (Fin 2) R').val)
      = fun g : GL (Fin 2) R => ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f := by
    funext g
    rw [← map_inv]
    rfl
  rw [h]
  exact hmap.comp (Units.continuous_val.comp continuous_inv)

private noncomputable def glCongr (e : R ≃+* R') (he : Continuous e) (he' : Continuous e.symm) :
    GL (Fin 2) R ≃ₜ* GL (Fin 2) R' where
  toFun := Matrix.GeneralLinearGroup.map (n := Fin 2) e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map (n := Fin 2) e.symm.toRingHom
  left_inv _ := Units.ext (Matrix.ext fun _ _ => e.symm_apply_apply _)
  right_inv _ := Units.ext (Matrix.ext fun _ _ => e.apply_symm_apply _)
  map_mul' := map_mul _
  continuous_toFun := continuous_glMap e.toRingHom he
  continuous_invFun := continuous_glMap e.symm.toRingHom he'

omit [TopologicalSpace R] [TopologicalSpace R'] [IsTopologicalRing R] [IsTopologicalRing R'] in

private theorem isRegularSemisimple_map (f : R →+* R') {g : GL (Fin 2) R}
    (hg : AutomorphicForm.IsRegularSemisimple g) :
    AutomorphicForm.IsRegularSemisimple (Matrix.GeneralLinearGroup.map (n := Fin 2) f g) := by
  have hm : ((Matrix.GeneralLinearGroup.map (n := Fin 2) f g : GL (Fin 2) R') : Matrix (Fin 2) (Fin 2) R')
      = ((g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).map f := rfl
  have h := hg.map f
  simp only [AutomorphicForm.IsRegularSemisimple, Matrix.trace_fin_two, Matrix.det_fin_two, map_sub, map_mul,
    map_pow, map_add, map_ofNat] at h
  simpa only [AutomorphicForm.IsRegularSemisimple, hm, Matrix.trace_fin_two, Matrix.det_fin_two,
    Matrix.map_apply] using h

end Congruence

section Carrier

variable (K : Type) [Field K] [NumberField K]

private noncomputable def lidEquiv : (K ⊗[K] InfiniteAdeleRing K) ≃+* InfiniteAdeleRing K :=
  (Algebra.TensorProduct.lid K (InfiniteAdeleRing K)).toRingEquiv

private theorem lidEquiv_symm_apply (a : InfiniteAdeleRing K) :
    (lidEquiv K).symm a = algebraMap (InfiniteAdeleRing K) (K ⊗[K] InfiniteAdeleRing K) a := by
  simp [lidEquiv, Algebra.TensorProduct.algebraMap_apply]

private theorem continuous_lidEquiv : Continuous (lidEquiv K) := by
  refine IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing K) (lidEquiv K).toRingHom ?_
  have h : ⇑((lidEquiv K).toRingHom.comp (algebraMap (InfiniteAdeleRing K) (K ⊗[K] InfiniteAdeleRing K)))
      = fun a : InfiniteAdeleRing K => a := by
    funext a
    simp [lidEquiv, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact continuous_id

private theorem continuous_lidEquiv_symm : Continuous (lidEquiv K).symm := by
  have h : ⇑(lidEquiv K).symm = algebraMap (InfiniteAdeleRing K) (K ⊗[K] InfiniteAdeleRing K) :=
    funext (lidEquiv_symm_apply K)
  rw [h]
  exact continuous_algebraMap (InfiniteAdeleRing K) (K ⊗[K] InfiniteAdeleRing K)

private noncomputable def glLid :
    GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K) ≃ₜ* GL (Fin 2) (InfiniteAdeleRing K) :=
  haveI : IsTopologicalRing (K ⊗[K] InfiniteAdeleRing K) :=
    AutomorphicForm.isTopologicalRing_tensor K K (InfiniteAdeleRing K)
  glCongr (lidEquiv K) (continuous_lidEquiv K) (continuous_lidEquiv_symm K)

private theorem sigmaGL_refl (x : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) :
    AutomorphicForm.sigmaGL K K (InfiniteAdeleRing K) AlgEquiv.refl x = x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp [AutomorphicForm.sigmaGL, AutomorphicForm.sigmaTensor]

private theorem normString_refl (δ : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) :
    AutomorphicForm.normString K K (InfiniteAdeleRing K) AlgEquiv.refl δ = δ := by
  simp [AutomorphicForm.normString, Module.finrank_self]

private theorem twistedCentralizer_refl_eq (γ : GL (Fin 2) (InfiniteAdeleRing K)) :
    AutomorphicForm.twistedCentralizer K K (InfiniteAdeleRing K) AlgEquiv.refl ((glLid K).symm γ)
      = (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))).map
          (glLid K).symm.toMulEquiv.toMonoidHom := by
  ext t
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, AutomorphicForm.twistedCentralizer,
    AutomorphicForm.mem_sigmaCentralizer_iff, sigmaGL_refl, mul_inv_eq_iff_eq_mul, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h' := congrArg (glLid K) h
    have h__af := h'.symm
    simp [map_mul] at h__af
    exact h__af
  · intro h
    have h' := congrArg (glLid K).symm h
    simpa [map_mul] using h'.symm

end Carrier

end TrivialTwist

open TrivialTwist in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ]
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : HasCompactSupport f) :
    ∃ w : GL (Fin 2) (InfiniteAdeleRing K) → ℝ,
      AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K) γ τ f w ∧ Continuous w := by
  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf (InfiniteAdeleRing K)
  haveI : IsTopologicalRing (K ⊗[K] InfiniteAdeleRing K) :=
    AutomorphicForm.isTopologicalRing_tensor K K (InfiniteAdeleRing K)
  set ι := glLid K
  set δ : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K) := ι.symm γ
  set T := Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))
  set T' := AutomorphicForm.twistedCentralizer K K (InfiniteAdeleRing K) AlgEquiv.refl δ
  letI : MeasurableSpace T := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ
  letI : MeasurableSpace T' := AutomorphicForm.twistedCentralizerBorel K K (InfiniteAdeleRing K) AlgEquiv.refl δ
  haveI : BorelSpace T := ⟨rfl⟩
  haveI : BorelSpace T' := ⟨rfl⟩
  have hT' : T' = T.map ι.symm.toMulEquiv.toMonoidHom := twistedCentralizer_refl_eq K γ
  let j : T ≃* T' := (MulEquiv.subgroupMap ι.symm.toMulEquiv T).trans (MulEquiv.subgroupCongr hT'.symm)
  have hj_coe : ∀ t : T,
      ((j t : T') : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) = ι.symm (t : GL (Fin 2) (InfiniteAdeleRing K)) :=
    fun _ => rfl
  have hj_symm_coe : ∀ t' : T',
      ((j.symm t' : T) : GL (Fin 2) (InfiniteAdeleRing K)) = ι (t' : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) := by
    intro t'
    have h := hj_coe (j.symm t')
    rw [j.apply_symm_apply] at h
    rw [h, ι.apply_symm_apply]
  have hj_cont : Continuous j := by
    refine continuous_induced_rng.2 ?_
    have h : (fun t : T => ((j t : T') : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)))
        = fun t : T => ι.symm (t : GL (Fin 2) (InfiniteAdeleRing K)) := funext hj_coe
    show Continuous fun t : T => ((j t : T') : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K))
    rw [h]
    exact ι.symm.continuous.comp continuous_subtype_val
  have hj_symm_cont : Continuous j.symm := by
    refine continuous_induced_rng.2 ?_
    have h : (fun t' : T' => ((j.symm t' : T) : GL (Fin 2) (InfiniteAdeleRing K)))
        = fun t' : T' => ι (t' : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) := funext hj_symm_coe
    show Continuous fun t' : T' => ((j.symm t' : T) : GL (Fin 2) (InfiniteAdeleRing K))
    rw [h]
    exact ι.continuous.comp continuous_subtype_val
  let τ' : Measure T' := Measure.map j τ
  haveI : τ'.IsHaarMeasure := j.isHaarMeasure_map τ hj_cont hj_symm_cont
  have hδ : AutomorphicForm.IsRegularSemisimple
      (AutomorphicForm.normString K K (InfiniteAdeleRing K) AlgEquiv.refl δ) := by
    rw [normString_refl]
    exact isRegularSemisimple_map (lidEquiv K).symm.toRingHom hγ
  obtain ⟨w', hw', hw'c⟩ :=
    AutomorphicForm.exists_isTwistedSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_normString_of_hasCompactSupport
      K K AlgEquiv.refl δ hδ τ' (f ∘ ι) (hf.comp_homeomorph ι.toHomeomorph)
  unfold AutomorphicForm.IsTwistedSectionFnOn at hw'
  obtain ⟨hw'0, -, hw'supp, hw'norm⟩ := hw'
  refine ⟨fun x => w' (ι.symm x), ?_, hw'c.comp ι.symm.continuous⟩
  unfold AutomorphicForm.IsSectionFnOn
  refine ⟨fun x => hw'0 _, ?_, ?_, ?_⟩
  · exact (hw'c.comp ι.symm.continuous).measurable
  · exact hw'supp.comp_homeomorph ι.symm.toHomeomorph
  · intro x hx
    have hx' : (f ∘ ι)
        ((ι.symm x)⁻¹ * δ * AutomorphicForm.sigmaGL K K (InfiniteAdeleRing K) AlgEquiv.refl (ι.symm x)) ≠ 0 := by
      rw [sigmaGL_refl]
      have h : (ι.symm x)⁻¹ * δ * ι.symm x = ι.symm (x⁻¹ * γ * x) := by
        simp only [δ, map_mul, map_inv]
      rw [h]
      simpa using hx
    have hnorm := hw'norm (ι.symm x) hx'
    have hmap : ∫ t' : T', w' ((t' : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) * ι.symm x) ∂τ'
        = ∫ t : T, w' (((j t : T') : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) * ι.symm x) ∂τ :=
      integral_map hj_cont.measurable.aemeasurable
        (hw'c.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
    have hkey : (fun t : T => w' (ι.symm ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x)))
        = fun t : T => w' (((j t : T') : GL (Fin 2) (K ⊗[K] InfiniteAdeleRing K)) * ι.symm x) := by
      funext t
      rw [hj_coe, map_mul]
    show ∫ t : T, w' (ι.symm ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x)) ∂τ = 1
    rw [hkey, ← hmap]
    exact hnorm

end S_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
end P2MW
export P2MW.S_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport (solution)
