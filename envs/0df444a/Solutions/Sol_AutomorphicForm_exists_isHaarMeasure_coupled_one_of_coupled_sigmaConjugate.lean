-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2662cbb0-7f2e-566b-b699-d31ad8300a01

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn Coupled mem_sigmaCentralizer_iff"
p2m_open "AutomorphicForm"

namespace TwistedCentralizerConj

section Algebra

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

private theorem conj_mem_twistedCentralizer (δ x : GL (Fin 2) (L ⊗[K] A)) {t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ twistedCentralizer K L A σ δ) :
    x⁻¹ * t * x ∈ twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  calc x⁻¹ * t * x * (x⁻¹ * δ * sigmaGL K L A σ x) * (sigmaGL K L A σ (x⁻¹ * t * x))⁻¹
      = x⁻¹ * (t * δ * (sigmaGL K L A σ t)⁻¹) * sigmaGL K L A σ x := by
        simp only [map_mul, map_inv]; group
    _ = x⁻¹ * δ * sigmaGL K L A σ x := by rw [ht]

private theorem conj_inv_mem_twistedCentralizer (δ x : GL (Fin 2) (L ⊗[K] A)) {s : GL (Fin 2) (L ⊗[K] A)}
    (hs : s ∈ twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) :
    x * s * x⁻¹ ∈ twistedCentralizer K L A σ δ := by
  rw [mem_sigmaCentralizer_iff] at hs ⊢
  calc x * s * x⁻¹ * δ * (sigmaGL K L A σ (x * s * x⁻¹))⁻¹
      = x * (s * (x⁻¹ * δ * sigmaGL K L A σ x) * (sigmaGL K L A σ s)⁻¹) * (sigmaGL K L A σ x)⁻¹ := by
        simp only [map_mul, map_inv]; group
    _ = x * (x⁻¹ * δ * sigmaGL K L A σ x) * (sigmaGL K L A σ x)⁻¹ := by rw [hs]
    _ = δ := by group

private def twistedConj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ → twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) :=
  fun t => ⟨x⁻¹ * t * x, conj_mem_twistedCentralizer K L A σ δ x t.2⟩

@[scoped simp] private theorem coe_twistedConj_apply (δ x : GL (Fin 2) (L ⊗[K] A)) (t : twistedCentralizer K L A σ δ) :
    ((twistedConj K L A σ δ x t : twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) :
      GL (Fin 2) (L ⊗[K] A)) = x⁻¹ * t * x :=
  rfl

private def twistedConjEquiv (δ x : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≃* twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) where
  toFun := twistedConj K L A σ δ x
  invFun s := ⟨x * s * x⁻¹, conj_inv_mem_twistedCentralizer K L A σ δ x s.2⟩
  left_inv t := Subtype.ext (show x * (x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x) * x⁻¹ = t by group)
  right_inv s := Subtype.ext (show x⁻¹ * (x * (s : GL (Fin 2) (L ⊗[K] A)) * x⁻¹) * x = s by group)
  map_mul' s t := Subtype.ext
    (show x⁻¹ * ((s : GL (Fin 2) (L ⊗[K] A)) * t) * x
        = x⁻¹ * (s : GL (Fin 2) (L ⊗[K] A)) * x * (x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x) by group)

private theorem coe_twistedConjEquiv (δ x : GL (Fin 2) (L ⊗[K] A)) :
    ⇑(twistedConjEquiv K L A σ δ x) = twistedConj K L A σ δ x :=
  rfl

private theorem coe_twistedConjEquiv_symm_apply (δ x : GL (Fin 2) (L ⊗[K] A))
    (s : twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) :
    (((twistedConjEquiv K L A σ δ x).symm s : twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A))
      = x * s * x⁻¹ :=
  rfl

end Algebra

section Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

private theorem continuous_twistedConj (δ x : GL (Fin 2) (L ⊗[K] A)) : Continuous (twistedConj K L A σ δ x) := by
  haveI := isTopologicalGroup_tensorGL K L A
  exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

private theorem continuous_twistedConjEquiv (δ x : GL (Fin 2) (L ⊗[K] A)) :
    Continuous (twistedConjEquiv K L A σ δ x) :=
  continuous_twistedConj K L A σ δ x

private theorem continuous_twistedConjEquiv_symm (δ x : GL (Fin 2) (L ⊗[K] A)) :
    Continuous (twistedConjEquiv K L A σ δ x).symm := by
  haveI := isTopologicalGroup_tensorGL K L A
  refine continuous_induced_rng.2 ?_
  show Continuous fun s : twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) =>
    x * (s : GL (Fin 2) (L ⊗[K] A)) * x⁻¹
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private theorem measurable_twistedConj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    @Measurable _ _ (twistedCentralizerBorel K L A σ δ)
      (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) (twistedConj K L A σ δ x) := by
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) := ⟨rfl⟩
  exact (continuous_twistedConj K L A σ δ x).measurable

private def twistedConjMeasurableEquiv (δ x : GL (Fin 2) (L ⊗[K] A)) :
    @MeasurableEquiv (twistedCentralizer K L A σ δ)
      (twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x))
      (twistedCentralizerBorel K L A σ δ) (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) := by
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) := ⟨rfl⟩
  exact
    { twistedConjEquiv K L A σ δ x with
      measurable_toFun := (continuous_twistedConjEquiv K L A σ δ x).measurable
      measurable_invFun := (continuous_twistedConjEquiv_symm K L A σ δ x).measurable }

private theorem coe_twistedConjMeasurableEquiv (δ x : GL (Fin 2) (L ⊗[K] A)) :
    ⇑(twistedConjMeasurableEquiv K L A σ δ x) = twistedConj K L A σ δ x :=
  rfl

private theorem measurableEmbedding_twistedConj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    @MeasurableEmbedding _ _ (twistedCentralizerBorel K L A σ δ)
      (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) (twistedConj K L A σ δ x) := by
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  rw [← coe_twistedConjMeasurableEquiv]
  exact (twistedConjMeasurableEquiv K L A σ δ x).measurableEmbedding

end Topology

end TwistedCentralizerConj
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn Coupled mem_sigmaCentralizer_iff"
p2m_open "AutomorphicForm"

namespace TwistedCentralizerConj

section Transport

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

private theorem isHaarMeasure_map_twistedConj (δ x : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x))
      (@Measure.map _ _ (twistedCentralizerBorel K L A σ δ)
        (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) (twistedConj K L A σ δ x) τ') := by
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := hτ'
  rw [← coe_twistedConjEquiv]
  exact MulEquiv.isHaarMeasure_map τ' (twistedConjEquiv K L A σ δ x) (continuous_twistedConjEquiv K L A σ δ x)
    (continuous_twistedConjEquiv_symm K L A σ δ x)

private theorem measurable_conj_one_subtype_val (δ x : GL (Fin 2) (L ⊗[K] A)) :
    @Measurable _ _ (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) (glBorelOf (L ⊗[K] A))
      fun t : twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x) =>
        (1 : GL (Fin 2) (L ⊗[K] A))⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * 1 := by
  letI := glBorelOf (L ⊗[K] A)
  letI := twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) := ⟨rfl⟩
  haveI := isTopologicalGroup_tensorGL K L A
  exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable

private theorem coupled_one_map_twistedConj (γ : GL (Fin 2) A) (δ x : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hC : Coupled K L A σ γ δ x τ τ') :
    Coupled K L A σ γ (x⁻¹ * δ * sigmaGL K L A σ x) 1 τ
      (@Measure.map _ _ (twistedCentralizerBorel K L A σ δ)
        (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) (twistedConj K L A σ δ x) τ') := by
  letI := glBorelOf (L ⊗[K] A)
  letI := centralizerBorel A γ
  letI := twistedCentralizerBorel K L A σ δ
  letI := twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  unfold Coupled at hC ⊢
  rw [Measure.map_map (measurable_conj_one_subtype_val K L A σ δ x) (measurable_twistedConj K L A σ δ x)]
  refine Eq.trans ?_ hC
  congr 1
  funext t
  simp only [Function.comp_apply, coe_twistedConj_apply, inv_one, one_mul, mul_one]

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

end TwistedCentralizerConj
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalGroup_tensorGL glBorelOf borelSpace_glBorelOf centralizerBorel sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn Coupled mem_sigmaCentralizer_iff"
p2m_open "AutomorphicForm"

namespace TwistedCentralizerConj

section OrbitalTransport

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

private theorem isTwistedOrbitalIntegralOn_of_map_twistedConj
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (hμ : ∀ g : GL (Fin 2) (L ⊗[K] A),
      @Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)) (fun z => g * z) μ = μ)
    (δ x : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ)
    (h : IsTwistedOrbitalIntegralOn K L A σ μ (x⁻¹ * δ * sigmaGL K L A σ x)
      (@Measure.map _ _ (twistedCentralizerBorel K L A σ δ)
        (twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) (twistedConj K L A σ δ x) τ') φ I) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  letI : MeasurableSpace (twistedCentralizer K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)) :=
    twistedCentralizerBorel K L A σ (x⁻¹ * δ * sigmaGL K L A σ x)
  haveI := borelSpace_glBorelOf (L ⊗[K] A)
  haveI := isTopologicalGroup_tensorGL K L A
  haveI : μ.IsMulLeftInvariant := ⟨hμ⟩
  obtain ⟨w, ⟨hw0, hwm, hwc, hws⟩, hI⟩ := h
  refine ⟨fun z => w (x⁻¹ * z), ⟨fun z => hw0 (x⁻¹ * z), ?_, ?_, ?_⟩, ?_⟩
  · exact hwm.comp (continuous_const.mul continuous_id).measurable
  · simpa only [Function.comp_def, Homeomorph.coe_mulLeft] using
      hwc.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  · intro z hz
    have hz' : φ ((x⁻¹ * z)⁻¹ * (x⁻¹ * δ * sigmaGL K L A σ x) * sigmaGL K L A σ (x⁻¹ * z)) ≠ 0 := by
      have hid : (x⁻¹ * z)⁻¹ * (x⁻¹ * δ * sigmaGL K L A σ x) * sigmaGL K L A σ (x⁻¹ * z)
          = z⁻¹ * δ * sigmaGL K L A σ z := by
        simp only [map_mul, map_inv]; group
      rw [hid]; exact hz
    have h1 := hws (x⁻¹ * z) hz'
    rw [(measurableEmbedding_twistedConj K L A σ δ x).integral_map] at h1
    simpa only [coe_twistedConj_apply, mul_assoc, mul_inv_cancel_left] using h1
  · rw [hI, ← integral_mul_left_eq_self
      (fun z => φ (z⁻¹ * δ * sigmaGL K L A σ z) * ((w (x⁻¹ * z) : ℝ) : ℂ)) x]
    refine integral_congr_ae (ae_of_all μ fun u => ?_)
    simp only [map_mul, mul_inv_rev, inv_mul_cancel_left, mul_assoc]

end OrbitalTransport
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

end TwistedCentralizerConj
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm.TwistedCentralizerConj P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate.AutomorphicForm"

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : ∀ g : GL (Fin 2) (L ⊗[K] A),
      @Measure.map _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A))
        (fun z => g * z) μ = μ)
    (γ : GL (Fin 2) A) (δ x : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (hC : AutomorphicForm.Coupled K L A σ γ δ x τ τ') :
    ∃ τ₁ : @Measure (AutomorphicForm.twistedCentralizer K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x))
        (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x)),
      @Measure.IsHaarMeasure _ _ _
          (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x)) τ₁ ∧
        AutomorphicForm.Coupled K L A σ γ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) 1 τ τ₁ ∧
        ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x) τ₁
              φ I →
            AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I :=
  ⟨@Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ x))
      (AutomorphicForm.TwistedCentralizerConj.twistedConj K L A σ δ x) τ',
    AutomorphicForm.TwistedCentralizerConj.isHaarMeasure_map_twistedConj K L A σ δ x τ' hτ',
    AutomorphicForm.TwistedCentralizerConj.coupled_one_map_twistedConj K L A σ γ δ x τ τ' hC,
    fun φ I hI =>
      AutomorphicForm.TwistedCentralizerConj.isTwistedOrbitalIntegralOn_of_map_twistedConj K L A σ μ hμ δ x τ' φ I
        hI⟩

end S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_coupled_one_of_coupled_sigmaConjugate (solution)
