-- Prove2me | solution 1 for AutomorphicForm.measureReal_torusUnits_pos_and_measure_detUnits_lt_top_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/eb0587ef-8fa1-5b08-be53-efe908662b72

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_det_mem_range_and_isOpen_isCompact_detUnits_twistedCentralizer_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_measureReal_torusUnits_pos_and_measure_detUnits_lt_top_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hu₀ : u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ₀e : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hy₁ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁)
    (hS : ∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
        ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
          y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t)
    (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT)
    (hlink : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT)) :
      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       0 < ((Measure.map Subtype.val τT) {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal) ∧
      (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
       τ' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} < ⊤) := by
  refine ⟨?_, ?_⟩
  · letI := AutomorphicForm.localGLBorel K v
    letI := AutomorphicForm.localCentralizerBorel K v γ₀
    have h := AutomorphicForm.measure_setOf_mem_localCentralizer_pos_and_lt_top_of_forall_not_diagonal K v γ₀ hγ₀ hγ₀e (Measure.map Subtype.val τT) ⟨τT, hτT, rfl⟩
    exact ENNReal.toReal_pos h.1.ne' h.2.ne
  · letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
    haveI : BorelSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) := ⟨rfl⟩
    haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
    haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
    haveI := hτ'
    obtain ⟨-, -, hUc⟩ := AutomorphicForm.det_mem_range_and_isOpen_isCompact_detUnits_twistedCentralizer_of_not_isSigmaConjugate_scalar_of_finrank_eq_two K L h2 σ hgen v c δ hδ hδq
    exact hUc.measure_lt_top

end S_AutomorphicForm_measureReal_torusUnits_pos_and_measure_detUnits_lt_top_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_measureReal_torusUnits_pos_and_measure_detUnits_lt_top_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
