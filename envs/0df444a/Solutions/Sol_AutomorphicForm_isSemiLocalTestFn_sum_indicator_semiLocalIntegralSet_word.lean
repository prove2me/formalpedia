-- Prove2me | solution 1 for AutomorphicForm.isSemiLocalTestFn_sum_indicator_semiLocalIntegralSet_word
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/dbd45e43-6ca3-5bd4-b835-c0b2cac8c140

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isSemiLocalTestFn_sum_indicator_semiLocalIntegralSet_word

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

namespace SlWord

open scoped TensorProduct.RightActions

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem translate_indicator (U : Set G)
    (hU : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) ∧ HasCompactSupport (U.indicator fun _ => (1 : ℂ)))
    (g : G) :
    IsLocallyConstant (fun x => U.indicator (fun _ => (1 : ℂ)) (g⁻¹ * x)) ∧
      HasCompactSupport (fun x => U.indicator (fun _ => (1 : ℂ)) (g⁻¹ * x)) := by
  refine ⟨hU.1.comp_continuous (continuous_const_mul g⁻¹), ?_⟩
  have e : (fun x => U.indicator (fun _ => (1 : ℂ)) (g⁻¹ * x)) =
      (U.indicator fun _ => (1 : ℂ)) ∘ (Homeomorph.mulLeft g⁻¹) := rfl
  rw [e]
  exact hU.2.comp_homeomorph _

end Generic

theorem finset_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι) (F : ι → X → ℂ)
    (hF : ∀ i ∈ s, IsLocallyConstant (F i) ∧ HasCompactSupport (F i)) :
    IsLocallyConstant (fun x => ∑ i ∈ s, F i x) ∧ HasCompactSupport (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hl := h1.1.add h2.1
    have hc := h1.2.add h2.2
    simp only [Finset.sum_insert ha]
    exact ⟨hl, hc⟩

theorem word_test (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (c : ι → GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    IsSemiLocalTestFn K L v (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      ∑ i ∈ s, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((c i)⁻¹ * x)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hU := AutomorphicForm.isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
  exact finset_sum s (fun i x => (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((c i)⁻¹ * x))
    fun i _ => translate_indicator _ hU _

end SlWord

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    IsSemiLocalTestFn K L v (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)) :=
  SlWord.word_test K L v Finset.univ fun ι : Fin (ks v) → Fin (ns v) =>
    semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v))

end S_AutomorphicForm_isSemiLocalTestFn_sum_indicator_semiLocalIntegralSet_word
end P2MW
export P2MW.S_AutomorphicForm_isSemiLocalTestFn_sum_indicator_semiLocalIntegralSet_word (solution)
