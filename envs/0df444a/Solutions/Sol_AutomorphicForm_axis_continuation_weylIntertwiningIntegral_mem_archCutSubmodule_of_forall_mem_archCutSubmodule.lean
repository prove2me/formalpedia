-- Prove2me | solution 1 for AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a84f42e7-f6e6-5885-96c8-54388e8ca9e8

import Theorems.Thm_AutomorphicForm_mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace NARC

theorem rowIsometryInclAt₀_injective (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a b h
  have h1 := congrArg (fun g => archComponent F w (glArch (𝓞 F) F g)) h
  simp only [rowIsometryInclAt₀_apply] at h1
  rw [show glArch (𝓞 F) F (adelicArchGLInclAt F w (a : GL (Fin 2) w.Completion)) = archGLIncl F w a from
      glArch_adelicArchGLIncl F _,
    show glArch (𝓞 F) F (adelicArchGLInclAt F w (b : GL (Fin 2) w.Completion)) = archGLIncl F w b from
      glArch_adelicArchGLIncl F _,
    archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h1
  exact Subtype.ext h1

end NARC

theorem solution
    (F : Type) [Field F] [NumberField F] (tysF : ArchTypeFamily F) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule F tysF)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (t : ℝ),
    Nφ ((t : ℂ) * Complex.I) ∈ archCutSubmodule F tysF := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu hφfty Oφ Eφ Nφ hEφ t
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEφ
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  rw [mem_archCutSubmodule_iff]
  intro w
  have hι := NARC.rowIsometryInclAt₀_injective F w

  have key := fun (f : AdelicGL2 (𝓞 F) F → ℂ) =>
    AutomorphicForm.mem_iSup_typeSubmodule_iff_forall_finsupp_sum_smul_eq_zero (rowIsometryInclAt₀ F w) hι
      (ρ := fun i : Fin (tysF.card w) => (tysF.rep w i).ρ) f
  change Nφ ((t : ℂ) * Complex.I) ∈ ⨆ i : Fin (tysF.card w), typeSubmodule (rowIsometryInclAt₀ F w) (tysF.rep w i).ρ
  refine (key _).mpr ?_
  intro a ha

  have hφzero : ∀ (s : ℂ) (y : AdelicGL2 (𝓞 F) F),
      (a.sum fun k c => c * φf s (y * rowIsometryInclAt₀ F w k)) = 0 := by
    intro s y
    have hmem : φf s ∈ ⨆ i : Fin (tysF.card w), typeSubmodule (rowIsometryInclAt₀ F w) (tysF.rep w i).ρ :=
      (mem_archCutSubmodule_iff F tysF (φf s)).mp (hφfty s) w
    exact congrFun ((key (φf s)).mp hmem a ha) y
  funext x

  have han : AnalyticOnNhd ℂ (fun s => a.sum fun k c => c * Nφ s (x * rowIsometryInclAt₀ F w k)) Oφ := by
    simp only [Finsupp.sum]
    have hrew : (fun s => ∑ k ∈ a.support, a k * Nφ s (x * rowIsometryInclAt₀ F w k)) =
        ∑ k ∈ a.support, fun s => a k * Nφ s (x * rowIsometryInclAt₀ F w k) := by
      funext s; simp only [Finset.sum_apply]
    rw [hrew]
    exact Finset.analyticOnNhd_sum _ fun k _ => analyticOnNhd_const.mul (hNa _)
  have hzero : ∀ s : ℂ, 1 / 2 < s.re → (a.sum fun k c => c * Nφ s (x * rowIsometryInclAt₀ F w k)) = 0 := by
    intro s hs
    have hint : ∀ k : rowIsometrySubgroup₀ w.Completion, Integrable (fun u : AdeleRing (𝓞 F) F =>
        φf s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * (x * rowIsometryInclAt₀ F w k))) (adelicAddHaar (𝓞 F) F) :=
      fun k => AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hαm μ ν hμ hν s hs (φf s) (hφf s)
        (hφfjc.comp (continuous_const.prodMk continuous_id)) _
    simp only [hN s hs, weylIntertwiningIntegral, Finsupp.sum]
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun k _ => (hint k).const_mul (a k)]
    have : ∀ u : AdeleRing (𝓞 F) F, (∑ k ∈ a.support, a k *
        φf s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * (x * rowIsometryInclAt₀ F w k))) = 0 := fun u => by
      have h := hφzero s ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * x)
      simp only [Finsupp.sum, mul_assoc] at h ⊢
      exact h
    simp only [this, integral_zero]
  have h1 : (1 : ℂ) ∈ Oφ := hhalf (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num)
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfg : (fun s => a.sum fun k c => c * Nφ s (x * rowIsometryInclAt₀ F w k)) =ᶠ[nhds (1 : ℂ)] 0 :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num))
      (fun s hs => hzero s hs)
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hOc h1 hfg
  have hs : ((t : ℂ) * Complex.I) ∈ Oφ := hax (by simp)
  exact hall hs

end S_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule (solution)
