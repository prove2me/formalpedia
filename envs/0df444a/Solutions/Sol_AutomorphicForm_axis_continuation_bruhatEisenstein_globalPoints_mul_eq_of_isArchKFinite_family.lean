-- Prove2me | solution 1 for AutomorphicForm.axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/43c57609-90ca-5c87-a8bc-9624368a6ad0

import Theorems.Thm_AutomorphicForm_pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
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
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
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
      (s : ℂ) (_hs : s ∈ Oφ) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
    Eφ s (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = Eφ s g := by
  intro αm hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hEφ s hs γ g
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEjc, hNjc, hE, hN⟩ := hEφ
  have hu : AnalyticOnNhd ℂ (fun s => Eφ s (AutomorphicForm.globalPoints (𝓞 F) F γ * g)) Oφ := hEa _
  have hv : AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ := hEa _
  have h1 : (1 : ℂ) ∈ Oφ := hhalf (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num)
  have hφc : ∀ s : ℂ, Continuous (φf s) := fun s =>
    hφfjc.comp (continuous_const.prodMk continuous_id)
  have key : ∀ s : ℂ, 1 / 2 < s.re → Eφ s (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = Eφ s g := by
    intro s hs'
    obtain ⟨hB, -⟩ := AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
      F hαm μ ν hμF hνF s (φf s) (hφf s)
    have hsum : Summable (fun ξ : F => φf s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) :=
      (AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ ν hμ hν s hs' (φf s) (hφf s) (hφc s) g).of_norm
    have h3 := (AutomorphicForm.pseudoEisenstein_globalPoints_mul_eq_of_forall_mem_borelSubgroup_of_summable F (φf s) hB g hsum γ).2
    rw [hE s hs', hE s hs']
    rw [AutomorphicForm.pseudoEisenstein_apply, AutomorphicForm.pseudoEisenstein_apply] at h3
    exact h3
  have hfg : (fun s => Eφ s (AutomorphicForm.globalPoints (𝓞 F) F γ * g)) =ᶠ[nhds (1 : ℂ)] (fun s => Eφ s g) := by
    have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact Filter.eventuallyEq_of_mem (hopen.mem_nhds (by simp only [Set.mem_setOf_eq, Complex.one_re]; norm_num))
      (fun s hs' => key s hs')
  exact (hu.eqOn_of_preconnected_of_eventuallyEq hv hOc h1 hfg) hs

end S_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family
end P2MW
export P2MW.S_AutomorphicForm_axis_continuation_bruhatEisenstein_globalPoints_mul_eq_of_isArchKFinite_family (solution)
