-- Prove2me | solution 1 for AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ba419550-ffc7-5775-a8cd-53978f459ce3

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral

set_option Elab.async false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm Filter Topology"
open scoped ENNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection isInducedSection_unipotent_mul AdelicGL2 globalPoints IsUnitaryChar unipotentGL2 unipotentGL2_add constantTerm etaFst etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral weylIntertwiningIntegrand_integrable_of_re_gt_half"
namespace BruhatCTSol
p2m_open "AutomorphicForm"

section Unfold

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

scoped instance instNontrivialAdeleRing : Nontrivial 𝔸 := by
  haveI : Inhabited (InfinitePlace F) := Classical.inhabited_of_nonempty inferInstance
  haveI : Nontrivial (InfiniteAdeleRing F) := inferInstanceAs (Nontrivial ((w : InfinitePlace F) → w.Completion))
  exact inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

def principalEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun k => ⟨ι k, k, rfl⟩)
    ⟨fun a b h => (algebraMap F 𝔸).injective (congrArg Subtype.val h), by rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

scoped instance instCountablePrincipal : Countable (AdeleRing.principalSubgroup (𝓞 F) F) :=
  (principalEquiv F).symm.injective.countable

variable (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]

theorem tsum_lintegral_adelicBox_comp_add (f : 𝔸 → ℝ≥0∞) :
    ∑' ξ : F, ∫⁻ t in adelicBox F, f (t + ι ξ) ∂μ = ∫⁻ t, f t ∂μ := by
  have hFD := isAddFundamentalDomain_adelicBox F μ
  rw [hFD.lintegral_eq_tsum'' f, ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => lintegral_congr fun t => ?_
  show f (t + ι ξ) = f (ι ξ + t)
  rw [add_comm]

theorem tsum_integral_adelicBox_comp_add {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    ∑' ξ : F, ∫ t in adelicBox F, Φ (t + ι ξ) ∂μ = ∫ t, Φ t ∂μ := by
  have hFD := isAddFundamentalDomain_adelicBox F μ
  rw [hFD.integral_eq_tsum'' Φ hΦ, ← (principalEquiv F).tsum_eq]
  refine tsum_congr fun ξ => integral_congr_ae (Eventually.of_forall fun t => ?_)
  show Φ (t + ι ξ) = Φ (ι ξ + t)
  rw [add_comm]

theorem integrableOn_and_setIntegral_tsum_translate {Φ : 𝔸 → ℂ} (hΦ : Integrable Φ μ) :
    IntegrableOn (fun t => ∑' ξ : F, Φ (t + ι ξ)) (adelicBox F) μ ∧
      ∫ t in adelicBox F, (∑' ξ : F, Φ (t + ι ξ)) ∂μ = ∫ t, Φ t ∂μ := by
  set ν : Measure 𝔸 := μ.restrict (adelicBox F) with hν
  have hT : ∀ ξ : F, Integrable (fun t => Φ (t + ι ξ)) μ := fun ξ => hΦ.comp_add_right (ι ξ)
  have hmeas : ∀ ξ : F, AEStronglyMeasurable (fun t => Φ (t + ι ξ)) ν := fun ξ =>
    (hT ξ).aestronglyMeasurable.restrict
  have hgmeas : AEMeasurable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν := by
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact AEMeasurable.iSup fun s => Finset.aemeasurable_fun_sum s fun ξ _ => (hmeas ξ).enorm
  have hsum : ∑' ξ : F, ∫⁻ t, ‖Φ (t + ι ξ)‖ₑ ∂ν = ∫⁻ t, ‖Φ t‖ₑ ∂μ := by
    rw [hν, tsum_lintegral_adelicBox_comp_add F μ (fun t => ‖Φ t‖ₑ)]
  have hglint : ∫⁻ t, (∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ∂ν < ∞ := by
    rw [lintegral_tsum fun ξ => (hmeas ξ).enorm, hsum]
    exact hΦ.2
  have hgint : Integrable (fun t => ∑' ξ : F, ‖Φ (t + ι ξ)‖ₑ) ν :=
    ⟨hgmeas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_enorm]
      simpa only [enorm_eq_self] using hglint⟩
  have hae : ∀ᵐ t ∂ν, HasSum (fun ξ : F => Φ (t + ι ξ)) (∑' ξ : F, Φ (t + ι ξ)) := by
    filter_upwards [ae_lt_top' hgmeas hglint.ne] with t ht
    have hs : Summable fun ξ : F => (‖Φ (t + ι ξ)‖₊ : ℝ) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      simpa only [enorm_eq_nnnorm] using ht.ne
    exact (Summable.of_norm (by simpa only [coe_nnnorm] using hs)).hasSum
  have hPmeas : AEStronglyMeasurable (fun t => ∑' ξ : F, Φ (t + ι ξ)) ν :=
    aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset F))
      (f := fun s : Finset F => fun t => ∑ ξ ∈ s, Φ (t + ι ξ))
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun ξ _ => hmeas ξ) hae
  refine ⟨hgint.mono'_enorm hPmeas (Eventually.of_forall fun t => enorm_tsum_le_tsum_enorm), ?_⟩

  have hfin : ∑' ξ : F, ∫⁻ t, ‖Φ (t + ι ξ)‖ₑ ∂ν ≠ ∞ := by
    rw [hsum]; exact hΦ.2.ne
  show ∫ t, (∑' ξ : F, Φ (t + ι ξ)) ∂ν = ∫ t, Φ t ∂μ
  rw [integral_tsum hmeas hfin, hν, tsum_integral_adelicBox_comp_add F μ hΦ]

end Unfold

section Core

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "G𝔸" => AdelicGL2 (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  show (globalPoints (𝓞 F) F gl2Weyl)⁻¹ = globalPoints (𝓞 F) F gl2Weyl
  rw [← map_inv (globalPoints (𝓞 F) F) gl2Weyl, gl2Weyl_inv]

theorem constantTerm_cond_adelicBox_eq (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (φ : G𝔸 → ℂ)
    (hN : ∀ (x : 𝔸) (g : G𝔸), φ (unipotentGL2 x * g) = φ g) (w g : G𝔸)
    (hint : Integrable (fun u : 𝔸 => φ (w * unipotentGL2 u * g)) μ) :
    constantTerm (ProbabilityTheory.cond μ (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * g')) g
      = φ g + ((μ (adelicBox F)).toReal : ℂ)⁻¹ * ∫ u, φ (w * unipotentGL2 u * g) ∂μ := by
  obtain ⟨hS, hunf⟩ := integrableOn_and_setIntegral_tsum_translate F μ hint

  have hE : (fun t : 𝔸 => φ (unipotentGL2 t * g) + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * (unipotentGL2 t * g)))
      = fun t => φ g + ∑' ξ : F, φ (w * unipotentGL2 (t + ι ξ) * g) := by
    funext t
    rw [hN t g]
    congr 1
    refine tsum_congr fun ξ => ?_
    rw [add_comm t, unipotentGL2_add]
    simp only [mul_assoc]
  have hpos : 0 < μ (adelicBox F) := measure_adelicBox_pos F μ
  have hlt : μ (adelicBox F) < ∞ := measure_adelicBox_lt_top F μ
  haveI : IsFiniteMeasure (μ.restrict (adelicBox F)) := ⟨by rw [Measure.restrict_apply_univ]; exact hlt⟩
  have hm : ((μ (adelicBox F)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hlt.ne⟩)
  show ∫ t, (φ (unipotentGL2 t * g) + ∑' ξ : F, φ (w * unipotentGL2 (ι ξ) * (unipotentGL2 t * g)))
      ∂(ProbabilityTheory.cond μ (adelicBox F)) = _
  rw [hE, ProbabilityTheory.cond, integral_smul_measure, integral_add (integrable_const _) hS, integral_const,
    measureReal_restrict_apply_univ, measureReal_def, hunf, ENNReal.toReal_inv]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]

theorem constantTerm_bruhatEisenstein_core {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (φ : G𝔸 → ℂ)
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (g : G𝔸)
    (hint : Integrable (fun u : 𝔸 => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)) (adelicAddHaar (𝓞 F) F)) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (ι ξ) * g')) g
      = φ g + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  rw [adelicWeyl_inv] at hint
  unfold weylIntertwiningIntegral
  rw [adelicWeyl_inv]
  exact constantTerm_cond_adelicBox_eq F (adelicAddHaar (𝓞 F) F) φ (fun x g => isInducedSection_unipotent_mul hφ x g)
    (adelicWeyl (𝓞 F) F) g hint

end Core

section Row

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm"
open scoped NNReal

theorem constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  intro α hα μ ν hμ hν s hs φ hφ hφc g
  exact constantTerm_bruhatEisenstein_core F φ hφ g
    (weylIntertwiningIntegrand_integrable_of_re_gt_half F hα μ ν hμ hν s hs φ hφ hφc g)

end Row

end AutomorphicForm.BruhatCTSol
p2m_reactivate "P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm.BruhatCTSol"
p2m_reactivate "P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm"
open scoped NNReal

example
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g :=
  AutomorphicForm.BruhatCTSol.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl F

end
p2m_reactivate "P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm.BruhatCTSol"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.AutomorphicForm"
open scoped NNReal

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    constantTerm
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 E g
      = φ g
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹
          * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := by
  first
    | exact AutomorphicForm.BruhatCTSol.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl F
    | (apply AutomorphicForm.BruhatCTSol.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral_impl <;> assumption)

end S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
end P2MW
export P2MW.S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral (solution)
