-- Prove2me | solution 1 for AutomorphicForm.continuous_and_differentiable_and_decay_and_eq_sum_integral_convOp_of_paleyWiener_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/50ce88f9-c280-5318-97a3-f52cf7f5fb37

import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_and_differentiable_and_decay_and_eq_sum_integral_convOp_of_paleyWiener_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ιP : Type) [Fintype ιP]
    (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
    (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
    (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => convOp K f (ψf e p.1) p.2)) ∧
    (∀ e g, Differentiable ℂ (fun s => convOp K f (ψf e s) g)) ∧
    (∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      convOp K f ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g) := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μH := adelicGLHaar (Fin 2) (𝓞 K) K with hμH
  set S := tsupport f with hS
  have hSc : IsCompact S := _hfc
  have hf0 : ∀ x, x ∉ S → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hL : 0 ≤ ∫ x, ‖f x‖ ∂μH := integral_nonneg fun x => norm_nonneg _
  have hfn_int : Integrable (fun x => ‖f x‖) μH := _hf.norm.integrable_of_hasCompactSupport _hfc.norm

  have hconv : ∀ (e : ιP) (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      convOp K f (ψf e s) g = ∫ x in S, ψf e s (g * x) * f x ∂μH := by
    intro e s g
    rw [convOp_apply, rightConv_apply]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hf0 x hx, mul_zero]).symm

  have h1 : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => convOp K f (ψf e p.1) p.2) := by
    intro e
    have hF : Continuous (Function.uncurry fun (p : ℂ × AdelicGL2 (𝓞 K) K) (y : AdelicGL2 (𝓞 K) K) =>
        ψf e p.1 (p.2 * y) * f y) := by
      refine Continuous.mul ?_ (_hf.comp continuous_snd)
      exact (_hψjc e).comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).mul continuous_snd))
    have h := continuous_parametric_integral_of_continuous (μ := μH) hF hSc
    refine h.congr fun p => ?_
    exact (hconv e p.1 p.2).symm

  have h2 : ∀ e g, Differentiable ℂ (fun s => convOp K f (ψf e s) g) := by
    intro e g
    have h := Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn μH isOpen_univ hSc
      (fun s x => ψf e s (g * x) * f x)
      (Continuous.continuousOn (((_hψjc e).comp (continuous_fst.prodMk
        ((continuous_const.mul continuous_snd)))).mul (_hf.comp continuous_snd)))
      (fun s _ x hx => by show ψf e s (g * x) * f x = 0; rw [hf0 x hx, mul_zero])
      (fun x => ((_hψhol e (g * x)).mul_const (f x)).differentiableOn)
    have heq : (fun s => convOp K f (ψf e s) g) = fun s => ∫ x, ψf e s (g * x) * f x ∂μH := by
      funext s; rw [convOp_apply, rightConv_apply]
    rw [heq]
    exact differentiableOn_univ.1 h

  have hψx : ∀ (e : ιP) (s : ℂ) (g : AdelicGL2 (𝓞 K) K), Continuous fun x : AdelicGL2 (𝓞 K) K => ψf e s (g * x) :=
    fun e s g => (_hψjc e).comp (continuous_const.prodMk (continuous_const_mul g))
  have hintx : ∀ (e : ιP) (s : ℂ) (g : AdelicGL2 (𝓞 K) K), Integrable (fun x => ψf e s (g * x) * f x) μH :=
    fun e s g => ((hψx e s g).mul _hf).integrable_of_hasCompactSupport _hfc.mul_left

  have h3 : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t := by
    intro e n σ₀ C hC
    obtain ⟨m, hm, ⟨B, hB⟩, hbd⟩ := _hψdec e n σ₀ (C * S) (hC.mul hSc)
    refine ⟨fun t => m t * ∫ x, ‖f x‖ ∂μH, hm.mul_const _, ⟨B * ∫ x, ‖f x‖ ∂μH, fun t =>
      mul_le_mul_of_nonneg_right (hB t) hL⟩, fun σ' hσ' t g hg => ?_⟩
    have hpos : 0 ≤ (1 + |t|) ^ n := by positivity
    rw [convOp_apply, rightConv_apply]
    calc (1 + |t|) ^ n * ‖∫ x, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x ∂μH‖
        ≤ (1 + |t|) ^ n * ∫ x, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x‖ ∂μH :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hpos
      _ = ∫ x, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x‖ ∂μH :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ x, m t * ‖f x‖ ∂μH := by
          refine integral_mono (((hintx e _ g).norm).const_mul _) (hfn_int.const_mul _) fun x => ?_
          by_cases hx : x ∈ S
          · show (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x‖ ≤ m t * ‖f x‖
            rw [norm_mul, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right (hbd σ' hσ' t (g * x) (Set.mul_mem_mul hg hx)) (norm_nonneg _)
          · show (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x‖ ≤ m t * ‖f x‖
            rw [hf0 x hx]; simp
      _ = m t * ∫ x, ‖f x‖ ∂μH := integral_const_mul _ _

  have h4 : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      convOp K f ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g := by
    intro σ' g

    have hmeasI : ∀ e, AEStronglyMeasurable (fun x : AdelicGL2 (𝓞 K) K =>
        ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) μH := by
      intro e
      have hc : Continuous (Function.uncurry fun (x : AdelicGL2 (𝓞 K) K) (t : ℝ) =>
          ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) :=
        (_hψjc e).comp (((continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))).prodMk ((continuous_const_mul g).comp continuous_fst))
      exact (hc.stronglyMeasurable.integral_prod_right).aestronglyMeasurable

    have hdom : ∀ e, ∃ m : ℝ → ℝ, Integrable m ∧
        (∀ (t : ℝ), ∀ x ∈ S, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)‖ ≤ m t) ∧
        ∀ (t : ℝ) (x : AdelicGL2 (𝓞 K) K),
          ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x‖ ≤ ‖f x‖ * m t := by
      intro e
      obtain ⟨m, hm, -, hbd⟩ := _hψdec e 0 |σ'| ({g} * S) ((isCompact_singleton).mul hSc)
      have hbd' : ∀ (t : ℝ), ∀ x ∈ S, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)‖ ≤ m t := by
        intro t x hx
        have h := hbd σ' le_rfl t (g * x) (Set.mul_mem_mul (Set.mem_singleton g) hx)
        rwa [pow_zero, one_mul] at h
      refine ⟨m, hm, hbd', fun t x => ?_⟩
      by_cases hx : x ∈ S
      · rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hbd' t x hx) (norm_nonneg _)
      · rw [hf0 x hx]; simp
    have hintI : ∀ e, Integrable (fun x : AdelicGL2 (𝓞 K) K =>
        (∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x) μH := by
      intro e
      obtain ⟨m, hm, hbd', -⟩ := hdom e
      refine Integrable.mono' (hfn_int.mul_const (∫ t, m t)) ((hmeasI e).mul _hf.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      by_cases hx : x ∈ S
      · calc ‖∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)‖ * ‖f x‖
            ≤ (∫ t : ℝ, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)‖) * ‖f x‖ :=
              mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) (norm_nonneg _)
          _ ≤ (∫ t : ℝ, m t) * ‖f x‖ :=
              mul_le_mul_of_nonneg_right (integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hm
                (Filter.Eventually.of_forall fun t => hbd' t x hx)) (norm_nonneg _)
          _ = ‖f x‖ * ∫ t, m t := mul_comm _ _
      · rw [hf0 x hx]; simp

    have hswap : ∀ e, (∫ x, (∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x ∂μH) =
        ∫ t : ℝ, convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g := by
      intro e
      obtain ⟨m, hm, -, hbd⟩ := hdom e
      have hcont : Continuous (Function.uncurry fun (x : AdelicGL2 (𝓞 K) K) (t : ℝ) =>
          ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x) :=
        ((_hψjc e).comp (((continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))).prodMk ((continuous_const_mul g).comp continuous_fst))).mul (_hf.comp continuous_fst)
      have hI : Integrable (Function.uncurry fun (x : AdelicGL2 (𝓞 K) K) (t : ℝ) =>
          ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x) (μH.prod volume) := by
        refine Integrable.mono' (hfn_int.mul_prod hm) hcont.aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => ?_)
        exact hbd p.2 p.1
      calc (∫ x, (∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x ∂μH)
          = ∫ x, (∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x) ∂μH := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            exact (integral_mul_const _ _).symm
        _ = ∫ t : ℝ, (∫ x, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x ∂μH) := integral_integral_swap hI
        _ = ∫ t : ℝ, convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            show (∫ x, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x) * f x ∂μH) =
              convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g
            rw [convOp_apply, rightConv_apply]
    rw [convOp_apply, rightConv_apply]
    simp_rw [_hψrep σ']
    calc (∫ x, (∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x ∂μH)
        = ∫ x, ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ((∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x) ∂μH := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show (∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x = _
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun e _ => by rw [mul_assoc]
      _ = ∑ e, ∫ x, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ((∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) (g * x)) * f x) ∂μH :=
          integral_finsetSum _ fun e _ => (hintI e).const_mul _
      _ = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [integral_const_mul, hswap e]
  exact ⟨h1, h2, h3, h4⟩

end S_AutomorphicForm_continuous_and_differentiable_and_decay_and_eq_sum_integral_convOp_of_paleyWiener_family
end P2MW
export P2MW.S_AutomorphicForm_continuous_and_differentiable_and_decay_and_eq_sum_integral_convOp_of_paleyWiener_family (solution)
