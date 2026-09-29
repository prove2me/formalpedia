-- Prove2me | solution 1 for AutomorphicForm.integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b09fa595-c817-5b86-926d-d8b2d3477e64

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_MellinParseval_setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul
import Theorems.Thm_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory Filter Topology NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal

namespace TorusPairingMatch

theorem lineIntegral_eq_lineIntegral (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ₁ σ₂ : ℝ)
    (h₁ : Integrable fun t : ℝ => F ((σ₁ : ℂ) + (t : ℂ) * Complex.I))
    (h₂ : Integrable fun t : ℝ => F ((σ₂ : ℂ) + (t : ℂ) * Complex.I))
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ x : ℝ, x ∈ Set.uIcc σ₁ σ₂ → ∀ R : ℝ, R₀ ≤ |R| →
      ‖F ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤ ε) :
    ∫ t : ℝ, F ((σ₁ : ℂ) + (t : ℂ) * Complex.I) = ∫ t : ℝ, F ((σ₂ : ℂ) + (t : ℂ) * Complex.I) := by
  set L₁ : ℂ := ∫ t : ℝ, F ((σ₁ : ℂ) + (t : ℂ) * Complex.I) with hL₁
  set L₂ : ℂ := ∫ t : ℝ, F ((σ₂ : ℂ) + (t : ℂ) * Complex.I) with hL₂
  set V₁ : ℝ → ℂ := fun R => ∫ t in (-R)..R, F ((σ₁ : ℂ) + (t : ℂ) * Complex.I) with hV₁
  set V₂ : ℝ → ℂ := fun R => ∫ t in (-R)..R, F ((σ₂ : ℂ) + (t : ℂ) * Complex.I) with hV₂
  set Ht : ℝ → ℂ := fun R => ∫ x in σ₁..σ₂, F ((x : ℂ) + (R : ℂ) * Complex.I) with hHt
  set Hb : ℝ → ℂ := fun R => ∫ x in σ₁..σ₂, F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) with hHb
  have hV₁t : Tendsto V₁ atTop (𝓝 L₁) :=
    intervalIntegral_tendsto_integral h₁ tendsto_neg_atTop_atBot tendsto_id
  have hV₂t : Tendsto V₂ atTop (𝓝 L₂) :=
    intervalIntegral_tendsto_integral h₂ tendsto_neg_atTop_atBot tendsto_id

  have hE : ∀ R : ℝ, Complex.I * (V₂ R - V₁ R) = Ht R - Hb R := by
    intro R
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F ⟨σ₁, -R⟩ ⟨σ₂, R⟩
      hF.differentiableOn
    dsimp only at key
    simp only [smul_eq_mul] at key
    linear_combination key
  have hlim₁ : Tendsto (fun R => Ht R - Hb R) atTop (𝓝 (Complex.I * (L₂ - L₁))) := by
    have h := (hV₂t.sub hV₁t).const_mul Complex.I
    refine h.congr fun R => ?_
    exact hE R
  have hlim₂ : Tendsto (fun R => Ht R - Hb R) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' : ℝ := ε / (2 * (|σ₂ - σ₁| + 1)) with hε'
    have hden : 0 < 2 * (|σ₂ - σ₁| + 1) := by positivity
    have hε'0 : 0 < ε' := div_pos hε hden
    obtain ⟨R₀, hR₀⟩ := hdec ε' hε'0
    refine ⟨max R₀ 0, fun R hR => ?_⟩
    have hR0 : 0 ≤ R := (le_max_right _ _).trans hR
    have hRabs : R₀ ≤ |R| := by rw [abs_of_nonneg hR0]; exact (le_max_left _ _).trans hR
    have hRabs' : R₀ ≤ |(-R : ℝ)| := by rw [abs_neg]; exact hRabs
    have hHt' : ‖Ht R‖ ≤ ε' * |σ₂ - σ₁| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      exact hR₀ x (Set.uIoc_subset_uIcc hx) R hRabs
    have hHb' : ‖Hb R‖ ≤ ε' * |σ₂ - σ₁| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      exact hR₀ x (Set.uIoc_subset_uIcc hx) (-R) hRabs'
    rw [dist_zero_right]
    calc ‖Ht R - Hb R‖ ≤ ‖Ht R‖ + ‖Hb R‖ := norm_sub_le _ _
      _ ≤ ε' * |σ₂ - σ₁| + ε' * |σ₂ - σ₁| := add_le_add hHt' hHb'
      _ = ε * (|σ₂ - σ₁| / (|σ₂ - σ₁| + 1)) := by
          rw [hε']; field_simp; ring
      _ < ε := by
          have h1 : |σ₂ - σ₁| / (|σ₂ - σ₁| + 1) < 1 := by
            rw [div_lt_one (by positivity)]; linarith
          calc ε * (|σ₂ - σ₁| / (|σ₂ - σ₁| + 1)) < ε * 1 := by
                exact mul_lt_mul_of_pos_left h1 hε
            _ = ε := mul_one ε
  have hzero : Complex.I * (L₂ - L₁) = 0 := tendsto_nhds_unique hlim₁ hlim₂
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hsub : L₂ - L₁ = 0 := (mul_eq_zero.mp hzero).resolve_left hI
  exact (sub_eq_zero.mp hsub).symm

section Profile

variable {X : Type*} [TopologicalSpace X]

noncomputable def prof (f : ℂ → X → ℂ) (u : ℝ) (g : X) : ℂ :=
  ∫ t : ℝ, Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I)) * f ((t : ℂ) * Complex.I) g

theorem norm_exp_ofReal_mul_ofReal_mul_I (u t : ℝ) :
    ‖Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I))‖ = 1 := by
  have : (u : ℂ) * ((t : ℂ) * Complex.I) = ((u * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem re_ofReal_mul_add_mul_I (u x R : ℝ) : ((u : ℂ) * ((x : ℂ) + (R : ℂ) * Complex.I)).re = u * x := by
  simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im]

theorem abs_le_one_of_mem_uIcc {σ x : ℝ} (hσ : |σ| ≤ 1) (hx : x ∈ Set.uIcc 0 σ) : |x| ≤ 1 := by
  rw [abs_le] at hσ ⊢
  rcases Set.mem_uIcc.1 hx with h | h <;> constructor <;> linarith [h.1, h.2, hσ.1, hσ.2]

theorem integrable_line (f : ℂ → X → ℂ) (C : Set X)
    (hfjc : Continuous fun p : ℂ × X => f p.1 p.2)
    (m₀ : ℝ → ℝ) (hm₀ : Integrable m₀)
    (hb₀ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m₀ t)
    (u σ' : ℝ) (hσ' : |σ'| ≤ 1) (g : X) (hg : g ∈ C) :
    Integrable fun t : ℝ =>
      Complex.exp ((u : ℂ) * ((σ' : ℂ) + (t : ℂ) * Complex.I)) * f ((σ' : ℂ) + (t : ℂ) * Complex.I) g := by
  have hline : Continuous fun t : ℝ => (σ' : ℂ) + (t : ℂ) * Complex.I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcont : Continuous fun t : ℝ =>
      Complex.exp ((u : ℂ) * ((σ' : ℂ) + (t : ℂ) * Complex.I)) * f ((σ' : ℂ) + (t : ℂ) * Complex.I) g :=
    (Complex.continuous_exp.comp (continuous_const.mul hline)).mul
      (hfjc.comp (hline.prodMk continuous_const))
  refine Integrable.mono' (hm₀.const_mul (Real.exp (u * σ'))) hcont.aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, Complex.norm_exp, re_ofReal_mul_add_mul_I]
  exact mul_le_mul_of_nonneg_left (hb₀ σ' hσ' t g hg) (Real.exp_pos _).le

theorem prof_eq (f : ℂ → X → ℂ) (C : Set X)
    (hfjc : Continuous fun p : ℂ × X => f p.1 p.2)
    (hfhol : ∀ g, Differentiable ℂ fun s => f s g)
    (m₀ : ℝ → ℝ) (hm₀ : Integrable m₀)
    (hb₀ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m₀ t)
    (B₁ : ℝ)
    (hb₁ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ C,
      (1 + |t|) * ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ B₁)
    (u σ : ℝ) (hσ : |σ| ≤ 1) (g : X) (hg : g ∈ C) :
    prof f u g = Complex.exp ((u : ℂ) * (σ : ℂ)) *
      ∫ t : ℝ, Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I)) * f ((σ : ℂ) + (t : ℂ) * Complex.I) g := by
  have hB₁ : 0 ≤ B₁ :=
    le_trans (by positivity) (hb₁ 0 (by simp) 0 g hg)
  have key := lineIntegral_eq_lineIntegral (fun s => Complex.exp ((u : ℂ) * s) * f s g)
    (((Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))).mul (hfhol g))
    0 σ
    (integrable_line f C hfjc m₀ hm₀ hb₀ u 0 (by simp) g hg)
    (integrable_line f C hfjc m₀ hm₀ hb₀ u σ hσ g hg)
    (by
      intro ε hε
      refine ⟨Real.exp |u| * B₁ / ε, fun x hx R hR => ?_⟩
      have hx1 : |x| ≤ 1 := abs_le_one_of_mem_uIcc hσ hx
      rw [norm_mul, Complex.norm_exp, re_ofReal_mul_add_mul_I]
      have h1 : Real.exp (u * x) ≤ Real.exp |u| := by
        refine Real.exp_le_exp.2 (le_trans (le_abs_self _) ?_)
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg u) hx1
      have hpos : 0 < 1 + |R| := by positivity
      have h2 : ‖f ((x : ℂ) + (R : ℂ) * Complex.I) g‖ ≤ B₁ / (1 + |R|) := by
        rw [le_div_iff₀ hpos, mul_comm]
        exact hb₁ x hx1 R g hg
      have h3 : Real.exp |u| * B₁ ≤ ε * (1 + |R|) := by
        have := (div_le_iff₀ hε).1 hR
        nlinarith [Real.exp_pos |u|, abs_nonneg R]
      calc Real.exp (u * x) * ‖f ((x : ℂ) + (R : ℂ) * Complex.I) g‖
          ≤ Real.exp |u| * (B₁ / (1 + |R|)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp |u| * B₁ / (1 + |R|) := by ring
        _ ≤ ε := by rw [div_le_iff₀ hpos]; exact h3)
  have hL : (∫ t : ℝ, Complex.exp ((u : ℂ) * (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
      f (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) g) = prof f u g := by
    unfold prof
    congr 1
    funext t
    rw [Complex.ofReal_zero, zero_add]
  rw [← hL, key, ← integral_const_mul]
  congr 1
  funext t
  rw [mul_add, Complex.exp_add, mul_assoc]

theorem norm_prof_le (f : ℂ → X → ℂ) (C : Set X)
    (hfjc : Continuous fun p : ℂ × X => f p.1 p.2)
    (hfhol : ∀ g, Differentiable ℂ fun s => f s g)
    (m₀ : ℝ → ℝ) (hm₀ : Integrable m₀)
    (hb₀ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m₀ t)
    (B₁ : ℝ)
    (hb₁ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ C,
      (1 + |t|) * ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ B₁)
    (u : ℝ) (g : X) (hg : g ∈ C) :
    ‖prof f u g‖ ≤ Real.exp (-|u|) * ∫ t : ℝ, m₀ t := by
  have hint : ∀ σ : ℝ, |σ| ≤ 1 →
      ‖∫ t : ℝ, Complex.exp ((u : ℂ) * ((t : ℂ) * Complex.I)) * f ((σ : ℂ) + (t : ℂ) * Complex.I) g‖
        ≤ ∫ t : ℝ, m₀ t := by
    intro σ hσ
    refine norm_integral_le_of_norm_le hm₀ (ae_of_all _ fun t => ?_)
    rw [norm_mul, norm_exp_ofReal_mul_ofReal_mul_I, one_mul]
    exact hb₀ σ hσ t g hg
  rcases le_or_gt 0 u with hu | hu
  · rw [prof_eq f C hfjc hfhol m₀ hm₀ hb₀ B₁ hb₁ u (-1) (by simp) g hg, norm_mul, Complex.norm_exp]
    have hre : ((u : ℂ) * (((-1 : ℝ)) : ℂ)).re = -|u| := by
      rw [abs_of_nonneg hu]; push_cast; simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left (hint (-1) (by simp)) (Real.exp_pos _).le
  · rw [prof_eq f C hfjc hfhol m₀ hm₀ hb₀ B₁ hb₁ u 1 (by simp) g hg, norm_mul, Complex.norm_exp]
    have hre : ((u : ℂ) * (((1 : ℝ)) : ℂ)).re = -|u| := by
      rw [abs_of_neg hu]; push_cast; simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left (hint 1 (by simp)) (Real.exp_pos _).le

theorem continuous_prof (f : ℂ → X → ℂ) (C : Set X)
    (hfjc : Continuous fun p : ℂ × X => f p.1 p.2)
    (m₀ : ℝ → ℝ) (hm₀ : Integrable m₀)
    (hb₀ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ C, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m₀ t)
    {S : Type*} [TopologicalSpace S] [FirstCountableTopology S] (ι : S → X) (hι : Continuous ι)
    (hιC : ∀ s, ι s ∈ C) :
    Continuous fun p : ℝ × S => prof f p.1 (ι p.2) := by
  have hline : Continuous fun t : ℝ => (t : ℂ) * Complex.I := Complex.continuous_ofReal.mul continuous_const
  refine continuous_of_dominated
    (F := fun (p : ℝ × S) (t : ℝ) => Complex.exp ((p.1 : ℂ) * ((t : ℂ) * Complex.I)) * f ((t : ℂ) * Complex.I) (ι p.2))
    (bound := m₀) (fun p => ?_) (fun p => ae_of_all _ fun t => ?_) hm₀ (ae_of_all _ fun t => ?_)
  · exact ((Complex.continuous_exp.comp (continuous_const.mul hline)).mul
      (hfjc.comp (hline.prodMk continuous_const))).aestronglyMeasurable
  · rw [norm_mul, norm_exp_ofReal_mul_ofReal_mul_I, one_mul]
    have := hb₀ 0 (by simp) t (ι p.2) (hιC p.2)
    rwa [Complex.ofReal_zero, zero_add] at this
  · exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).mul
      (hfjc.comp (continuous_const.prodMk (hι.comp continuous_snd)))

end Profile

section Torus

variable (K : Type) [Field K] [NumberField K]

theorem diagOne_mem_adelicBorel (y : (AdeleRing (𝓞 K) K)ˣ) :
    (diagOne y : AdelicGL2 (𝓞 K) K) ∈ adelicBorel (𝓞 K) K := by
  show ((diagOne y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  rw [diagOne_coe_apply]
  simp

theorem borelDiagFst_diagOne (y : (AdeleRing (𝓞 K) K)ˣ) :
    borelDiagFst (⟨diagOne y, diagOne_mem_adelicBorel K y⟩ : ↥(adelicBorel (𝓞 K) K)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = y
  rw [diagOne_coe_apply]
  simp

theorem borelDiagSnd_diagOne (y : (AdeleRing (𝓞 K) K)ˣ) :
    borelDiagSnd (⟨diagOne y, diagOne_mem_adelicBorel K y⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 =
    ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
  rw [diagOne_coe_apply]
  simp

theorem apply_diagOne_mul (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (χ χ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K (etaFst χ α hα s) (etaSnd χ' α hα s) φ)
    (y : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    φ (diagOne y * g) = ((χ y : ℂˣ) : ℂ) * ((((α y : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2)) * φ g := by
  rw [hφ (diagOne y) (diagOne_mem_adelicBorel K y) g, borelDiagFst_diagOne, borelDiagSnd_diagOne, map_one,
    Units.val_one, mul_one, etaFst_apply, Units.val_mul, cpowChar_apply_val]

theorem continuous_diagOne :
    Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => (diagOne y : AdelicGL2 (𝓞 K) K) := by
  have hval : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      ((diagOne y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.diagonal ![(y : AdeleRing (𝓞 K) K), 1] := fun y => rfl
  have hinv : ∀ y : (AdeleRing (𝓞 K) K)ˣ,
      (((diagOne y : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.diagonal ![((y⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] := fun y => by
    rw [← map_inv]; rfl
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun y : (AdeleRing (𝓞 K) K)ˣ =>
      ((diagOne y : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    simp_rw [hval]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_val
    · simp [Matrix.diagonal_apply_ne]; exact continuous_const
    · simp [Matrix.diagonal_apply_ne]; exact continuous_const
    · simpa using continuous_const
  · show Continuous fun y : (AdeleRing (𝓞 K) K)ˣ =>
      (((diagOne y : AdelicGL2 (𝓞 K) K)⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    simp_rw [hinv]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using Units.continuous_coe_inv
    · simp [Matrix.diagonal_apply_ne]; exact continuous_const
    · simp [Matrix.diagonal_apply_ne]; exact continuous_const
    · simpa using continuous_const

end Torus

theorem measurable_expNegAbsLogMulInv : Measurable fun r : ℝ => Real.exp (-|Real.log r|) * r⁻¹ :=
  (Real.measurable_log.abs.neg.exp).mul measurable_inv

theorem integrableOn_exp_neg_abs_log_mul_inv :
    IntegrableOn (fun r : ℝ => Real.exp (-|Real.log r|) * r⁻¹) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine integrableOn_union.2 ⟨?_, ?_⟩
  · refine Integrable.of_bound measurable_expNegAbsLogMulInv.aestronglyMeasurable 1
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun r hr => ?_))
    have hlog : Real.log r ≤ 0 := Real.log_nonpos hr.1.le hr.2
    rw [abs_of_nonpos hlog, neg_neg, Real.exp_log hr.1, mul_inv_cancel₀ hr.1.ne', norm_one]
  · refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one).congr_fun
      (fun r hr => ?_) measurableSet_Ioi
    have hr0 : 0 < r := zero_lt_one.trans hr
    have hlog : 0 ≤ Real.log r := Real.log_nonneg (le_of_lt hr)
    show r ^ (-2 : ℝ) = Real.exp (-|Real.log r|) * r⁻¹
    rw [abs_of_nonneg hlog, Real.exp_neg, Real.exp_log hr0, Real.rpow_neg hr0.le, Real.rpow_two, sq, mul_inv]

theorem lintegral_exp_neg_abs_log_mul_inv_lt_top :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-|Real.log r|) * r⁻¹) < ∞ :=
  lt_of_le_of_lt (lintegral_mono fun _ => Real.ofReal_le_enorm _)
    integrableOn_exp_neg_abs_log_mul_inv.hasFiniteIntegral

end TorusPairingMatch

namespace TorusPairingMatch

theorem scalar_identity (r : ℝ) (hr : 0 < r) (a b : ℂ) (τ₀ T : ℝ)
    (hab : a = b * (r : ℂ) ^ (Complex.I * (τ₀ : ℂ))) (hb : b * conj b = 1) :
    ((r⁻¹ : ℝ) : ℂ) * (a * (r : ℂ) ^ (1 / 2 : ℂ)) * conj (b * (r : ℂ) ^ ((T : ℂ) * Complex.I + 1 / 2)) =
      (r : ℂ) ^ (-(((T - τ₀ : ℝ) : ℂ) * Complex.I)) := by
  subst hab
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set L : ℂ := (Real.log r : ℂ) with hL
  have hcp : ∀ s : ℂ, (r : ℂ) ^ s = Complex.exp (L * s) := fun s => by
    rw [Complex.cpow_def_of_ne_zero hr0, hL, Complex.ofReal_log hr.le]
  have hinv : ((r⁻¹ : ℝ) : ℂ) = Complex.exp (-L) := by
    rw [Complex.exp_neg, hL, ← Complex.ofReal_exp, Real.exp_log hr, Complex.ofReal_inv]
  have hconj : conj ((T : ℂ) * Complex.I + 1 / 2) = -((T : ℂ) * Complex.I) + 1 / 2 := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, map_ofNat]; ring
  have hLc : conj L = L := by rw [hL, Complex.conj_ofReal]
  simp only [map_mul, hcp, ← Complex.exp_conj, hLc, hconj, hinv]
  calc Complex.exp (-L) * (b * Complex.exp (L * (Complex.I * (τ₀ : ℂ))) * Complex.exp (L * (1 / 2))) *
        (conj b * Complex.exp (L * (-((T : ℂ) * Complex.I) + 1 / 2)))
      = (b * conj b) * (Complex.exp (-L) * Complex.exp (L * (Complex.I * (τ₀ : ℂ))) * Complex.exp (L * (1 / 2)) *
          Complex.exp (L * (-((T : ℂ) * Complex.I) + 1 / 2))) := by ring
    _ = Complex.exp (-L + L * (Complex.I * (τ₀ : ℂ)) + L * (1 / 2) + L * (-((T : ℂ) * Complex.I) + 1 / 2)) := by
        rw [hb, one_mul, Complex.exp_add, Complex.exp_add, Complex.exp_add]
    _ = _ := by congr 1; push_cast; ring

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open NumberField.TateGlobal in

theorem setIntegral_comp_ideleNorm_eq (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hNm : Measurable (ideleNorm K)) (h : ℝ → ℂ) (hh : Measurable h) :
    ∫ z in D, h (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
      ((V.toReal : ℝ) : ℂ) * ∫ r in Set.Ioi (0 : ℝ), ((r⁻¹ : ℝ) : ℂ) * h r := by
  set ρ : Measure ℝ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).withDensity (fun r => ENNReal.ofReal r⁻¹) with hρ
  have hmap : ((NumberField.Idele.idelicHaar K).restrict D).map (ideleNorm K) = V • ρ := by
    refine Measure.ext fun s hs => ?_
    calc ((NumberField.Idele.idelicHaar K).restrict D).map (ideleNorm K) s
        = ((NumberField.Idele.idelicHaar K).restrict D) (ideleNorm K ⁻¹' s) := Measure.map_apply hNm hs
      _ = ∫⁻ z, (ideleNorm K ⁻¹' s).indicator 1 z ∂((NumberField.Idele.idelicHaar K).restrict D) :=
          (lintegral_indicator_one (hNm hs)).symm
      _ = ∫⁻ z in D, s.indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) := by
          congr 1
      _ = V * ∫⁻ y in Set.Ioi (0 : ℝ), s.indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ :=
          hV _ (measurable_const.indicator hs)
      _ = V * ∫⁻ y in Set.Ioi (0 : ℝ), s.indicator (fun y => ENNReal.ofReal y⁻¹) y := by
          congr 1
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ s <;> simp [hy]
      _ = V * ∫⁻ y in s, ENNReal.ofReal y⁻¹ ∂((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
          rw [lintegral_indicator hs]
      _ = (V • ρ) s := by rw [Measure.smul_apply, smul_eq_mul, hρ, withDensity_apply _ hs]
  calc ∫ z in D, h (ideleNorm K z) ∂(NumberField.Idele.idelicHaar K)
      = ∫ r, h r ∂(((NumberField.Idele.idelicHaar K).restrict D).map (ideleNorm K)) :=
        (integral_map hNm.aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ r, h r ∂(V • ρ) := by rw [hmap]
    _ = V.toReal • ∫ r, h r ∂ρ := integral_smul_measure _ _
    _ = V.toReal • ∫ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal r⁻¹).toReal • h r := by
        rw [hρ, integral_withDensity_eq_integral_toReal_smul (measurable_inv.ennreal_ofReal)
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    _ = V.toReal • ∫ r in Set.Ioi (0 : ℝ), ((r⁻¹ : ℝ) : ℂ) * h r := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
        rw [ENNReal.toReal_ofReal (inv_nonneg.2 (le_of_lt hr)), Complex.real_smul]
    _ = ((V.toReal : ℝ) : ℂ) * ∫ r in Set.Ioi (0 : ℝ), ((r⁻¹ : ℝ) : ℂ) * h r := by rw [Complex.real_smul]

end TorusPairingMatch

attribute [local instance] NumberField.AdelicHaar.glBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open NumberField.TateGlobal TorusPairingMatch in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (D : Set (AdeleRing (𝓞 K) K)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm K z) ∂(NumberField.Idele.idelicHaar K) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)

      (μP νP : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμPu : IsUnitaryChar (𝓞 K) K μP) (_hνPu : IsUnitaryChar (𝓞 K) K νP)
      (_hμPic : IsIdeleClassChar (𝓞 K) K μP) (_hνPic : IsIdeleClassChar (𝓞 K) K νP)
      (_hμPc : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP x : ℂˣ) : ℂ))
      (f : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μP αm hαm s) (etaSnd νP αm hαm s) (f s))
      (_hfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => f p.1 p.2))
      (_hfhol : ∀ g, Differentiable ℂ (fun s => f s g))
      (_hfdec : ∀ (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)

      (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ'u : IsUnitaryChar (𝓞 K) K μ') (_hμ'ic : IsIdeleClassChar (𝓞 K) K μ')
      (T : ℝ) (Φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hΦ : IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((T : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((T : ℂ) * Complex.I)) Φ)
      (_hΦc : Continuous Φ)
      (τ₀ : ℝ) (_hmatch : μP = μ' * NumberField.TateGlobal.normPowChar K τ₀),
    Integrable (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
          (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
            conj (Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))))
        ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))).prod
          (maximalCompactHaar K)) ∧
    ∫ y in D, (NumberField.TateGlobal.ideleNorm K y)⁻¹ •
          ∫ k, (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne y * (k : AdelicGL2 (𝓞 K) K))) *
              conj (Φ (diagOne y * (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K)
        ∂(NumberField.Idele.idelicHaar K) =
      ((V.toReal * (2 * Real.pi) : ℝ) : ℂ) *
        ∫ k, f (((T - τ₀ : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (Φ (k : AdelicGL2 (𝓞 K) K))
          ∂(maximalCompactHaar K) := by
  intro αm hαm D hDm hDF V hV0 hVT hV μP νP hμPu hνPu hμPic hνPic hμPc f hf hfjc hfhol hfdec μ' ν' hμ'u hμ'ic
    T Φ hΦ hΦc τ₀ hmatch

  haveI hBGL : BorelSpace (AdelicGL2 (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hNpos : ∀ y : (AdeleRing (𝓞 K) K)ˣ, 0 < ideleNorm K y := fun y => ideleNorm_pos y
  have hNc : Continuous (ideleNorm K) := NumberField.TateGlobal.continuous_ideleNorm K
  have hlogc : Continuous fun y : (AdeleRing (𝓞 K) K)ˣ => Real.log (ideleNorm K y) :=
    hNc.log fun y => (hNpos y).ne'
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
    haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : SecondCountableTopology (adelicMaximalCompact K) :=
    (IsEmbedding.subtypeVal :
      IsEmbedding (Subtype.val : adelicMaximalCompact K → AdelicGL2 (𝓞 K) K)).secondCountableTopology
  haveI : LocallyCompactSpace (AdeleRing (𝓞 K) K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 K) K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI hHaar : (NumberField.Idele.idelicHaar K).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar K
  haveI : SigmaFinite (NumberField.Idele.idelicHaar K) := Measure.IsHaarMeasure.sigmaFinite _

  have hKc : IsCompact (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) := isCompact_adelicMaximalCompact K
  obtain ⟨m₀, hm₀i, -, hm₀⟩ := hfdec 0 1 _ hKc
  have hb₀ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m₀ t := by
    intro σ' hσ' t g hg
    have := hm₀ σ' hσ' t g hg
    rwa [pow_zero, one_mul] at this
  obtain ⟨m₁, -, ⟨B₁, hB₁⟩, hm₁⟩ := hfdec 1 1 _ hKc
  have hb₁ : ∀ σ' : ℝ, |σ'| ≤ 1 → ∀ t : ℝ, ∀ g ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      (1 + |t|) * ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ B₁ := by
    intro σ' hσ' t g hg
    have := hm₁ σ' hσ' t g hg
    rw [pow_one] at this
    exact this.trans (hB₁ t)
  have hone : (1 : AdelicGL2 (𝓞 K) K) ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) :=
    (adelicMaximalCompact K).one_mem
  have hm₀nn : ∀ t, 0 ≤ m₀ t := fun t => (norm_nonneg _).trans (hb₀ 0 (by simp) t 1 hone)
  have hM₀ : 0 ≤ ∫ t, m₀ t := integral_nonneg hm₀nn
  obtain ⟨CΦ, hCΦ⟩ := hKc.exists_bound_of_continuousOn hΦc.continuousOn
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg _).trans (hCΦ 1 hone)

  have hPbd : ∀ (u : ℝ), ∀ g ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      ‖prof f u g‖ ≤ Real.exp (-|u|) * ∫ t, m₀ t :=
    norm_prof_le f _ hfjc hfhol m₀ hm₀i hb₀ B₁ hb₁
  have hPc : Continuous fun p : ℝ × adelicMaximalCompact K => prof f p.1 (p.2 : AdelicGL2 (𝓞 K) K) :=
    continuous_prof f _ hfjc m₀ hm₀i hb₀ (fun k : adelicMaximalCompact K => (k : AdelicGL2 (𝓞 K) K))
      continuous_subtype_val (fun k => k.2)

  have hfT : ∀ (s : ℂ) (y : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      f s (diagOne y * g) = ((μP y : ℂˣ) : ℂ) * (((ideleNorm K y : ℝ) : ℂ) ^ (s + 1 / 2)) * f s g :=
    fun s y g => apply_diagOne_mul K αm hαm μP νP s (f s) (hf s) y g
  have hΦT : ∀ (y : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      Φ (diagOne y * g) = ((μ' y : ℂˣ) : ℂ) * (((ideleNorm K y : ℝ) : ℂ) ^ ((T : ℂ) * Complex.I + 1 / 2)) * Φ g :=
    fun y g => apply_diagOne_mul K αm hαm μ' ν' _ Φ hΦ y g
  have hcpow : ∀ (y : (AdeleRing (𝓞 K) K)ˣ) (t : ℝ),
      ((ideleNorm K y : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I + 1 / 2) =
        ((ideleNorm K y : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
          Complex.exp ((Real.log (ideleNorm K y) : ℂ) * ((t : ℂ) * Complex.I)) := by
    intro y t
    have h0 : ((ideleNorm K y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hNpos y).ne'
    rw [Complex.cpow_add _ _ h0, mul_comm, Complex.cpow_def_of_ne_zero h0 ((t : ℂ) * Complex.I),
      ← Complex.ofReal_log (hNpos y).le]
  have hinner : ∀ (y : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne y * g)) =
        ((μP y : ℂˣ) : ℂ) * ((ideleNorm K y : ℝ) : ℂ) ^ (1 / 2 : ℂ) * prof f (Real.log (ideleNorm K y)) g := by
    intro y g
    simp_rw [hfT, hcpow y]
    rw [prof, ← integral_const_mul]
    congr 1
    funext t
    ring

  set F : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K → ℂ := fun p =>
    (∫ t' : ℝ, f ((t' : ℂ) * Complex.I) (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) *
      conj (Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) with hFdef
  have hFeq : F = fun p => (((μP p.1 : ℂˣ) : ℂ) * ((ideleNorm K p.1 : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      prof f (Real.log (ideleNorm K p.1)) (p.2 : AdelicGL2 (𝓞 K) K)) *
        conj (Φ (diagOne p.1 * (p.2 : AdelicGL2 (𝓞 K) K))) := by
    funext p
    rw [hFdef]
    dsimp only
    rw [hinner]
  have hFc : Continuous F := by
    rw [hFeq]
    refine Continuous.mul (Continuous.mul (Continuous.mul ?_ ?_) ?_) ?_
    · exact hμPc.comp continuous_fst
    · exact Continuous.cpow (Complex.continuous_ofReal.comp (hNc.comp continuous_fst)) continuous_const
        (fun p => Complex.ofReal_mem_slitPlane.2 (hNpos p.1))
    · exact hPc.comp ((hlogc.comp continuous_fst).prodMk continuous_snd)
    · exact Complex.continuous_conj.comp (hΦc.comp (((continuous_diagOne K).comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)))
  have hhalfre : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  have hTre : ((T : ℂ) * Complex.I + 1 / 2).re = 1 / 2 := by simp
  have hsq : ∀ y : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K y ^ (1 / 2 : ℝ) * ideleNorm K y ^ (1 / 2 : ℝ) = ideleNorm K y := by
    intro y
    rw [← Real.rpow_add (hNpos y)]
    norm_num
  have hFbd : ∀ p, ‖F p‖ ≤ ((∫ t, m₀ t) * CΦ) *
      (ideleNorm K p.1 * Real.exp (-|Real.log (ideleNorm K p.1)|)) := by
    intro p
    rw [hFeq]
    dsimp only
    rw [norm_mul, norm_mul, norm_mul, hμPu, one_mul, Complex.norm_conj, hΦT, norm_mul, norm_mul, hμ'u, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hNpos _), Complex.norm_cpow_eq_rpow_re_of_pos (hNpos _), hhalfre, hTre]
    have h1 := hPbd (Real.log (ideleNorm K p.1)) _ p.2.2
    have h2 := hCΦ _ p.2.2
    have hr : 0 ≤ ideleNorm K p.1 ^ (1 / 2 : ℝ) := Real.rpow_nonneg (hNpos _).le _
    calc ideleNorm K p.1 ^ (1 / 2 : ℝ) * ‖prof f (Real.log (ideleNorm K p.1)) (p.2 : AdelicGL2 (𝓞 K) K)‖ *
          (ideleNorm K p.1 ^ (1 / 2 : ℝ) * ‖Φ (p.2 : AdelicGL2 (𝓞 K) K)‖)
        ≤ ideleNorm K p.1 ^ (1 / 2 : ℝ) * (Real.exp (-|Real.log (ideleNorm K p.1)|) * ∫ t, m₀ t) *
          (ideleNorm K p.1 ^ (1 / 2 : ℝ) * CΦ) := by
          gcongr
      _ = ((∫ t, m₀ t) * CΦ) * ((ideleNorm K p.1 ^ (1 / 2 : ℝ) * ideleNorm K p.1 ^ (1 / 2 : ℝ)) *
            Real.exp (-|Real.log (ideleNorm K p.1)|)) := by ring
      _ = _ := by rw [hsq]

  have hdensm : Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹) :=
    (hNc.measurable.inv).ennreal_ofReal
  set c₀ : ℝ := (∫ t, m₀ t) * CΦ with hc₀
  have hc₀0 : 0 ≤ c₀ := mul_nonneg hM₀ hCΦ0
  have hbm : Measurable fun r : ℝ => c₀ * (r * Real.exp (-|Real.log r|)) :=
    measurable_const.mul (measurable_id.mul (Real.measurable_log.abs.neg.exp))
  have hgm : Measurable fun y : (AdeleRing (𝓞 K) K)ˣ =>
      ENNReal.ofReal (c₀ * (ideleNorm K y * Real.exp (-|Real.log (ideleNorm K y)|))) :=
    (hbm.comp hNc.measurable).ennreal_ofReal
  have hInt : Integrable F ((((NumberField.Idele.idelicHaar K).restrict D).withDensity
      (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
    refine ⟨hFc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ p, ‖F p‖ₑ ∂((((NumberField.Idele.idelicHaar K).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))).prod (maximalCompactHaar K))
        ≤ ∫⁻ p, ENNReal.ofReal (c₀ * (ideleNorm K p.1 * Real.exp (-|Real.log (ideleNorm K p.1)|)))
            ∂((((NumberField.Idele.idelicHaar K).restrict D).withDensity
              (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))).prod (maximalCompactHaar K)) := by
          refine lintegral_mono fun p => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hFbd p)
      _ = ∫⁻ y, ENNReal.ofReal (c₀ * (ideleNorm K y * Real.exp (-|Real.log (ideleNorm K y)|)))
            ∂(((NumberField.Idele.idelicHaar K).restrict D).withDensity
              (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))) := by
          rw [lintegral_prod (fun p : (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
              ENNReal.ofReal (c₀ * (ideleNorm K p.1 * Real.exp (-|Real.log (ideleNorm K p.1)|))))
            ((hgm.comp measurable_fst).aemeasurable)]
          simp only [lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ y in D, ENNReal.ofReal ((ideleNorm K y)⁻¹) *
            ENNReal.ofReal (c₀ * (ideleNorm K y * Real.exp (-|Real.log (ideleNorm K y)|)))
              ∂(NumberField.Idele.idelicHaar K) := by
          rw [lintegral_withDensity_eq_lintegral_mul _ hdensm hgm]
          rfl
      _ = V * ∫⁻ r in Set.Ioi (0 : ℝ), (ENNReal.ofReal r⁻¹ *
            ENNReal.ofReal (c₀ * (r * Real.exp (-|Real.log r|)))) * ENNReal.ofReal r⁻¹ :=
          hV (fun r => ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c₀ * (r * Real.exp (-|Real.log r|))))
            (measurable_inv.ennreal_ofReal.mul hbm.ennreal_ofReal)
      _ = V * (ENNReal.ofReal c₀ * ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-|Real.log r|) * r⁻¹)) := by
          congr 1
          rw [← lintegral_const_mul _ measurable_expNegAbsLogMulInv.ennreal_ofReal]
          refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
          have hr0 : 0 < r := hr
          rw [← ENNReal.ofReal_mul (inv_pos.2 hr0).le, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hc₀0]
          congr 1
          field_simp
      _ < ∞ := ENNReal.mul_lt_top hVT.lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_exp_neg_abs_log_mul_inv_lt_top)
  refine ⟨hInt, ?_⟩

  set t₀ : ℝ := T - τ₀ with ht₀
  have hlineC : Continuous fun t : ℝ => (t : ℂ) * Complex.I := Complex.continuous_ofReal.mul continuous_const
  have hakc : ∀ k : AdelicGL2 (𝓞 K) K, Continuous (fun t : ℝ => f ((t : ℂ) * Complex.I) k) := fun k =>
    hfjc.comp (hlineC.prodMk continuous_const)
  have hak : ∀ k ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      Integrable (fun t : ℝ => f ((t : ℂ) * Complex.I) k) := fun k hk =>
    Integrable.mono' hm₀i (hakc k).aestronglyMeasurable (ae_of_all _ fun t => by
      have := hb₀ 0 (by simp) t k hk
      rwa [Complex.ofReal_zero, zero_add] at this)
  have hap : ∀ k ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      IntegrableOn (fun y : ℝ => ((y ^ (-(0 : ℝ)) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * f ((t : ℂ) * Complex.I) k) (Set.Ioi 0) := by
    intro k hk
    have h6717 := MellinParseval.integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le 0 1 one_pos
      (fun s => f s k) m₀ ((hfhol k).differentiableOn) hm₀i
      (fun σ' hσ' t => hb₀ σ' (by rw [sub_zero] at hσ'; exact hσ'.le) t k hk)
    refine h6717.congr_fun (fun y _ => ?_) measurableSet_Ioi
    dsimp only
    congr 1
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    dsimp only
    rw [Complex.ofReal_zero, zero_add]
  have hmellin : ∀ k ∈ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)),
      ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
        ∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * f ((t : ℂ) * Complex.I) k) =
        ((2 * Real.pi : ℝ) : ℂ) * f ((t₀ : ℂ) * Complex.I) k := fun k hk =>
    MellinParseval.setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul
      (fun t => f ((t : ℂ) * Complex.I) k) (hak k hk) (hakc k) (hap k hk) t₀
  have hprofc : ∀ k : adelicMaximalCompact K, Continuous fun u : ℝ => prof f u (k : AdelicGL2 (𝓞 K) K) :=
    fun k => hPc.comp (continuous_id.prodMk continuous_const)
  have hhm : ∀ k : adelicMaximalCompact K, Measurable (fun r : ℝ =>
      (r : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) * prof f (Real.log r) (k : AdelicGL2 (𝓞 K) K)) := fun k =>
    (Complex.measurable_ofReal.pow_const _).mul ((hprofc k).measurable.comp Real.measurable_log)
  have hμP : ∀ y : (AdeleRing (𝓞 K) K)ˣ, ((μP y : ℂˣ) : ℂ) =
      ((μ' y : ℂˣ) : ℂ) * ((ideleNorm K y : ℝ) : ℂ) ^ (Complex.I * (τ₀ : ℂ)) := by
    intro y
    rw [hmatch, MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply]
  have hμ'1 : ∀ y : (AdeleRing (𝓞 K) K)ˣ, ((μ' y : ℂˣ) : ℂ) * conj ((μ' y : ℂˣ) : ℂ) = 1 := by
    intro y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ'u y]
    simp
  have hptM : ∀ (y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      (ideleNorm K y)⁻¹ • F (y, k) = conj (Φ (k : AdelicGL2 (𝓞 K) K)) *
        (((ideleNorm K y : ℝ) : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
          prof f (Real.log (ideleNorm K y)) (k : AdelicGL2 (𝓞 K) K)) := by
    intro y k
    have hsc := scalar_identity (ideleNorm K y) (hNpos y) _ _ τ₀ T (hμP y) (hμ'1 y)
    simp only [map_mul] at hsc
    rw [hFeq]
    dsimp only
    rw [Complex.real_smul, hΦT]
    simp only [map_mul]
    calc ((((ideleNorm K y)⁻¹ : ℝ)) : ℂ) *
          (((μP y : ℂˣ) : ℂ) * ((ideleNorm K y : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
              prof f (Real.log (ideleNorm K y)) (k : AdelicGL2 (𝓞 K) K) *
            (conj ((μ' y : ℂˣ) : ℂ) * conj (((ideleNorm K y : ℝ) : ℂ) ^ ((T : ℂ) * Complex.I + 1 / 2)) *
              conj (Φ (k : AdelicGL2 (𝓞 K) K))))
        = ((((ideleNorm K y)⁻¹ : ℝ) : ℂ) * (((μP y : ℂˣ) : ℂ) * ((ideleNorm K y : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
            (conj ((μ' y : ℂˣ) : ℂ) * conj (((ideleNorm K y : ℝ) : ℂ) ^ ((T : ℂ) * Complex.I + 1 / 2)))) *
            (prof f (Real.log (ideleNorm K y)) (k : AdelicGL2 (𝓞 K) K) * conj (Φ (k : AdelicGL2 (𝓞 K) K))) := by
          push_cast; ring
      _ = _ := by rw [hsc, ht₀]; ring
  have hinnerY : ∀ k : adelicMaximalCompact K,
      ∫ y, F (y, k) ∂(((NumberField.Idele.idelicHaar K).restrict D).withDensity
        (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))) =
        conj (Φ (k : AdelicGL2 (𝓞 K) K)) *
          (((V.toReal : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * f ((t₀ : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) := by
    intro k
    rw [integral_withDensity_eq_integral_toReal_smul hdensm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hcg : (fun y : (AdeleRing (𝓞 K) K)ˣ => (ENNReal.ofReal (ideleNorm K y)⁻¹).toReal • F (y, k)) =
        fun y => conj (Φ (k : AdelicGL2 (𝓞 K) K)) *
          (((ideleNorm K y : ℝ) : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
            prof f (Real.log (ideleNorm K y)) (k : AdelicGL2 (𝓞 K) K)) := by
      funext y
      rw [ENNReal.toReal_ofReal (inv_nonneg.2 (hNpos y).le), hptM]
    rw [hcg, integral_const_mul, setIntegral_comp_ideleNorm_eq K D V hV hNc.measurable _ (hhm k), ← hmellin _ k.2]
    congr 2
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := hr
    rw [prof]
    congr 3
    funext t
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hr0.ne') ((t : ℂ) * Complex.I),
      ← Complex.ofReal_log hr0.le]
  have hLHS : (∫ y in D, (ideleNorm K y)⁻¹ • ∫ k, F (y, k) ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K)) =
      ∫ y, (∫ k, F (y, k) ∂(maximalCompactHaar K)) ∂(((NumberField.Idele.idelicHaar K).restrict D).withDensity
        (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))) := by
    rw [integral_withDensity_eq_integral_toReal_smul hdensm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    congr 1
    funext y
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 (hNpos y).le)]
  show (∫ y in D, (ideleNorm K y)⁻¹ • ∫ k, F (y, k) ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K)) = _
  calc (∫ y in D, (ideleNorm K y)⁻¹ • ∫ k, F (y, k) ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K))
      = ∫ y, (∫ k, F (y, k) ∂(maximalCompactHaar K)) ∂(((NumberField.Idele.idelicHaar K).restrict D).withDensity
          (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹))) := hLHS
    _ = ∫ k, (∫ y, F (y, k) ∂(((NumberField.Idele.idelicHaar K).restrict D).withDensity
          (fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹)))) ∂(maximalCompactHaar K) := by
        rw [← integral_prod F hInt, integral_prod_symm F hInt]
    _ = ∫ k, conj (Φ (k : AdelicGL2 (𝓞 K) K)) *
          (((V.toReal : ℝ) : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * f ((t₀ : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)))
            ∂(maximalCompactHaar K) := by
        congr 1
        funext k
        exact hinnerY k
    _ = ((V.toReal * (2 * Real.pi) : ℝ) : ℂ) *
          ∫ k, f ((t₀ : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (Φ (k : AdelicGL2 (𝓞 K) K))
            ∂(maximalCompactHaar K) := by
        rw [← integral_const_mul]
        congr 1
        funext k
        push_cast
        ring

end S_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar
end P2MW
export P2MW.S_AutomorphicForm_integrable_and_setIntegral_inv_ideleNorm_smul_integral_lineIntegral_mul_conj_eq_of_isInducedSection_of_eq_mul_normPowChar (solution)
