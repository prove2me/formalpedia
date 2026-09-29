-- Prove2me | solution 1 for AutomorphicForm.exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/ba1ff19a-a65a-59b8-ab02-b0b8e8a298f9

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Theorems.Thm_AutomorphicForm_exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_eq_zero_of_toCarrier_eq_zero
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sqrt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

namespace S14HS0A

section Weight

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

variable (K : Type) [Field K] [NumberField K]

abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

def wtR (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℝ :=
  ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)

def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

variable {K}

scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

scoped instance instRightInvμ : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

theorem wtR_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : 0 < wtR K σ x :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

theorem wt_eq (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : wt K σ x = ((wtR K σ x : ℝ) : ℂ) := rfl

theorem wtR_continuous (σ : ℝ) : Continuous (wtR K σ) :=
  (continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne'

theorem wtR_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ wtR K σ x ∧ wtR K σ x ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  unfold wtR
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hs),
      (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ideleNorm_pos _) h2 hs.le),
      (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)⟩

theorem Wlo_pos (α β σ : ℝ) (hα : 0 < α) (hαβ : α < β) : 0 < min (α ^ (-σ)) (β ^ (-σ)) :=
  lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans hαβ) _)

theorem slab_measurableSet (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab K α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurableSet α β))

theorem eLpNorm_toReal_sq {ν : Measure (AdelicGL2 (𝓞 K) K)} {w : AdelicGL2 (𝓞 K) K → ℂ}
    (hw : MemLp w 2 ν) : (eLpNorm w 2 ν).toReal ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂ν := by
  have hI : 0 ≤ ∫ x, ‖w x‖ ^ 2 ∂ν := integral_nonneg fun x => by positivity
  rw [hw.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

theorem integrable_normSq_mul_wtR (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ slab K α β) (w : AdelicGL2 (𝓞 K) K → ℂ) (hw : MemLp w 2 ((μ K).restrict Φ₀)) :
    Integrable (fun x => ‖w x‖ ^ 2 * wtR K σ x) ((μ K).restrict Φ₀) := by
  have hsq : Integrable (fun x => ‖w x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  have hmeas : AEStronglyMeasurable (wtR K σ) ((μ K).restrict Φ₀) := (wtR_continuous σ).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wtR K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
    filter_upwards [ae_mem_slab α β Φ₀ hΦ₀] with x hx
    rw [Real.norm_of_nonneg (wtR_pos σ x).le]
    exact (wtR_bounds α β σ hα x hx).2
  exact (hsq.bdd_mul hmeas hbd).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem integral_normSq_mul_wtR_le (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ slab K α β) (w : AdelicGL2 (𝓞 K) K → ℂ) (hw : MemLp w 2 ((μ K).restrict Φ₀)) :
    ∫ x in Φ₀, ‖w x‖ ^ 2 * wtR K σ x ∂(μ K) ≤ max (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖w x‖ ^ 2 ∂(μ K) := by
  have hsq : Integrable (fun x => ‖w x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  rw [← integral_const_mul]
  refine integral_mono_ae (integrable_normSq_mul_wtR α β σ hα Φ₀ hΦ₀ w hw) (hsq.const_mul _)
    ((ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => ?_)
  show ‖w x‖ ^ 2 * wtR K σ x ≤ max (α ^ (-σ)) (β ^ (-σ)) * ‖w x‖ ^ 2
  rw [mul_comm (max _ _)]
  exact mul_le_mul_of_nonneg_left (wtR_bounds α β σ hα x hx).2 (sq_nonneg _)

theorem mul_integral_normSq_le (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ slab K α β) (w : AdelicGL2 (𝓞 K) K → ℂ) (hw : MemLp w 2 ((μ K).restrict Φ₀)) :
    min (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖w x‖ ^ 2 ∂(μ K) ≤ ∫ x in Φ₀, ‖w x‖ ^ 2 * wtR K σ x ∂(μ K) := by
  have hsq : Integrable (fun x => ‖w x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  rw [← integral_const_mul]
  refine integral_mono_ae (hsq.const_mul _) (integrable_normSq_mul_wtR α β σ hα Φ₀ hΦ₀ w hw)
    ((ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => ?_)
  show min (α ^ (-σ)) (β ^ (-σ)) * ‖w x‖ ^ 2 ≤ ‖w x‖ ^ 2 * wtR K σ x
  rw [mul_comm (min _ _)]
  exact mul_le_mul_of_nonneg_left (wtR_bounds α β σ hα x hx).1 (sq_nonneg _)

end Weight

section Pairing

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

variable {X : Type*} [MeasurableSpace X] {ρ : Measure X}

theorem integrable_mul_conj (a b : X → ℂ) (ha : MemLp a 2 ρ) (hb : MemLp b 2 ρ) :
    Integrable (fun x => a x * conj (b x)) ρ := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha.1).1 ha
  have hb' := (memLp_two_iff_integrable_sq_norm hb.1).1 hb
  have hpt : ∀ x, ‖a x * conj (b x)‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hm : AEStronglyMeasurable (fun x => a x * conj (b x)) ρ :=
    ha.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hb.1)
  exact Integrable.mono' ((ha'.add hb').div_const 2) hm (Filter.Eventually.of_forall hpt)

theorem integral_norm_sq_eq_re (w : X → ℂ) :
    ∫ x, ‖w x‖ ^ 2 ∂ρ = RCLike.re (∫ x, w x * conj (w x) ∂ρ) := by
  have h2 : (fun x => w x * conj (w x)) = fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [h2, integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]

theorem integral_mul_conj_self_eq (w : X → ℂ) :
    ∫ x, w x * conj (w x) ∂ρ = ((∫ x, ‖w x‖ ^ 2 ∂ρ : ℝ) : ℂ) := by
  have h2 : (fun x => w x * conj (w x)) = fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [h2, integral_complex_ofReal]

theorem norm_integral_mul_conj_le (a b : X → ℂ) (ha : MemLp a 2 ρ) (hb : MemLp b 2 ρ) :
    ‖∫ x, a x * conj (b x) ∂ρ‖ ≤ Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂ρ) * Real.sqrt (∫ x, ‖b x‖ ^ 2 ∂ρ) := by

  have hinner : ∫ x, a x * conj (b x) ∂ρ = ⟪hb.toLp b, ha.toLp a⟫_ℂ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
    rw [hxa, hxb, RCLike.inner_apply, mul_comm]
  have hna : ‖ha.toLp a‖ = Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂ρ) := by
    rw [Lp.norm_toLp, ← Real.sqrt_sq ENNReal.toReal_nonneg, eLpNorm_toReal_sq' ha]
  have hnb : ‖hb.toLp b‖ = Real.sqrt (∫ x, ‖b x‖ ^ 2 ∂ρ) := by
    rw [Lp.norm_toLp, ← Real.sqrt_sq ENNReal.toReal_nonneg, eLpNorm_toReal_sq' hb]
  rw [hinner, ← hna, ← hnb, mul_comm]
  exact norm_inner_le_norm _ _
where

  eLpNorm_toReal_sq' {w : X → ℂ} (hw : MemLp w 2 ρ) : (eLpNorm w 2 ρ).toReal ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂ρ := by
    have hI : 0 ≤ ∫ x, ‖w x‖ ^ 2 ∂ρ := integral_nonneg fun x => by positivity
    rw [hw.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
    simp only [Real.rpow_two]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast, ← Real.rpow_mul hI]
    norm_num

theorem integral_norm_sq_sum_smul_le {m : ℕ} (y : Fin m → X → ℂ) (hy : ∀ l, MemLp (y l) 2 ρ) (c : Fin m → ℂ) :
    ∫ x, ‖(∑ l, c l • y l) x‖ ^ 2 ∂ρ ≤ (∑ l, ‖c l‖ ^ 2) * ∑ l, ∫ x, ‖y l x‖ ^ 2 ∂ρ := by
  have hsum : MemLp (∑ l, c l • y l) 2 ρ := memLp_finsetSum' _ fun l _ => (hy l).const_smul (c l)

  have htri : (eLpNorm (∑ l, c l • y l) 2 ρ).toReal ≤ ∑ l, ‖c l‖ * (eLpNorm (y l) 2 ρ).toReal := by
    have h1 : eLpNorm (∑ l, c l • y l) 2 ρ ≤ ∑ l, eLpNorm (c l • y l) 2 ρ :=
      eLpNorm_sum_le (fun l _ => ((hy l).const_smul (c l)).1) one_le_two
    have h2 : ∀ l, eLpNorm (c l • y l) 2 ρ = ‖c l‖ₑ * eLpNorm (y l) 2 ρ := fun l => eLpNorm_const_smul _ _ _ _
    have hfin : ∀ l ∈ Finset.univ, eLpNorm (c l • y l) 2 ρ ≠ ∞ := fun l _ => ((hy l).const_smul (c l)).2.ne
    calc (eLpNorm (∑ l, c l • y l) 2 ρ).toReal ≤ (∑ l, eLpNorm (c l • y l) 2 ρ).toReal :=
          ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) h1
      _ = ∑ l, (eLpNorm (c l • y l) 2 ρ).toReal := ENNReal.toReal_sum hfin
      _ = ∑ l, ‖c l‖ * (eLpNorm (y l) 2 ρ).toReal := Finset.sum_congr rfl fun l _ => by
          rw [h2 l, ENNReal.toReal_mul, toReal_enorm]
  have hcs : (∑ l, ‖c l‖ * (eLpNorm (y l) 2 ρ).toReal) ^ 2 ≤
      (∑ l, ‖c l‖ ^ 2) * ∑ l, (eLpNorm (y l) 2 ρ).toReal ^ 2 := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun l => ‖c l‖) (fun l => (eLpNorm (y l) 2 ρ).toReal)
    have hA : 0 ≤ ∑ l, ‖c l‖ ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
    have hB : 0 ≤ ∑ l, (eLpNorm (y l) 2 ρ).toReal ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
    have hL : 0 ≤ ∑ l, ‖c l‖ * (eLpNorm (y l) 2 ρ).toReal :=
      Finset.sum_nonneg fun l _ => mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    calc (∑ l, ‖c l‖ * (eLpNorm (y l) 2 ρ).toReal) ^ 2
        ≤ (Real.sqrt (∑ l, ‖c l‖ ^ 2) * Real.sqrt (∑ l, (eLpNorm (y l) 2 ρ).toReal ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hL h 2
      _ = (∑ l, ‖c l‖ ^ 2) * ∑ l, (eLpNorm (y l) 2 ρ).toReal ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  rw [← eLpNorm_toReal_sq'' hsum]
  simp_rw [← eLpNorm_toReal_sq'' (hy _)]
  exact (pow_le_pow_left₀ ENNReal.toReal_nonneg htri 2).trans hcs
where
  eLpNorm_toReal_sq'' {w : X → ℂ} (hw : MemLp w 2 ρ) : (eLpNorm w 2 ρ).toReal ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂ρ := by
    have hI : 0 ≤ ∫ x, ‖w x‖ ^ 2 ∂ρ := integral_nonneg fun x => by positivity
    rw [hw.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
    simp only [Real.rpow_two]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast, ← Real.rpow_mul hI]
    norm_num

theorem integral_norm_sq_sum_smul {n : ℕ} (e : Fin n → X → ℂ) (he : ∀ j, MemLp (e j) 2 ρ)
    (horth : ∀ j j', j ≠ j' → ∫ x, e j x * conj (e j' x) ∂ρ = 0) (a : Fin n → ℂ) :
    ∫ x, ‖(∑ j, a j • e j) x‖ ^ 2 ∂ρ = ∑ j, ‖a j‖ ^ 2 * ∫ x, ‖e j x‖ ^ 2 ∂ρ := by
  have hint : ∀ j j', Integrable (fun x => e j x * conj (e j' x)) ρ := fun j j' => integrable_mul_conj _ _ (he j) (he j')
  have hexp : ∀ x, (∑ j, a j • e j) x * conj ((∑ j, a j • e j) x) =
      ∑ j, ∑ j', a j' * conj (a j) * (e j' x * conj (e j x)) := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  have hI : ∫ x, (∑ j, a j • e j) x * conj ((∑ j, a j • e j) x) ∂ρ =
      ∑ j, ((‖a j‖ ^ 2 * ∫ x, ‖e j x‖ ^ 2 ∂ρ : ℝ) : ℂ) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun j' _ => (hint j' j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun j' _ => (hint j' j).const_mul _]
    rw [Finset.sum_eq_single j]
    · rw [integral_const_mul, Complex.ofReal_mul, Complex.ofReal_pow, integral_mul_conj_self_eq (e j),
        Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    · intro j' _ hj'
      rw [integral_const_mul, horth j' j hj', mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [integral_norm_sq_eq_re, hI]
  simp only [map_sum, RCLike.re_to_complex, Complex.ofReal_re]

variable {K : Type} [Field K] [NumberField K]

theorem pairing_eq_integral_sqrtwt (Φ : Set (AdelicGL2 (𝓞 K) K)) (σ : ℝ) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    CuspidalSpectrum.pairing K Φ σ a b =
      ∫ x in Φ, (a x * ((Real.sqrt (wtR K σ x) : ℝ) : ℂ)) * conj (b x * ((Real.sqrt (wtR K σ x) : ℝ) : ℂ))
        ∂(μ K) := by
  rw [CuspidalSpectrum.pairing_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hs : ((Real.sqrt (wtR K σ x) : ℝ) : ℂ) * ((Real.sqrt (wtR K σ x) : ℝ) : ℂ) = ((wtR K σ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (wtR_pos σ x).le]
  simp only [map_mul, Complex.conj_ofReal]
  show a x * conj (b x) * ((wtR K σ x : ℝ) : ℂ) = _
  rw [← hs]
  ring

theorem memLp_mul_sqrtwt (α β σ : ℝ) (hα : 0 < α) (Φ : Set (AdelicGL2 (𝓞 K) K)) (hΦ : Φ ⊆ slab K α β)
    (a : AdelicGL2 (𝓞 K) K → ℂ) (ha : MemLp a 2 ((μ K).restrict Φ)) :
    MemLp (fun x => a x * ((Real.sqrt (wtR K σ x) : ℝ) : ℂ)) 2 ((μ K).restrict Φ) ∧
      ∫ x in Φ, ‖a x * ((Real.sqrt (wtR K σ x) : ℝ) : ℂ)‖ ^ 2 ∂(μ K) = ∫ x in Φ, ‖a x‖ ^ 2 * wtR K σ x ∂(μ K) := by
  have hcont : Continuous fun x => ((Real.sqrt (wtR K σ x) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (wtR_continuous σ))
  have hbd : ∀ᵐ x ∂((μ K).restrict Φ), ‖a x * ((Real.sqrt (wtR K σ x) : ℝ) : ℂ)‖ ≤
      Real.sqrt (max (α ^ (-σ)) (β ^ (-σ))) * ‖a x‖ := by
    filter_upwards [ae_mem_slab α β Φ hΦ] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (wtR_bounds α β σ hα x hx).2) (norm_nonneg _)
  refine ⟨MemLp.of_le_mul ha (ha.1.mul hcont.aestronglyMeasurable) hbd, ?_⟩
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (wtR_pos σ x).le]

theorem norm_pairing_le (α β σ : ℝ) (hα : 0 < α) (Φ : Set (AdelicGL2 (𝓞 K) K)) (hΦ : Φ ⊆ slab K α β)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (ha : MemLp a 2 ((μ K).restrict Φ)) (hb : MemLp b 2 ((μ K).restrict Φ)) :
    ‖CuspidalSpectrum.pairing K Φ σ a b‖ ≤
      Real.sqrt (∫ x in Φ, ‖a x‖ ^ 2 * wtR K σ x ∂(μ K)) * Real.sqrt (∫ x in Φ, ‖b x‖ ^ 2 * wtR K σ x ∂(μ K)) := by
  obtain ⟨ha', hai⟩ := memLp_mul_sqrtwt α β σ hα Φ hΦ a ha
  obtain ⟨hb', hbi⟩ := memLp_mul_sqrtwt α β σ hα Φ hΦ b hb
  rw [pairing_eq_integral_sqrtwt, ← hai, ← hbi]
  exact norm_integral_mul_conj_le _ _ ha' hb'

theorem pairing_self_eq (Φ : Set (AdelicGL2 (𝓞 K) K)) (σ : ℝ) (a : AdelicGL2 (𝓞 K) K → ℂ) :
    CuspidalSpectrum.pairing K Φ σ a a = ((∫ x in Φ, ‖a x‖ ^ 2 * wtR K σ x ∂(μ K) : ℝ) : ℂ) := by
  rw [CuspidalSpectrum.pairing_def, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show a x * conj (a x) * ((wtR K σ x : ℝ) : ℂ) = (((‖a x‖ ^ 2 * wtR K σ x : ℝ)) : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.ofReal_pow]

theorem integrable_pairingIntegrand (α β σ : ℝ) (hα : 0 < α) (Φ : Set (AdelicGL2 (𝓞 K) K)) (hΦ : Φ ⊆ slab K α β)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (ha : MemLp a 2 ((μ K).restrict Φ)) (hb : MemLp b 2 ((μ K).restrict Φ)) :
    Integrable (fun x => a x * conj (b x) * wt K σ x) ((μ K).restrict Φ) := by
  have h1 : Integrable (fun x => a x * conj (b x)) ((μ K).restrict Φ) := integrable_mul_conj a b ha hb
  have hmeas : AEStronglyMeasurable (wt K σ) ((μ K).restrict Φ) :=
    (Complex.continuous_ofReal.comp (wtR_continuous σ)).aestronglyMeasurable
  have hbd : ∀ᵐ x ∂((μ K).restrict Φ), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
    filter_upwards [ae_mem_slab α β Φ hΦ] with x hx
    rw [wt_eq, Complex.norm_real, Real.norm_of_nonneg (wtR_pos σ x).le]
    exact (wtR_bounds α β σ hα x hx).2
  exact (h1.bdd_mul hmeas hbd).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem pairing_sum_left (α β σ : ℝ) (hα : 0 < α) (Φ : Set (AdelicGL2 (𝓞 K) K)) (hΦ : Φ ⊆ slab K α β)
    {n : ℕ} (a : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (ha : ∀ k, MemLp (a k) 2 ((μ K).restrict Φ))
    (b : AdelicGL2 (𝓞 K) K → ℂ) (hb : MemLp b 2 ((μ K).restrict Φ)) :
    CuspidalSpectrum.pairing K Φ σ (fun x => ∑ k, a k x) b = ∑ k, CuspidalSpectrum.pairing K Φ σ (a k) b := by
  simp only [CuspidalSpectrum.pairing_def, Finset.sum_mul]
  exact integral_finsetSum Finset.univ fun k _ => integrable_pairingIntegrand α β σ hα Φ hΦ (a k) b (ha k) hb

end Pairing

section CuspData

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm

open scoped ProbabilityTheory ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel

variable {K : Type} [Field K] [NumberField K]

theorem integrable_constantTermIntegrand
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (g : AdelicGL2 (𝓞 K) K) :
    Integrable (constantTermIntegrand unipotentGL2 f g)
      ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  have hcont : Continuous (constantTermIntegrand unipotentGL2 f g) :=
    hf.comp ((CuspidalSpectrum.continuous_unipotentGL2_adele K).mul continuous_const)
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hint : IntegrableOn (constantTermIntegrand unipotentGL2 f g) (adelicBox K)
      (adelicAddHaar (𝓞 K) K) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  exact hint.smul_measure (ENNReal.inv_ne_top.2 (adelicAddHaar_adelicBox_pos K).ne')

variable (K) in

def cuspData (Φ : Set (AdelicGL2 (𝓞 K) K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧
    IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ ∧
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ)}
  zero_mem' :=
    ⟨continuous_const, isLsXiFunction_zero (𝓞 K) K ⊤ ξ, fun g => constantTerm_zero _ _ g, MemLp.zero⟩
  add_mem' := by
    rintro φ ψ ⟨hφc, hφl, hφz, hφ2⟩ ⟨hψc, hψl, hψz, hψ2⟩
    refine ⟨hφc.add hψc, ⟨fun γ g => ?_, fun z g => ?_⟩, fun g => ?_, hφ2.add hψ2⟩
    · simp only [Pi.add_apply, hφl.left_invariant, hψl.left_invariant]
    · simp only [Pi.add_apply, hφl.central_transform, hψl.central_transform, mul_add]
    · have h1 := hφz g
      have h2 := hψz g
      have hsplit : constantTermIntegrand unipotentGL2 (φ + ψ) g =
          fun q => constantTermIntegrand unipotentGL2 φ g q + constantTermIntegrand unipotentGL2 ψ g q := rfl
      unfold constantTerm at h1 h2 ⊢
      rw [hsplit, integral_add (integrable_constantTermIntegrand hφc g) (integrable_constantTermIntegrand hψc g),
        h1, h2, add_zero]
  smul_mem' := by
    rintro c φ ⟨hφc, hφl, hφz, hφ2⟩
    refine ⟨hφc.const_smul c, ⟨fun γ g => ?_, fun z g => ?_⟩, fun g => ?_, hφ2.const_smul c⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hφl.left_invariant]
    · simp only [Pi.smul_apply, smul_eq_mul, hφl.central_transform, mul_left_comm]
    · have h1 := hφz g
      have hsplit : constantTermIntegrand unipotentGL2 (c • φ) g =
          fun q => c * constantTermIntegrand unipotentGL2 φ g q := rfl
      unfold constantTerm at h1 ⊢
      rw [hsplit, integral_const_mul, h1, mul_zero]

theorem mem_cuspData_iff {Φ : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} :
    φ ∈ cuspData K Φ ξ ↔ Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧
      IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ ∧
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
  Iff.rfl

theorem isotypicCuspSubmodule_le_cuspData (W : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)) (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (Ψ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Ψ ≤ cuspData K W ξ := by
  refine Submodule.span_le.2 fun φ hφ => ?_
  have h : IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Ψ φ := hφ
  have hcusp : IsCuspAutomorphicFnAt K (productionPinsOf K W U gen (adelicBox K)) ξ φ := h.smoothCusp.1
  have hmem : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ W φ := hcusp.1
  obtain ⟨hl, h2⟩ := (lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ W φ).1 hmem
  exact ⟨h.continuous, hl, hcusp.2, h2⟩

theorem isotypicCuspSubmodule_le_contMemberSubmodule (W : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)) (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (Ψ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Ψ ≤
      CuspidalSpectrum.contMemberSubmodule K W ξ := by
  intro φ hφ
  obtain ⟨hc, hl, -, h2⟩ := mem_cuspData_iff.1 (isotypicCuspSubmodule_le_cuspData W U gen ξ N S Ψ hφ)
  exact ⟨(CuspidalSpectrum.mem_memberSubmodule_iff' K W ξ φ).2 ⟨hl, h2⟩, hc⟩

theorem cuspData_le_contMemberSubmodule (W : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :
    cuspData K W ξ ≤ CuspidalSpectrum.contMemberSubmodule K W ξ := by
  intro φ hφ
  obtain ⟨hc, hl, -, h2⟩ := mem_cuspData_iff.1 hφ
  exact ⟨(CuspidalSpectrum.mem_memberSubmodule_iff' K W ξ φ).2 ⟨hl, h2⟩, hc⟩

theorem rightConv_sum_smul_apply {n : ℕ} (e : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (he : ∀ j, Continuous (e j))
    (a : Fin n → ℂ) (h : AdelicGL2 (𝓞 K) K → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h)
    (d : AdelicGL2 (𝓞 K) K) :
    rightConv K (∑ j, a j • e j) h d = ∑ j, a j * rightConv K (e j) h d := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hint : ∀ j, Integrable (fun y => e j (d * y) * h y) (adelicGLHaar (Fin 2) (𝓞 K) K) := fun j =>
    (((he j).comp (continuous_const.mul continuous_id)).mul hh).integrable_of_hasCompactSupport hhc.mul_left
  simp only [rightConv_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => by simpa only [mul_assoc] using (hint j).const_mul (a j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

theorem rightConv_sum_smul {n : ℕ} (e : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (he : ∀ j, Continuous (e j))
    (a : Fin n → ℂ) (h : AdelicGL2 (𝓞 K) K → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    rightConv K (∑ j, a j • e j) h = ∑ j, a j • rightConv K (e j) h := by
  funext d
  rw [rightConv_sum_smul_apply e he a h hh hhc d]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem rightConv_add_left (u v h : AdelicGL2 (𝓞 K) K → ℂ) (hu : Continuous u) (hv : Continuous v)
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    rightConv K (u + v) h = rightConv K u h + rightConv K v h := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  funext d
  have hiu : Integrable (fun y => u (d * y) * h y) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    ((hu.comp (continuous_const.mul continuous_id)).mul hh).integrable_of_hasCompactSupport hhc.mul_left
  have hiv : Integrable (fun y => v (d * y) * h y) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    ((hv.comp (continuous_const.mul continuous_id)).mul hh).integrable_of_hasCompactSupport hhc.mul_left
  simp only [rightConv_apply, Pi.add_apply, add_mul]
  exact integral_add hiu hiv

theorem rightConv_smul_left (c : ℂ) (u h : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K (c • u) h = c • rightConv K u h := by
  funext d
  simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem rightConv_zero_left (h : AdelicGL2 (𝓞 K) K → ℂ) : rightConv K (0 : AdelicGL2 (𝓞 K) K → ℂ) h = 0 := by
  funext d
  simp [rightConv_apply]

end CuspData

section Assoc

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open MeasureTheory.Measure
open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

variable {K : Type} [Field K] [NumberField K]

scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

scoped instance countable_ringOfIntegers : Countable (𝓞 K) :=
  (NumberField.RingOfIntegers.coe_injective (K := K)).countable

scoped instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  refine (Function.Surjective.countable (f := fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) ?_)
  intro I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  exact ⟨s, hs⟩

scoped instance countable_heightOneSpectrum : Countable (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  Function.Injective.countable (f := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h

open scoped RestrictedProduct in
scoped instance secondCountable_finiteAdeleRing :
    SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometry_toCompletion (v := v)).isEmbedding.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem kernel_integrable (u g h : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hh : Continuous h) (hhc : HasCompactSupport h) (x : AdelicGL2 (𝓞 K) K) :
    Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (x * p.1) * (g p.2 * h (p.2⁻¹ * p.1)))
      ((μ K).prod (μ K)) := by
  have hcont : Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (x * p.1) * (g p.2 * h (p.2⁻¹ * p.1)) :=
    (huc.comp (continuous_const.mul continuous_fst)).mul
      ((hg.comp continuous_snd).mul (hh.comp (continuous_snd.inv.mul continuous_fst)))
  have hsupp : HasCompactSupport
      fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (x * p.1) * (g p.2 * h (p.2⁻¹ * p.1)) := by
    refine HasCompactSupport.intro (((hgc : IsCompact (tsupport g)).mul (hhc : IsCompact (tsupport h))).prod hgc)
      fun p hp => ?_
    by_contra hne
    apply hp
    have hg' : g p.2 ≠ 0 := fun h0 => hne (by simp [h0])
    have hh' : h (p.2⁻¹ * p.1) ≠ 0 := fun h0 => hne (by simp [h0])
    refine Set.mk_mem_prod ?_ (subset_tsupport g hg')
    have : p.1 = p.2 * (p.2⁻¹ * p.1) := by group
    rw [this]
    exact Set.mul_mem_mul (subset_tsupport g hg') (subset_tsupport h hh')
  exact hcont.integrable_of_hasCompactSupport hsupp

theorem rightConv_rightConv_inv (u g h : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hh : Continuous h) (hhc : HasCompactSupport h) :
    rightConv K u (rightConv K g fun y => h y⁻¹) = rightConv K (rightConv K u h) g := by
  funext x
  have e₁ : ∀ z : AdelicGL2 (𝓞 K) K, rightConv K g (fun y => h y⁻¹) z = ∫ y, g y * h (y⁻¹ * z) ∂(μ K) := by
    intro z
    rw [rightConv_apply]
    have hl := integral_mul_left_eq_self (μ := μ K) (fun y => g y * h (y⁻¹ * z)) z
    simp only [mul_inv_rev, inv_mul_cancel_right] at hl
    exact hl
  have e₂ : ∀ y : AdelicGL2 (𝓞 K) K, ∫ z, u (x * z) * h (y⁻¹ * z) ∂(μ K) = rightConv K u h (x * y) := by
    intro y
    rw [rightConv_apply, ← integral_mul_left_eq_self (μ := μ K) (fun z => u (x * z) * h (y⁻¹ * z)) y]
    simp only [inv_mul_cancel_left, mul_assoc]
  have hint := kernel_integrable u g h huc hg hgc hh hhc x
  calc rightConv K u (rightConv K g fun y => h y⁻¹) x
      = ∫ z, u (x * z) * ∫ y, g y * h (y⁻¹ * z) ∂(μ K) ∂(μ K) := by
        rw [rightConv_apply]
        simp only [e₁]
    _ = ∫ z, ∫ y, u (x * z) * (g y * h (y⁻¹ * z)) ∂(μ K) ∂(μ K) := by
        simp only [integral_const_mul]
    _ = ∫ y, ∫ z, u (x * z) * (g y * h (y⁻¹ * z)) ∂(μ K) ∂(μ K) := integral_integral_swap hint
    _ = ∫ y, g y * ∫ z, u (x * z) * h (y⁻¹ * z) ∂(μ K) ∂(μ K) := by
        congr 1
        funext y
        rw [← integral_const_mul]
        congr 1
        funext z
        ring
    _ = ∫ y, rightConv K u h (x * y) * g y ∂(μ K) := by
        simp only [e₂, mul_comm]
    _ = rightConv K (rightConv K u h) g x := (rightConv_apply K _ _ x).symm

theorem continuous_rightConv_of_hasCompactSupport (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Continuous (rightConv K u g) := by
  have hconv : rightConv K u g = fun x => ∫ y, u (x * y) * g y ∂(μ K) := funext fun x => rightConv_apply K u g x
  rw [hconv, continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hNc.mul (hgc : IsCompact (tsupport g))).exists_bound_of_continuousOn huc.continuousOn
  refine continuousAt_of_dominated (bound := fun y => M * ‖g y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((huc.comp (continuous_const.mul continuous_id)).mul hg).aestronglyMeasurable
  · refine Filter.eventually_of_mem hN fun x hx => Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport g
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mul_mem_mul hx hy)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hg.norm.integrable_of_hasCompactSupport hgc.norm).const_mul M
  · exact Filter.Eventually.of_forall fun y =>
      ((huc.comp (continuous_id.mul continuous_const)).mul continuous_const).continuousAt

theorem hasCompactSupport_rightConv_inv (g h : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h) : HasCompactSupport (rightConv K g fun y => h y⁻¹) := by
  refine HasCompactSupport.intro ((hgc : IsCompact (tsupport g)).mul (hhc : IsCompact (tsupport h))) fun x hx => ?_
  rw [rightConv_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : h y⁻¹ = 0
  · simp [hy]
  have hgx : g (x * y) = 0 := by
    by_contra hgx
    apply hx
    have : x = x * y * y⁻¹ := by group
    rw [this]
    exact Set.mul_mem_mul (subset_tsupport g hgx) (subset_tsupport h hy)
  simp [hgx]

theorem rightConv_sum_right (u : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (F : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ k, Continuous (F k)) (hFc : ∀ k, HasCompactSupport (F k)) :
    rightConv K u (∑ k, F k) = ∑ k, rightConv K u (F k) := by
  funext x
  simp only [rightConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun k _ =>
    ((huc.comp (continuous_const.mul continuous_id)).mul (hF k)).integrable_of_hasCompactSupport (hFc k).mul_left

theorem rightConv_eq_sum_of_forall_eq_sum (u f : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (g h : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hg : ∀ k, Continuous (g k)) (hgc : ∀ k, HasCompactSupport (g k))
    (hh : ∀ k, Continuous (h k)) (hhc : ∀ k, HasCompactSupport (h k))
    (hf : ∀ x, f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x) :
    rightConv K u f = ∑ k, rightConv K (rightConv K u (h k)) (g k) := by
  have hf' : f = ∑ k, rightConv K (g k) fun y => h k y⁻¹ := by
    funext x
    rw [hf x, Finset.sum_apply]
  have hinvc : ∀ k, Continuous fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k => (hh k).comp continuous_inv
  have hinvcs : ∀ k, HasCompactSupport fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k =>
    (hhc k).comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  rw [hf', rightConv_sum_right u huc _
    (fun k => continuous_rightConv_of_hasCompactSupport (g k) _ (hg k) (hinvc k) (hinvcs k))
    (fun k => hasCompactSupport_rightConv_inv (g k) (h k) (hgc k) (hhc k))]
  exact Finset.sum_congr rfl fun k _ => rightConv_rightConv_inv u (g k) (h k) huc (hg k) (hgc k) (hh k) (hhc k)

end Assoc

section GramSchmidt

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def ip (Φ : Set (AdelicGL2 (𝓞 K) K)) (a b : AdelicGL2 (𝓞 K) K → ℂ) : ℂ :=
  ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K

theorem ip_def (Φ : Set (AdelicGL2 (𝓞 K) K)) (a b : AdelicGL2 (𝓞 K) K → ℂ) :
    ip K Φ a b = ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K := rfl

theorem weightedMeasure_zero_eq (Φ : Set (AdelicGL2 (𝓞 K) K)) :
    weightedMeasure K Φ 0 = (adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ := by
  rw [weightedMeasure_def]
  have hone : (fun x => ENNReal.ofReal (weight K 0 x)) = (1 : AdelicGL2 (𝓞 K) K → ENNReal) := by
    funext x
    simp [weight_def]
  rw [hone, withDensity_one]

theorem exists_orthonormal_spanning {α β : ℝ} {Φ : Set (AdelicGL2 (𝓞 K) K)}
    (hΦ₀ : IsSlabFundamentalDomain K α β Φ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (P : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (hP : P ≤ contMemberSubmodule K Φ ξ) [FiniteDimensional ℂ ↥P] :
    ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ k, e k ∈ P) ∧ (∀ k l, ip K Φ (e k) (e l) = if l = k then 1 else 0) ∧
      Submodule.span ℂ (Set.range e) = P := by
  have hcont : ∀ x : ↥P, (x : AdelicGL2 (𝓞 K) K → ℂ) ∈ contMemberSubmodule K Φ ξ := fun x => hP x.2
  have hle : P ≤ memberSubmodule K Φ ξ := fun _ hx => (hP hx).1
  obtain ⟨T, hT⟩ : ∃ T : ↥P →ₗ[ℂ] Carrier K Φ 0, T = (toCarrier K hΦ₀ 0 ξ).comp (Submodule.inclusion hle) :=
    ⟨_, rfl⟩
  have hTcoe : ∀ x : ↥P, ⇑(T x) =ᵐ[weightedMeasure K Φ 0] (x : AdelicGL2 (𝓞 K) K → ℂ) := by
    intro x
    rw [hT]
    exact MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem K hΦ₀ 0 (hle x.2))
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun x hx => Subtype.ext ?_
    rw [hT] at hx
    exact eq_zero_of_toCarrier_eq_zero K hΦ₀ 0 ξ (x : AdelicGL2 (𝓞 K) K → ℂ) (hcont x) hx
  have hpair : ∀ x y : ↥P,
      ip K Φ (x : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K → ℂ) = inner ℂ (T y) (T x) := by
    intro x y
    rw [L2.inner_def]
    simp_rw [RCLike.inner_apply]
    unfold ip
    rw [← weightedMeasure_zero_eq]
    refine integral_congr_ae ?_
    filter_upwards [hTcoe x, hTcoe y] with g hx hy
    rw [hx, hy]
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥P ≃ₗ[ℂ] ↥(LinearMap.range T),
      ∀ x, ((φ x : ↥(LinearMap.range T)) : Carrier K Φ 0) = T x :=
    ⟨LinearEquiv.ofInjective T hinj, fun _ => rfl⟩
  obtain ⟨m, ⟨e⟩⟩ : ∃ m : ℕ, Nonempty (OrthonormalBasis (Fin m) ℂ ↥(LinearMap.range T)) :=
    ⟨_, ⟨stdOrthonormalBasis ℂ ↥(LinearMap.range T)⟩⟩
  obtain ⟨bas, hbas⟩ : ∃ bas : Module.Basis (Fin m) ℂ ↥P, ∀ k, bas k = φ.symm (e k) :=
    ⟨e.toBasis.map φ.symm, fun k => by rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]⟩
  have hTbas : ∀ k, T (bas k) = ((e k : ↥(LinearMap.range T)) : Carrier K Φ 0) := by
    intro k
    rw [hbas, ← hφ, LinearEquiv.apply_symm_apply]
  refine ⟨m, fun k => (bas k : AdelicGL2 (𝓞 K) K → ℂ), fun k => (bas k).2, fun k l => ?_, ?_⟩
  · rw [hpair, hTbas, hTbas]
    exact orthonormal_iff_ite.1 e.orthonormal l k
  · refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun k => (bas k).2)) fun x hx => ?_
    have h := Submodule.mem_map_of_mem (f := P.subtype) (bas.mem_span ⟨x, hx⟩)
    rw [← Submodule.span_image, ← Set.range_comp'] at h
    exact h

theorem integral_norm_sq_eq_one_of_ip_eq_one (Φ : Set (AdelicGL2 (𝓞 K) K)) (e : AdelicGL2 (𝓞 K) K → ℂ)
    (h : ip K Φ e e = 1) : ∫ g in Φ, ‖e g‖ ^ 2 ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1 := by
  rw [integral_norm_sq_eq_re, ← ip_def, h]
  simp

end GramSchmidt

section Frame

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

theorem exists_sigma_of_continuous_of_trivial
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1) :
    ∃ σ : ℝ, ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ := by
  let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ξ.comp Subgroup.topEquiv.symm.toMonoidHom
  have hclass : IsIdeleClassChar (𝓞 K) K χ := fun u =>
    hξt _ (MonoidHom.mem_range.2 ⟨u, rfl⟩)
  have hcont : Continuous χ := by
    refine Units.continuous_iff.2 ⟨hξc, ?_⟩
    have h1 : (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z)⁻¹ : ℂˣ).val) =
        (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∘ fun z => z⁻¹ := by
      funext z
      simp only [Function.comp_apply, ← map_inv]
      rfl
    rw [h1]
    exact hξc.comp continuous_inv
  obtain ⟨σ, hσ⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K χ hclass hcont
  exact ⟨σ, fun z => hσ z⟩

private theorem _root_.S14HS0A.exists_notMem_finset (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "S14HS0A" "exists_notMem_finset"

theorem ne_bot_of_forall_dvd_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_notMem_finset S
  exact hw (hN w ⟨⊥, by rw [Ideal.mul_bot]⟩)

end Frame

section Level

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

variable {K : Type} [Field K] [NumberField K]

theorem rightConv_mem_isotypicCuspSubmodule_principalLevel {α β : ℝ} (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (Ψ : HeckeEigensystem K ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    {u : AdelicGL2 (𝓞 K) K → ℂ}
    (hu : u ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ) :
    rightConv K u f ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ := by
  have hu' : u ∈ Submodule.span ℂ {ψ | IsIsotypicCuspFormAt K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ ψ} := hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span
      (AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isBiInvariantUnder_principalLevel_of_isFundamentalDomain_slab
        K α β Φ hΦs hΦ ξ S N N hN hN Ψ f hf hfc hfU x hx)
  | zero =>
    rw [rightConv_zero_left]
    exact Submodule.zero_mem _
  | add x y hx hy hx' hy' =>
    have hxc : Continuous x := continuous_of_mem_isotypicCuspSubmodule hx
    have hyc : Continuous y := continuous_of_mem_isotypicCuspSubmodule hy
    rw [rightConv_add_left x y f hxc hyc hf hfc]
    exact Submodule.add_mem _ hx' hy'
  | smul c x hx hx' =>
    rw [rightConv_smul_left]
    exact Submodule.smul_mem _ c hx'

end Level

section Main

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalSpectrum NumberField.TateGlobal
open scoped ComplexConjugate ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem le_of_sq_le_mul {s D : ℝ} (hs : 0 ≤ s) (hD : 0 ≤ D) (h : s ^ 2 ≤ s * D) : s ≤ D := by
  rcases hs.lt_or_eq with hpos | hzero
  · rw [sq] at h
    exact le_of_mul_le_mul_left h hpos
  · rw [← hzero]
    exact hD

theorem core (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f) :
    ∃ M : ℝ, ∀ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
      (∀ i, cls i ∈ cuspClasses K (productionPinsOf K Φ
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξ N SK ∧
        b i ∈ isotypicCuspSubmodule K
              (productionPinsOf K Φ
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξ N SK (cls i)) →
      (∀ i, ∫ g in Φ, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) →
      (∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        ∀ (F : Finset ι) [DecidableEq (HeckeEigensystem K ℂ)],
          ∑ π ∈ F.image cls,
              Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
                ∫ x in Φ, ‖rightConv K (b i) f x‖ ^ 2 ∂adelicGLHaar (Fin 2) (𝓞 K) K) ≤ M := by

  set pins : CarrierPins K := productionPinsOf K Φ
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K) with hpins
  have hΦs' : Φ ⊆ slab K α β := hΦs
  have hΦ₀ : IsSlabFundamentalDomain K α β Φ := ⟨hα, hαβ, hΦs, hΦ⟩

  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hff
  obtain ⟨n, g, h, hg, hh, hfgh⟩ := exists_eq_sum_rightConv_of_isFactorizableTestFn K f hff
  have hgc : ∀ k, Continuous (g k) := fun k => (continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hg k)).1
  have hgs : ∀ k, HasCompactSupport (g k) := fun k =>
    (continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hg k)).2
  have hhc : ∀ k, Continuous (h k) := fun k => (continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hh k)).1
  have hhs : ∀ k, HasCompactSupport (h k) := fun k =>
    (continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hh k)).2

  set fl : Fin n → AdelicGL2 (𝓞 K) K → ℂ := fun k y => conj (g k y⁻¹) *
    ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) with hfl
  have hflc : ∀ k, Continuous (fl k) := fun k =>
    (Complex.continuous_conj.comp ((hgc k).comp continuous_inv)).mul (Complex.continuous_ofReal.comp (wtR_continuous σ))
  have hfls : ∀ k, HasCompactSupport (fl k) := fun k =>
    (((hgs k).comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))).comp_left (g := conj) (map_zero _)).mul_right

  have hEng := fun k => AutomorphicForm.exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
    K α β hα hαβ Φ hΦs hΦ ξ σ hσ (g k) (hg k)
  have hEnh := fun k => AutomorphicForm.exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
    K α β hα hαβ Φ hΦs hΦ ξ σ hσ (h k) (hh k)
  choose Ag hAg using hEng
  choose Ah hAh using hEnh

  set Wlo : ℝ := min (α ^ (-σ)) (β ^ (-σ)) with hWlo
  set Whi : ℝ := max (α ^ (-σ)) (β ^ (-σ)) with hWhi
  have hWlo0 : 0 < Wlo := Wlo_pos α β σ hα hαβ
  have hWhi0 : 0 ≤ Whi := hWlo0.le.trans (min_le_max)
  set C : ℝ := Real.sqrt Whi / Wlo with hC
  have hC0 : 0 ≤ C := div_nonneg (Real.sqrt_nonneg _) hWlo0.le
  refine ⟨C * ∑ k, Real.sqrt (max (Ag k) 0) * Real.sqrt (Whi * max (Ah k) 0), fun ι b cls hb hb₁ hb₀ F _ => ?_⟩

  set H : HeckeEigensystem K ℂ → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    fun π => isotypicCuspSubmodule K pins ξ N SK π with hH
  have hHcd : ∀ π, H π ≤ cuspData K Φ ξ := fun π =>
    isotypicCuspSubmodule_le_cuspData Φ _ _ ξ N SK π
  have hHcm : ∀ π, H π ≤ contMemberSubmodule K Φ ξ := fun π =>
    isotypicCuspSubmodule_le_contMemberSubmodule Φ _ _ ξ N SK π
  have hbH : ∀ i, b i ∈ H (cls i) := fun i => (hb i).2

  have cd_cont : ∀ {u}, u ∈ cuspData K Φ ξ → Continuous u := fun hu => (mem_cuspData_iff.1 hu).1
  have cd_lsxi : ∀ {u}, u ∈ cuspData K Φ ξ → IsLsXiFunction (𝓞 K) K ⊤ ξ u := fun hu => (mem_cuspData_iff.1 hu).2.1
  have cd_cusp : ∀ {u}, u ∈ cuspData K Φ ξ → IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 u :=
    fun hu => (mem_cuspData_iff.1 hu).2.2.1
  have cd_L2 : ∀ {u}, u ∈ cuspData K Φ ξ → MemLp u 2 ((μ K).restrict Φ) := fun hu => (mem_cuspData_iff.1 hu).2.2.2

  set w : ι → AdelicGL2 (𝓞 K) K → ℂ := fun i => rightConv K (b i) f with hw
  have hwH : ∀ i, w i ∈ H (cls i) := fun i =>
    rightConv_mem_isotypicCuspSubmodule_principalLevel Φ hΦs hΦ ξ SK N hN (cls i) f hfc hfs hfU (hbH i)

  set v : Fin n → ι → AdelicGL2 (𝓞 K) K → ℂ := fun k i => rightConv K (b i) (h k) with hv
  have hvc : ∀ k i, Continuous (v k i) := fun k i =>
    continuous_rightConv_of_hasCompactSupport (b i) (h k) (cd_cont (hHcd _ (hbH i))) (hhc k) (hhs k)
  have hvl : ∀ k i, IsLsXiFunction (𝓞 K) K ⊤ ξ (v k i) := fun k i =>
    { left_invariant := fun γ x => by
        simp only [hv, rightConv, mul_assoc, (cd_lsxi (hHcd _ (hbH i))).left_invariant]
      central_transform := fun z x => by
        simp only [hv, rightConv, mul_assoc, (cd_lsxi (hHcd _ (hbH i))).central_transform, integral_const_mul] }
  have hv2 : ∀ k i, MemLp (v k i) 2 ((μ K).restrict Φ) := fun k i =>
    (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ hΦs hΦ ξ σ hσ (b i) (b i)
      (cd_lsxi (hHcd _ (hbH i))) (cd_lsxi (hHcd _ (hbH i))) (cd_cont (hHcd _ (hbH i))) (cd_cont (hHcd _ (hbH i)))
      (cd_L2 (hHcd _ (hbH i))) (cd_L2 (hHcd _ (hbH i))) (h k) (hhc k) (hhs k)).1

  have hassoc : ∀ i, w i = ∑ k, rightConv K (v k i) (g k) := fun i =>
    rightConv_eq_sum_of_forall_eq_sum (b i) f (cd_cont (hHcd _ (hbH i))) g h hgc hgs hhc hhs hfgh

  set yfl : Fin n → ι → AdelicGL2 (𝓞 K) K → ℂ := fun k i => rightConv K (w i) (fl k) with hyfl
  have hadj : ∀ k i, MemLp (rightConv K (v k i) (g k)) 2 ((μ K).restrict Φ) ∧
      MemLp (yfl k i) 2 ((μ K).restrict Φ) ∧
      pairing K Φ σ (rightConv K (v k i) (g k)) (w i) = pairing K Φ σ (v k i) (yfl k i) := fun k i =>
    adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ hΦs hΦ ξ σ hσ (v k i) (w i)
      (hvl k i) (cd_lsxi (hHcd _ (hwH i))) (hvc k i) (cd_cont (hHcd _ (hwH i))) (hv2 k i) (cd_L2 (hHcd _ (hwH i)))
      (g k) (hgc k) (hgs k)

  set Fp : HeckeEigensystem K ℂ → Finset ι := fun p => F.filter (fun i => cls i = p) with hFp
  have hFp_cls : ∀ {p i}, i ∈ Fp p → cls i = p := fun hi => (Finset.mem_filter.1 hi).2
  set Pp : HeckeEigensystem K ℂ → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    fun p => Submodule.span ℂ (Set.range fun j : ↥(Fp p) => w (j : ι)) with hPp
  have hPpH : ∀ p, Pp p ≤ H p := by
    intro p
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun j => ?_)
    have h := hwH (j : ι)
    rw [hFp_cls j.2] at h
    exact h
  have hGS : ∀ p, ∃ (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ l, e l ∈ Pp p) ∧ (∀ k l, ip K Φ (e k) (e l) = if l = k then 1 else 0) ∧
      Submodule.span ℂ (Set.range e) = Pp p := by
    intro p
    haveI : FiniteDimensional ℂ ↥(Pp p) := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    exact exists_orthonormal_spanning hΦ₀ ξ (Pp p) ((hPpH p).trans (hHcm p))
  choose m e he_mem he_on he_span using hGS
  have heH : ∀ p l, e p l ∈ H p := fun p l => hPpH p (he_mem p l)

  have hcoef : ∀ i : ↥F, ∃ c : Fin (m (cls i)) → ℂ, ∑ l, c l • e (cls i) l = w i := by
    intro i
    have hi : (i : ι) ∈ Fp (cls i) := Finset.mem_filter.2 ⟨i.2, rfl⟩
    have hmem : w i ∈ Pp (cls i) := Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    rw [← he_span] at hmem
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  choose co hco using hcoef

  set X : HeckeEigensystem K ℂ → ℝ := fun p => ∑ i ∈ Fp p, ∫ x in Φ, ‖w i x‖ ^ 2 ∂(μ K) with hX
  set Xσ : HeckeEigensystem K ℂ → ℝ := fun p => ∑ i ∈ Fp p, ∫ x in Φ, ‖w i x‖ ^ 2 * wtR K σ x ∂(μ K) with hXσ
  set B : Fin n → HeckeEigensystem K ℂ → ℝ :=
    fun k p => ∑ i ∈ Fp p, ∫ x in Φ, ‖v k i x‖ ^ 2 * wtR K σ x ∂(μ K) with hB
  set y : Fin n → (p : HeckeEigensystem K ℂ) → Fin (m p) → AdelicGL2 (𝓞 K) K → ℂ :=
    fun k p l => rightConv K (e p l) (fl k) with hy
  set a : Fin n → HeckeEigensystem K ℂ → ℝ :=
    fun k p => ∑ l, ∫ x in Φ, ‖y k p l x‖ ^ 2 ∂(μ K) with ha
  have hX0 : ∀ p, 0 ≤ X p := fun p => Finset.sum_nonneg fun i _ => integral_nonneg fun x => by positivity
  have hXσ0 : ∀ p, 0 ≤ Xσ p := fun p => Finset.sum_nonneg fun i _ =>
    integral_nonneg fun x => mul_nonneg (by positivity) (wtR_pos σ x).le
  have hB0 : ∀ k p, 0 ≤ B k p := fun k p => Finset.sum_nonneg fun i _ =>
    integral_nonneg fun x => mul_nonneg (by positivity) (wtR_pos σ x).le
  have ha0 : ∀ k p, 0 ≤ a k p := fun k p => Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity

  have hy2 : ∀ k p l, MemLp (y k p l) 2 ((μ K).restrict Φ) := fun k p l =>
    (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ hΦs hΦ ξ σ hσ (e p l) (e p l)
      (cd_lsxi (hHcd _ (heH p l))) (cd_lsxi (hHcd _ (heH p l))) (cd_cont (hHcd _ (heH p l)))
      (cd_cont (hHcd _ (heH p l))) (cd_L2 (hHcd _ (heH p l))) (cd_L2 (hHcd _ (heH p l))) (g k) (hgc k) (hgs k)).2.1

  have hA : ∀ p, Wlo * X p ≤ Xσ p := by
    intro p
    rw [hX, hXσ, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_integral_normSq_le α β σ hα Φ hΦs' (w i) (cd_L2 (hHcd _ (hwH i)))

  have hBstep : ∀ p, Xσ p ≤ ∑ k, Real.sqrt (B k p) *
      Real.sqrt (∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K)) := by
    intro p

    have h1 : ((Xσ p : ℝ) : ℂ) = ∑ i ∈ Fp p, ∑ k, pairing K Φ σ (v k i) (yfl k i) := by
      rw [hXσ, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pairing_self_eq]

      have hleft : pairing K Φ σ (w i) (w i) = pairing K Φ σ (fun x => ∑ k, rightConv K (v k i) (g k) x) (w i) := by
        rw [pairing_def, pairing_def]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only []
        rw [← Finset.sum_apply, ← hassoc i]
      rw [hleft, pairing_sum_left α β σ hα Φ hΦs' (fun k => rightConv K (v k i) (g k)) (fun k => (hadj k i).1) (w i)
        (cd_L2 (hHcd _ (hwH i)))]
      exact Finset.sum_congr rfl fun k _ => (hadj k i).2.2
    have h2 : Xσ p = RCLike.re (∑ i ∈ Fp p, ∑ k, pairing K Φ σ (v k i) (yfl k i)) := by
      rw [← h1, RCLike.re_to_complex, Complex.ofReal_re]
    rw [h2, Finset.sum_comm]
    refine (RCLike.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => norm_pairing_le α β σ hα Φ hΦs' (v k i) (yfl k i) (hv2 k i)
      (hadj k i).2.1).trans ?_
    exact Real.sum_sqrt_mul_sqrt_le (Fp p) (fun i => integral_nonneg fun x => mul_nonneg (by positivity) (wtR_pos σ x).le)
      (fun i => integral_nonneg fun x => mul_nonneg (by positivity) (wtR_pos σ x).le)

  have hCstep : ∀ k p, ∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K) ≤ Whi * (X p * a k p) := by
    intro k p

    have h1 : ∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K) ≤
        Whi * ∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 ∂(μ K) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => integral_normSq_mul_wtR_le α β σ hα Φ hΦs' (yfl k i) (hadj k i).2.1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hWhi0)

    rw [hX, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hiF : i ∈ F := (Finset.mem_filter.1 hi).1
    have hcls : cls i = p := hFp_cls hi

    obtain ⟨c, hc, hceq⟩ : ∃ c : Fin (m p) → ℂ, (∑ l, c l • e p l = w i) ∧
        (∑ l, ‖c l‖ ^ 2 : ℝ) = ∫ x in Φ, ‖w i x‖ ^ 2 ∂(μ K) := by
      subst hcls
      refine ⟨co ⟨i, hiF⟩, hco ⟨i, hiF⟩, ?_⟩

      have hP := integral_norm_sq_sum_smul (ρ := (μ K).restrict Φ) (e (cls i)) (fun l => cd_L2 (hHcd _ (heH _ l)))
        (fun l l' hll' => by
          have h := he_on (cls i) l l'
          rw [if_neg (Ne.symm hll')] at h
          exact h) (co ⟨i, hiF⟩)
      rw [hco ⟨i, hiF⟩] at hP
      rw [hP]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_norm_sq_eq_one_of_ip_eq_one Φ (e (cls i) l) (by have h := he_on (cls i) l l; rwa [if_pos rfl] at h),
        mul_one]

    have hexp : yfl k i = ∑ l, c l • y k p l := by
      show rightConv K (w i) (fl k) = ∑ l, c l • rightConv K (e p l) (fl k)
      rw [← hc]
      exact rightConv_sum_smul (e p) (fun l => cd_cont (hHcd _ (heH p l))) c (fl k) (hflc k) (hfls k)
    rw [hexp, ← hceq]
    exact integral_norm_sq_sum_smul_le (ρ := (μ K).restrict Φ) (y k p) (hy2 k p) c

  have hD : ∀ p, Real.sqrt (X p) ≤ C * ∑ k, Real.sqrt (a k p) * Real.sqrt (B k p) := by
    intro p
    set s : ℝ := Real.sqrt (Xσ p) with hs
    set D : ℝ := Real.sqrt (Whi / Wlo) * ∑ k, Real.sqrt (a k p) * Real.sqrt (B k p) with hDdef
    have hD0 : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun k _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

    have hsD : s ^ 2 ≤ s * D := by
      rw [hs, Real.sq_sqrt (hXσ0 p)]
      refine (hBstep p).trans ?_
      have hterm : ∀ k, Real.sqrt (B k p) * Real.sqrt (∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K)) ≤
          Real.sqrt (Xσ p) * (Real.sqrt (Whi / Wlo) * (Real.sqrt (a k p) * Real.sqrt (B k p))) := by
        intro k
        have hY : ∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K) ≤ (Whi / Wlo) * a k p * Xσ p := by
          refine (hCstep k p).trans ?_
          have hXle : X p ≤ Wlo⁻¹ * Xσ p := by
            rw [le_inv_mul_iff₀ hWlo0]
            exact hA p
          calc Whi * (X p * a k p) ≤ Whi * (Wlo⁻¹ * Xσ p * a k p) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXle (ha0 k p)) hWhi0
            _ = Whi / Wlo * a k p * Xσ p := by rw [div_eq_mul_inv]; ring
        calc Real.sqrt (B k p) * Real.sqrt (∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K))
            ≤ Real.sqrt (B k p) * Real.sqrt ((Whi / Wlo) * a k p * Xσ p) :=
              mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hY) (Real.sqrt_nonneg _)
          _ = Real.sqrt (Xσ p) * (Real.sqrt (Whi / Wlo) * (Real.sqrt (a k p) * Real.sqrt (B k p))) := by
              rw [Real.sqrt_mul (mul_nonneg (div_nonneg hWhi0 hWlo0.le) (ha0 k p)),
                Real.sqrt_mul (div_nonneg hWhi0 hWlo0.le)]
              ring
      calc ∑ k, Real.sqrt (B k p) * Real.sqrt (∑ i ∈ Fp p, ∫ x in Φ, ‖yfl k i x‖ ^ 2 * wtR K σ x ∂(μ K))
          ≤ ∑ k, Real.sqrt (Xσ p) * (Real.sqrt (Whi / Wlo) * (Real.sqrt (a k p) * Real.sqrt (B k p))) :=
            Finset.sum_le_sum fun k _ => hterm k
        _ = s * D := by rw [hs, hDdef, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsle : s ≤ D := le_of_sq_le_mul (Real.sqrt_nonneg _) hD0 hsD

    have hX1 : Real.sqrt (X p) ≤ Real.sqrt (Wlo⁻¹) * s := by
      rw [hs, ← Real.sqrt_mul (inv_nonneg.2 hWlo0.le)]
      refine Real.sqrt_le_sqrt ?_
      rw [le_inv_mul_iff₀ hWlo0]
      exact hA p
    refine hX1.trans ((mul_le_mul_of_nonneg_left hsle (Real.sqrt_nonneg _)).trans (le_of_eq ?_))
    rw [hDdef, ← mul_assoc, hC]
    congr 1
    rw [← Real.sqrt_mul (inv_nonneg.2 hWlo0.le),
      show Wlo⁻¹ * (Whi / Wlo) = Whi / Wlo ^ 2 by field_simp,
      Real.sqrt_div' _ (sq_nonneg Wlo), Real.sqrt_sq hWlo0.le]

  have hE : ∑ p ∈ F.image cls, Real.sqrt (X p) ≤
      C * ∑ k, Real.sqrt (∑ p ∈ F.image cls, a k p) * Real.sqrt (∑ p ∈ F.image cls, B k p) := by
    calc ∑ p ∈ F.image cls, Real.sqrt (X p)
        ≤ ∑ p ∈ F.image cls, C * ∑ k, Real.sqrt (a k p) * Real.sqrt (B k p) := Finset.sum_le_sum fun p _ => hD p
      _ = C * ∑ k, ∑ p ∈ F.image cls, Real.sqrt (a k p) * Real.sqrt (B k p) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ C * ∑ k, Real.sqrt (∑ p ∈ F.image cls, a k p) * Real.sqrt (∑ p ∈ F.image cls, B k p) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ =>
            Real.sum_sqrt_mul_sqrt_le (F.image cls) (fun p => ha0 k p) (fun p => hB0 k p)) hC0

  have hF1 : ∀ k, ∑ p ∈ F.image cls, B k p ≤ Whi * max (Ah k) 0 := by
    intro k
    have hfib : ∑ p ∈ F.image cls, B k p = ∑ i ∈ F, ∫ x in Φ, ‖v k i x‖ ^ 2 * wtR K σ x ∂(μ K) :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem cls hi) _
    rw [hfib]
    have h1 : ∑ i ∈ F, ∫ x in Φ, ‖v k i x‖ ^ 2 * wtR K σ x ∂(μ K) ≤ Whi * ∑ i ∈ F, ∫ x in Φ, ‖v k i x‖ ^ 2 ∂(μ K) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => integral_normSq_mul_wtR_le α β σ hα Φ hΦs' (v k i) (hv2 k i)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hWhi0)

    set nF : ℕ := F.card with hnF
    let φF : Fin nF ≃ ↥F := F.equivFin.symm
    let eb : Fin nF → AdelicGL2 (𝓞 K) K → ℂ := fun j => b (φF j)
    have heb : ∀ j, eb j ∈ cuspData K Φ ξ := fun j => hHcd _ (hbH _)
    have heb_orth : ∀ j j', j ≠ j' → ∫ x in Φ, eb j x * conj (eb j' x) ∂(μ K) = 0 := by
      intro j j' hjj
      have hne : ((φF j : ↥F) : ι) ≠ ((φF j' : ↥F) : ι) := fun h' => hjj (φF.injective (Subtype.ext h'))
      exact hb₀ _ _ hne
    have heb_norm : ∀ j, ∫ x in Φ, ‖eb j x‖ ^ 2 ∂(μ K) ≤ 1 := fun j => by
      rw [integral_norm_sq_eq_one_of_ip_eq_one Φ (eb j) (hb₁ _)]
    have hmain := (hAh k nF eb (fun j => cd_cont (heb j)) (fun j => cd_lsxi (heb j)) (fun j => cd_cusp (heb j))
      (fun j => cd_L2 (heb j)) heb_orth heb_norm).1
    have hreidx : (∑ i ∈ F, ∫ x in Φ, ‖v k i x‖ ^ 2 ∂(μ K)) = ∑ j, ∫ x in Φ, ‖rightConv K (eb j) (h k) x‖ ^ 2 ∂(μ K) := by
      rw [← Finset.sum_coe_sort F]
      exact (Fintype.sum_equiv φF _ _ fun j => rfl).symm
    rw [hreidx]
    exact hmain.trans (le_max_left _ _)

  have hF2 : ∀ k, ∑ p ∈ F.image cls, a k p ≤ max (Ag k) 0 := by
    intro k

    set J := Σ p : ↥(F.image cls), Fin (m (p : HeckeEigensystem K ℂ)) with hJ
    set nJ : ℕ := Fintype.card J with hnJ
    let ψ : Fin nJ ≃ J := (Fintype.equivFin J).symm
    let E : Fin nJ → AdelicGL2 (𝓞 K) K → ℂ := fun j => e ((ψ j).1 : HeckeEigensystem K ℂ) (ψ j).2
    have hE : ∀ j, E j ∈ cuspData K Φ ξ := fun j => hHcd _ (heH _ _)
    have hEclass : ∀ q : ↥(F.image cls), (q : HeckeEigensystem K ℂ) ∈ cuspClasses K pins ξ N SK := by
      intro q
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 q.2
      rw [← hi]
      exact (hb i).1
    have hE_orth : ∀ j j', j ≠ j' → ∫ x in Φ, E j x * conj (E j' x) ∂(μ K) = 0 := by
      intro j j' hjj
      have hne : ψ j ≠ ψ j' := fun h' => hjj (ψ.injective h')

      by_cases hq : (ψ j).1 = (ψ j').1
      ·
        have key : ∀ x x' : J, x ≠ x' → x.1 = x'.1 →
            ip K Φ (e (x.1 : HeckeEigensystem K ℂ) x.2) (e (x'.1 : HeckeEigensystem K ℂ) x'.2) = 0 := by
          rintro ⟨q, l⟩ ⟨q', l'⟩ hxx hqq
          simp only at hqq
          subst hqq
          have hll : l ≠ l' := fun h' => hxx (by rw [h'])
          have h := he_on (q : HeckeEigensystem K ℂ) l l'
          rw [if_neg (Ne.symm hll)] at h
          exact h
        exact key (ψ j) (ψ j') hne hq
      ·
        have hne' : ((ψ j).1 : HeckeEigensystem K ℂ) ≠ ((ψ j').1 : HeckeEigensystem K ℂ) :=
          fun h' => hq (Subtype.ext h')
        exact AutomorphicForm.setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
          K α β hα hαβ Φ hΦs hΦ ξ N SK hN _ _ (hEclass _) (hEclass _) hne' (E j) (E j') (heH _ _) (heH _ _)
    have hE_norm : ∀ j, ∫ x in Φ, ‖E j x‖ ^ 2 ∂(μ K) ≤ 1 := fun j => by
      rw [integral_norm_sq_eq_one_of_ip_eq_one Φ (E j)
        (by have h := he_on ((ψ j).1 : HeckeEigensystem K ℂ) (ψ j).2 (ψ j).2; rwa [if_pos rfl] at h)]
    have hmain := (hAg k nJ E (fun j => cd_cont (hE j)) (fun j => cd_lsxi (hE j)) (fun j => cd_cusp (hE j))
      (fun j => cd_L2 (hE j)) hE_orth hE_norm).2

    have hreidx : ∑ p ∈ F.image cls, a k p = ∑ j, ∫ x in Φ, ‖rightConv K (E j) (fl k) x‖ ^ 2 ∂(μ K) := by
      rw [← Finset.sum_coe_sort (F.image cls)]
      have h1 : ∑ q : ↥(F.image cls), a k q =
          ∑ x : J, ∫ x' in Φ, ‖y k (x.1 : HeckeEigensystem K ℂ) x.2 x'‖ ^ 2 ∂(μ K) :=
        (Fintype.sum_sigma (fun x : J => ∫ x' in Φ, ‖y k (x.1 : HeckeEigensystem K ℂ) x.2 x'‖ ^ 2 ∂(μ K))).symm
      rw [h1]
      refine Fintype.sum_equiv ψ.symm _ _ (fun x => ?_)
      show (∫ x' in Φ, ‖rightConv K (e (x.1 : HeckeEigensystem K ℂ) x.2) (fl k) x'‖ ^ 2 ∂(μ K)) =
        ∫ x' in Φ, ‖rightConv K (e ((ψ (ψ.symm x)).1 : HeckeEigensystem K ℂ) (ψ (ψ.symm x)).2) (fl k) x'‖ ^ 2 ∂(μ K)
      rw [Equiv.apply_symm_apply]
    rw [hreidx]
    exact hmain.trans (le_max_left _ _)

  have hgoal : ∑ π ∈ F.image cls, Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
      ∫ x in Φ, ‖rightConv K (b i) f x‖ ^ 2 ∂(μ K)) = ∑ p ∈ F.image cls, Real.sqrt (X p) := rfl
  rw [hgoal]
  refine hE.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hC0)
  exact mul_le_mul (Real.sqrt_le_sqrt (hF2 k)) (Real.sqrt_le_sqrt (hF1 k)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Main

end S14HS0A
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal.S14HS0A"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ComplexConjugate

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn K f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f) :
    ∃ M : ℝ, ∀ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
      (∀ i, cls i ∈ cuspClasses K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK ∧
        b i ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK) →
      (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b i g)
          ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) →
      (∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b j g)
          ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
        ∀ (F : Finset ι) [DecidableEq (HeckeEigensystem K ℂ)],
          ∑ π ∈ F.image cls,
              Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
                (eLpNorm (convOp K f (b i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal ^ 2) ≤ M := by
  obtain ⟨-, -, -, hΦs, hΦ⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  obtain ⟨σ, hσ⟩ := S14HS0A.exists_sigma_of_continuous_of_trivial ξK hξc hξt
  obtain ⟨M, hM⟩ := S14HS0A.core K α β hα hαβ (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ ξK σ hσ
    SK N hN f hff hfU
  refine ⟨M, fun ι b cls hb hb₁ hb₀ F _ => ?_⟩
  have hmain := hM ι b cls (fun i => ⟨(hb i).1, (hb i).2.1⟩) hb₁ hb₀ F
  refine le_of_eq_of_le (Finset.sum_congr rfl fun π _ => congrArg Real.sqrt (Finset.sum_congr rfl fun i _ => ?_)) hmain

  have hmem := S14HS0A.rightConv_mem_isotypicCuspSubmodule_principalLevel
    (AutomorphicForm.canonicalTruncationDomain K α β) hΦs hΦ ξK SK N hN (cls i) f hf hfc hfU (hb i).2.1
  have hL2 := (S14HS0A.mem_cuspData_iff.1 (S14HS0A.isotypicCuspSubmodule_le_cuspData _ _ _ ξK N SK (cls i) hmem)).2.2.2
  rw [AutomorphicForm.convOp_apply]
  exact S14HS0A.eLpNorm_toReal_sq hL2

end
end S_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal (solution)
