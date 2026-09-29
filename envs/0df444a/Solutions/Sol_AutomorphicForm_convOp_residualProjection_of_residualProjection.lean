-- Prove2me | solution 1 for AutomorphicForm.convOp_residualProjection_of_residualProjection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/32160432-d373-55d9-be5b-5c152f5db38b

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

import Theorems.Thm_AutomorphicForm_aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_convOp_residualProjection_of_residualProjection
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped Pointwise ENNReal
open AutomorphicForm

theorem T6B.iSup_ofReal_min_natCast (r : ℝ) (hr : 0 ≤ r) :
    (⨆ n : ℕ, ENNReal.ofReal (min r n)) = ENNReal.ofReal r := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  refine le_iSup_of_le ⌈r⌉₊ ?_
  rw [min_eq_left (Nat.le_ceil r)]

theorem T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (h : AdelicGL2 (𝓞 K) K) (hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) = 1) :
    ∫⁻ x in Φ, ENNReal.ofReal (‖u (x * h)‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ x in Φ, ENNReal.ofReal (‖u x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := isFiniteMeasure_restrict.2 hΦfin.ne
  have huh : AEStronglyMeasurable (fun x => u (x * h)) (adelicGLHaar (Fin 2) (𝓞 K) K) :=
    hu.comp_quasiMeasurePreserving (measurePreserving_mul_right (adelicGLHaar (Fin 2) (𝓞 K) K) h).quasiMeasurePreserving
  have hmeas_min : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∀ n : ℕ, AEStronglyMeasurable (fun x => min (‖v x‖ ^ 2) (n : ℝ))
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) := fun v hv n =>
    ((continuous_id.pow 2).min continuous_const).comp_aestronglyMeasurable hv.restrict.norm
  have hnn : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ) (n : ℕ) (x : AdelicGL2 (𝓞 K) K), 0 ≤ min (‖v x‖ ^ 2) (n : ℝ) :=
    fun v n x => le_min (sq_nonneg _) (Nat.cast_nonneg n)
  have hint : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∀ n : ℕ, Integrable (fun x => min (‖v x‖ ^ 2) (n : ℝ)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    fun v hv n => Integrable.of_bound (hmeas_min v hv n) n (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn v n x)]; exact min_le_right _ _)

  have key : ∀ n : ℕ, ∫⁻ x in Φ, ENNReal.ofReal (min (‖u (x * h)‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ x in Φ, ENNReal.ofReal (min (‖u x‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro n
    have hB := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
      K α β Φ hΦs hΦ h hh (fun x => ((min (‖u x‖ ^ 2) (n : ℝ) : ℝ) : ℂ)) (fun γ g => by rw [hΓ γ g])
    rw [integral_complex_ofReal, integral_complex_ofReal] at hB
    have hR : ∫ x in Φ, min (‖u (x * h)‖ ^ 2) (n : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ x in Φ, min (‖u x‖ ^ 2) (n : ℝ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by exact_mod_cast hB
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _ huh n) (Filter.Eventually.of_forall (hnn _ n)),
      ← ofReal_integral_eq_lintegral_ofReal (hint _ hu n) (Filter.Eventually.of_forall (hnn _ n)), hR]

  have hsup : ∀ (v : AdelicGL2 (𝓞 K) K → ℂ), AEStronglyMeasurable v (adelicGLHaar (Fin 2) (𝓞 K) K) →
      ∫⁻ x in Φ, ENNReal.ofReal (‖v x‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ⨆ n : ℕ, ∫⁻ x in Φ, ENNReal.ofReal (min (‖v x‖ ^ 2) (n : ℝ)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro v hv
    rw [← lintegral_iSup' (fun n => (hmeas_min v hv n).aemeasurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => fun a b hab =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hab)))]
    exact lintegral_congr fun x => (T6B.iSup_ofReal_min_natCast _ (sq_nonneg _)).symm
  rw [hsup _ huh, hsup _ hu]
  exact iSup_congr key

namespace Ws31
namespace Adjoint

theorem setIntegral_mul_conj_comp_mul_eq (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (v w : AdelicGL2 (𝓞 K) K → ℂ)
    (hvΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), v (globalPoints (𝓞 K) K γ * g) = v g)
    (hwΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), w (globalPoints (𝓞 K) K γ * g) = w g)
    (hvZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      v (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * v g)
    (hwZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      w (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * w g)
    (x : AdelicGL2 (𝓞 K) K) :
    ∫ g in Φ, v g * conj (w (g * x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ g in Φ, v (g * x⁻¹) * conj (w g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => v (g * x⁻¹) * conj (w g) with hF
  have hFΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), F (globalPoints (𝓞 K) K γ * g) = F g := by
    intro γ g; simp only [hF, mul_assoc, hvΓ, hwΓ]

  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hr : 0 < 1 / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) := one_div_pos.2 hd
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.2 hr)
  have hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * x)) = 1 := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar K, pow_two,
      NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hr.le, one_div_mul_cancel hd.ne']
  have hξ2 : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      conj (((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = 1 := by
    intro z
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hξu, one_pow, Complex.ofReal_one]

  have h1 : ∀ g, F (g * (centralScalar (𝓞 K) K z * x)) = v g * conj (w (g * x)) := by
    intro g
    have e1 : g * (centralScalar (𝓞 K) K z * x) * x⁻¹ = centralScalar (𝓞 K) K z * g := by
      rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, mul_centralScalar_comm]
    have e2 : g * (centralScalar (𝓞 K) K z * x) = centralScalar (𝓞 K) K z * (g * x) := by
      rw [← mul_assoc, mul_centralScalar_comm, mul_assoc]
    simp only [hF]
    rw [e1, e2, hvZ, hwZ, map_mul]
    calc ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * v g * (conj (((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * conj (w (g * x)))
        = (conj (((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) * (v g * conj (w (g * x))) := by ring
      _ = v g * conj (w (g * x)) := by rw [hξ2, one_mul]
  have key := AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
    K α β Φ hΦs hΦ _ hh F hFΓ
  simp only [h1] at key
  rw [key]

end Ws31.Adjoint

namespace Ws31
namespace Adjoint

theorem setLIntegral_norm_sq_comp_mul_eq_of_central (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦfin : adelicGLHaar (Fin 2) (𝓞 K) K Φ < ⊤)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : AEStronglyMeasurable u (adelicGLHaar (Fin 2) (𝓞 K) K))
    (hΓ : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), u (globalPoints (𝓞 K) K γ * g) = u g)
    (hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      u (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g)
    (x : AdelicGL2 (𝓞 K) K) :
    ∫⁻ g in Φ, ENNReal.ofReal (‖u (g * x)‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫⁻ g in Φ, ENNReal.ofReal (‖u g‖ ^ 2) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have hd : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hr : 0 < 1 / NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) := one_div_pos.2 hd
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.2 hr)
  have hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * x)) = 1 := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar K, pow_two,
      NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hr.le, one_div_mul_cancel hd.ne']
  have hpt : ∀ g : AdelicGL2 (𝓞 K) K, ‖u (g * (centralScalar (𝓞 K) K z * x))‖ = ‖u (g * x)‖ := by
    intro g
    rw [← mul_assoc, mul_centralScalar_comm, mul_assoc, hZ, norm_mul, hξu z, one_mul]
  rw [← T6B.setLIntegral_ofReal_norm_sq_comp_mul_eq K α β Φ hΦs hΦ hΦfin u hu hΓ _ hh]
  exact lintegral_congr fun g => by rw [hpt]

end Ws31.Adjoint

namespace Ws31
namespace PairForm

theorem norm_integral_mul_conj_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (φ ψ : X → ℂ) (hφ : MemLp φ 2 ν) (hψ : MemLp ψ 2 ν) :
    ‖∫ x, φ x * conj (ψ x) ∂ν‖ ≤ (eLpNorm φ 2 ν).toReal * (eLpNorm ψ 2 ν).toReal := by
  have h1 : ∫ x, φ x * conj (ψ x) ∂ν = inner ℂ (hψ.toLp ψ) (hφ.toLp φ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hφ.coeFn_toLp, hψ.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, mul_comm]
  rw [h1]
  calc ‖inner ℂ (hψ.toLp ψ) (hφ.toLp φ)‖ ≤ ‖hψ.toLp ψ‖ * ‖hφ.toLp φ‖ := norm_inner_le_norm _ _
    _ = (eLpNorm φ 2 ν).toReal * (eLpNorm ψ 2 ν).toReal := by rw [Lp.norm_toLp, Lp.norm_toLp, mul_comm]

theorem comp_mul_mem_residualSpan (K : Type) [Field K] [NumberField K]
    (Z : Subgroup (AdeleRing (𝓞 K) K)ˣ) (ξ : Z →* ℂˣ) (r : AdelicGL2 (𝓞 K) K → ℂ)
    (hr : r ∈ AutomorphicForm.residualSpan (𝓞 K) K Z ξ) (y : AdelicGL2 (𝓞 K) K) :
    (fun g => r (g * y)) ∈ AutomorphicForm.residualSpan (𝓞 K) K Z ξ := by
  let T : (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * y)
  have hT : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, T u = fun g => u (g * y) := fun u => rfl
  have hle : Submodule.map T (AutomorphicForm.residualSpan (𝓞 K) K Z ξ) ≤
      AutomorphicForm.residualSpan (𝓞 K) K Z ξ := by
    unfold AutomorphicForm.residualSpan
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro φ ⟨χ, hχ, rfl⟩
    have e : T (AutomorphicForm.chiDet (𝓞 K) K χ) =
        ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • AutomorphicForm.chiDet (𝓞 K) K χ := by
      funext g
      show AutomorphicForm.chiDet (𝓞 K) K χ (g * y) =
        ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * AutomorphicForm.chiDet (𝓞 K) K χ g
      simp only [AutomorphicForm.chiDet, map_mul, Units.val_mul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, hχ, rfl⟩)
  rw [← hT]
  exact hle (Submodule.mem_map_of_mem hr)

theorem isAutomorphicFnAt_comp_mul (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (y : AdelicGL2 (𝓞 K) K) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (fun g => u (g * y)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  have hfin : μ Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne
  have huL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
  have huΓ := huL.1.left_invariant
  have huZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      u (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g :=
    fun z g => huL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have hum : AEStronglyMeasurable u μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK u hu
  have hu2 : MemLp u 2 (μ.restrict Φ) := huL.2
  have hIu : Integrable (fun g => ‖u g‖ ^ 2) (μ.restrict Φ) :=
    (memLp_two_iff_integrable_sq_norm hum.restrict).1 hu2
  have hmass : ∫⁻ g in Φ, ENNReal.ofReal (‖u (g * y)‖ ^ 2) ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖u g‖ ^ 2) ∂μ :=
    Ws31.Adjoint.setLIntegral_norm_sq_comp_mul_eq_of_central K α β Φ hslab hFD hfin ξK hξu u hum huΓ huZ y
  have huym : AEStronglyMeasurable (fun g => u (g * y)) μ :=
    hum.comp_quasiMeasurePreserving (measurePreserving_mul_right μ y).quasiMeasurePreserving
  have hIuy : Integrable (fun g => ‖u (g * y)‖ ^ 2) (μ.restrict Φ) := by
    refine ⟨(huym.restrict.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
    show ∫⁻ g in Φ, ‖‖u (g * y)‖ ^ 2‖ₑ ∂μ < ⊤
    have h1 : ∫⁻ g in Φ, ‖‖u (g * y)‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖u (g * y)‖ ^ 2) ∂μ :=
      lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
    have h2 : ∫⁻ g in Φ, ‖‖u g‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖u g‖ ^ 2) ∂μ :=
      lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
    rw [h1, hmass, ← h2]
    exact hIu.2
  have huy2 : MemLp (fun g => u (g * y)) 2 (μ.restrict Φ) :=
    (memLp_two_iff_integrable_sq_norm huym.restrict).2 hIuy
  refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, huy2⟩
  · rw [mul_assoc]
    exact huΓ γ (g * y)
  · rw [mul_assoc]
    exact huL.1.central_transform z (g * y)

theorem fubini_pairing (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (ha : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK a) (hb : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK b)
    (h : AdelicGL2 (𝓞 K) K → ℂ) (hh : Continuous h) (hhc : HasCompactSupport h) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        (∫ x, a (g * x) * h x ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x, h x * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        a (g * x) * conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  have hfin : μ Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne
  have haL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 ha
  have hbL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hb
  have ham : AEStronglyMeasurable a μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK a ha
  have hbm : AEStronglyMeasurable b μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK b hb
  have haΓ := haL.1.left_invariant
  have haZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      a (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * a g :=
    fun z g => haL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
  have ha2 : MemLp a 2 (μ.restrict Φ) := haL.2
  have hb2 : MemLp b 2 (μ.restrict Φ) := hbL.2

  have hIa : Integrable (fun g => ‖a g‖ ^ 2) (μ.restrict Φ) := (memLp_two_iff_integrable_sq_norm ham.restrict).1 ha2
  have hIb : Integrable (fun g => ‖b g‖ ^ 2) (μ.restrict Φ) := (memLp_two_iff_integrable_sq_norm hbm.restrict).1 hb2
  have hmass : ∀ x : AdelicGL2 (𝓞 K) K,
      ∫⁻ g in Φ, ENNReal.ofReal (‖a (g * x)‖ ^ 2) ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖a g‖ ^ 2) ∂μ :=
    fun x => Ws31.Adjoint.setLIntegral_norm_sq_comp_mul_eq_of_central K α β Φ hslab hFD hfin ξK hξu a ham haΓ haZ x
  have haxm : ∀ x : AdelicGL2 (𝓞 K) K, AEStronglyMeasurable (fun g => a (g * x)) μ := fun x =>
    ham.comp_quasiMeasurePreserving (measurePreserving_mul_right μ x).quasiMeasurePreserving
  have hIax : ∀ x : AdelicGL2 (𝓞 K) K, Integrable (fun g => ‖a (g * x)‖ ^ 2) (μ.restrict Φ) := by
    intro x
    refine ⟨((haxm x).restrict.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
    show ∫⁻ g in Φ, ‖‖a (g * x)‖ ^ 2‖ₑ ∂μ < ⊤
    have h1 : ∫⁻ g in Φ, ‖‖a (g * x)‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖a (g * x)‖ ^ 2) ∂μ :=
      lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
    have h2 : ∫⁻ g in Φ, ‖‖a g‖ ^ 2‖ₑ ∂μ = ∫⁻ g in Φ, ENNReal.ofReal (‖a g‖ ^ 2) ∂μ :=
      lintegral_congr fun g => Real.enorm_eq_ofReal (sq_nonneg _)
    rw [h1, hmass x, ← h2]
    exact hIa.2
  have hax : ∀ x : AdelicGL2 (𝓞 K) K, MemLp (fun g => a (g * x)) 2 (μ.restrict Φ) := fun x =>
    (memLp_two_iff_integrable_sq_norm (haxm x).restrict).2 (hIax x)
  have hmassR : ∀ x : AdelicGL2 (𝓞 K) K, ∫ g in Φ, ‖a (g * x)‖ ^ 2 ∂μ = ∫ g in Φ, ‖a g‖ ^ 2 ∂μ := by
    intro x
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => sq_nonneg _) (hIax x).1,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => sq_nonneg _) hIa.1, hmass x]

  set G : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K → ℂ := fun p => a (p.1 * p.2) * h p.2 * conj (b p.1) with hG
  have hq : Measure.QuasiMeasurePreserving (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => p.1 * p.2)
      ((μ.restrict Φ).prod μ) μ :=
    Measure.quasiMeasurePreserving_snd.comp (measurePreserving_prod_mul (μ.restrict Φ) μ).quasiMeasurePreserving
  have hGm : AEStronglyMeasurable G ((μ.restrict Φ).prod μ) :=
    ((ham.comp_quasiMeasurePreserving hq).mul (hh.comp continuous_snd).aestronglyMeasurable).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hbm.restrict.comp_fst)
  have hconjb : MemLp (fun g => conj (b g)) 2 (μ.restrict Φ) :=
    hb2.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hbm.restrict)
      (Filter.Eventually.of_forall fun g => (RCLike.norm_conj _).symm)
  have hGi : Integrable G ((μ.restrict Φ).prod μ) := by
    refine (integrable_prod_iff' hGm).2 ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · have h1 : Integrable ((fun g => a (g * x)) * fun g => conj (b g)) (μ.restrict Φ) :=
        (hax x).integrable_mul hconjb
      have := h1.mul_const (h x)
      refine this.congr (Filter.Eventually.of_forall fun g => ?_)
      show a (g * x) * conj (b g) * h x = a (g * x) * h x * conj (b g)
      ring
    ·
      have hbound : ∀ x, ∫ g, ‖G (g, x)‖ ∂(μ.restrict Φ) ≤
          ‖h x‖ * ((∫ g in Φ, ‖a g‖ ^ 2 ∂μ) + ∫ g in Φ, ‖b g‖ ^ 2 ∂μ) := by
        intro x
        have hpt : ∀ g, ‖G (g, x)‖ ≤ ‖h x‖ * (‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2) := by
          intro g
          simp only [hG, norm_mul, RCLike.norm_conj]
          have : ‖a (g * x)‖ * ‖b g‖ ≤ ‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2 := by
            nlinarith [sq_nonneg (‖a (g * x)‖ - ‖b g‖), norm_nonneg (a (g * x)), norm_nonneg (b g)]
          calc ‖a (g * x)‖ * ‖h x‖ * ‖b g‖ = ‖h x‖ * (‖a (g * x)‖ * ‖b g‖) := by ring
            _ ≤ ‖h x‖ * (‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2) := by gcongr
        calc ∫ g, ‖G (g, x)‖ ∂(μ.restrict Φ) ≤ ∫ g, ‖h x‖ * (‖a (g * x)‖ ^ 2 + ‖b g‖ ^ 2) ∂(μ.restrict Φ) :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => norm_nonneg _)
                (((hIax x).add hIb).const_mul _) (Filter.Eventually.of_forall hpt)
          _ = ‖h x‖ * ((∫ g in Φ, ‖a g‖ ^ 2 ∂μ) + ∫ g in Φ, ‖b g‖ ^ 2 ∂μ) := by
              rw [integral_const_mul, integral_add (hIax x) hIb, hmassR x]
      have hmeasI : AEStronglyMeasurable (fun x => ∫ g, ‖G (g, x)‖ ∂(μ.restrict Φ)) μ := by
        have := hGm.prod_swap.norm
        exact this.integral_prod_right'
      refine Integrable.mono' ((hh.norm.integrable_of_hasCompactSupport hhc.norm).mul_const
        ((∫ g in Φ, ‖a g‖ ^ 2 ∂μ) + ∫ g in Φ, ‖b g‖ ^ 2 ∂μ)) hmeasI (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun g => norm_nonneg _)]
      exact hbound x

  have hL : ∀ g, (∫ x, a (g * x) * h x ∂μ) * conj (b g) = ∫ x, G (g, x) ∂μ := by
    intro g
    rw [← integral_mul_const]
  have hR : ∀ x, (∫ g in Φ, G (g, x) ∂μ) = h x * ∫ g in Φ, a (g * x) * conj (b g) ∂μ := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show a (g * x) * h x * conj (b g) = h x * (a (g * x) * conj (b g))
    ring
  simp_rw [hL]
  rw [integral_integral_swap (f := fun g x => G (g, x)) hGi]
  simp_rw [hR]

end Ws31.PairForm

namespace Ws31
namespace ResCommute

theorem component_mem_span_translates {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    (ψ : ι → (G →* ℂ)) (hψ : Function.Injective ψ) (c : ι → ℂ) (i : ι) :
    (fun g => c i * ψ i g) ∈
      Submodule.span ℂ (Set.range fun y : G => fun g => ∑ j, c j * ψ j (g * y)) := by
  classical
  let L : (ι → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun a g => ∑ j, a j * (c j * ψ j g)
      map_add' := by
        intro a b; funext g
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext g
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hLapp : ∀ (a : ι → ℂ) (g : G), L a g = ∑ j, a j * (c j * ψ j g) := fun a g => rfl
  let v : G → (ι → ℂ) := fun y j => ψ j y
  have hLv : ∀ y, L (v y) = fun g => ∑ j, c j * ψ j (g * y) := by
    intro y; funext g
    rw [hLapp]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; ring

  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ a : ι → ℂ, φ a = ∑ j, a j * φ (Pi.single j 1) := by
      intro a
      conv_lhs => rw [pi_eq_sum_univ a]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      congr 1
      congr 1
      funext k
      simp only [Pi.single_apply, eq_comm]
    have hzero : ∀ y, ∑ j, φ (Pi.single j 1) * ψ j y = 0 := by
      intro y
      have hy : v y ∈ LinearMap.ker φ := hker (Submodule.subset_span ⟨y, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at hy
      simpa only [mul_comm] using hy
    have hli := (linearIndependent_monoidHom G ℂ).comp ψ hψ
    rw [Fintype.linearIndependent_iff] at hli
    have hall := hli (fun j => φ (Pi.single j 1)) (by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      exact hzero y)
    apply hφ0
    refine LinearMap.ext fun a => ?_
    rw [hφ a, LinearMap.zero_apply]
    simp only [hall, mul_zero, Finset.sum_const_zero]
  have hmem : (Pi.single i (1:ℂ) : ι → ℂ) ∈ Submodule.span ℂ (Set.range v) := by
    rw [htop]; exact Submodule.mem_top
  have h1 : Submodule.map L (Submodule.span ℂ (Set.range v)) =
      Submodule.span ℂ (Set.range fun y : G => fun g => ∑ j, c j * ψ j (g * y)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    have hcomp : (⇑L ∘ v) = fun y : G => fun g => ∑ j, c j * ψ j (g * y) := funext hLv
    rw [hcomp]
  have h2 : L (Pi.single i 1) ∈ Submodule.span ℂ (Set.range fun y : G => fun g => ∑ j, c j * ψ j (g * y)) := by
    rw [← h1]; exact Submodule.mem_map_of_mem hmem
  have h3 : L (Pi.single i 1) = fun g => c i * ψ i g := by
    funext g
    rw [hLapp, Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, one_mul]
    · intro j _ hj
      simp only [Pi.single_apply, hj, if_false, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [← h3]; exact h2

end Ws31.ResCommute

namespace Ws31
namespace ResCommute

theorem memLp_two_conj (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) :
    MemLp (fun g => conj (u g)) 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  have hfin : μ Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne
  have huL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
  have hu2 : MemLp u 2 (μ.restrict Φ) := huL.2
  have hum : AEStronglyMeasurable u μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK u hu
  exact hu2.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hum.restrict)
    (Filter.Eventually.of_forall fun g => (RCLike.norm_conj _).symm)

theorem isAutomorphicFnAt_sub (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (u w : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u) (hw : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK w) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (u - w) := by
  have huL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
  have hwL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hw
  refine (lsXiMemberAt_iff _ _ _ _ _ _ _).2 ⟨⟨fun γ g => ?_, fun z g => ?_⟩, huL.2.sub hwL.2⟩
  · simp only [Pi.sub_apply, huL.1.left_invariant γ g, hwL.1.left_invariant γ g]
  · simp only [Pi.sub_apply, huL.1.central_transform z g, hwL.1.central_transform z g, mul_sub]

theorem convOp_mem_residualSpan (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (q : AdelicGL2 (𝓞 K) K → ℂ)
    (hqS : q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK)
    (hqA : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    convOp K f q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  have hfin : μ Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne
  set P := productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K) with hP
  classical
  have hqS' := hqS
  unfold AutomorphicForm.residualSpan at hqS'
  obtain ⟨t, htS, hqt⟩ := Submodule.mem_span_finite_of_mem_span hqS'
  obtain ⟨c, -, hsum⟩ := Submodule.mem_span_finset.1 hqt
  have hgen : ∀ j : ↥t, ∃ χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      SquaresToXi (𝓞 K) K P.Z ξK χ ∧ (j.1 : AdelicGL2 (𝓞 K) K → ℂ) = chiDet (𝓞 K) K χ :=
    fun j => htS j.2
  choose χ hχsq hχeq using hgen
  let ψ : ↥t → (AdelicGL2 (𝓞 K) K →* ℂ) := fun j =>
    (Units.coeHom ℂ).comp ((χ j).comp Matrix.GeneralLinearGroup.det)
  have hψeq : ∀ (j : ↥t) (g : AdelicGL2 (𝓞 K) K), (ψ j g : ℂ) = j.1 g := by
    intro j g
    have e := congrFun (hχeq j) g
    rw [e]
    rfl
  have hψinj : Function.Injective ψ := by
    intro j k hjk
    apply Subtype.ext
    funext g
    rw [← hψeq j g, ← hψeq k g, hjk]

  have hq : ∀ g, q g = ∑ j : ↥t, c j.1 * ψ j g := by
    intro g
    rw [← hsum, Finset.sum_apply, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hψeq]

  have hψ1 : ∀ (j : ↥t) (g : AdelicGL2 (𝓞 K) K), ‖(ψ j g : ℂ)‖ = 1 := by
    intro j g
    have h2 := hχsq j ⟨Matrix.GeneralLinearGroup.det g, Subgroup.mem_top _⟩
    have h3 : ‖((χ j (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]
      exact hξu _
    have h0 := norm_nonneg ((χ j (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)
    exact (pow_eq_one_iff_of_nonneg h0 two_ne_zero).1 h3

  have hqm : AEStronglyMeasurable q μ :=
    AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ hslab hFD ξK q hqA
  have hqym : ∀ y : AdelicGL2 (𝓞 K) K, AEStronglyMeasurable (fun g => q (g * y)) μ := fun y =>
    hqm.comp_quasiMeasurePreserving (measurePreserving_mul_right μ y).quasiMeasurePreserving
  have hT : ∀ u ∈ Submodule.span ℂ (Set.range fun y : AdelicGL2 (𝓞 K) K => fun g => ∑ j, c j.1 * ψ j (g * y)),
      AEStronglyMeasurable u μ := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => AEStronglyMeasurable u μ) ?_ ?_ ?_ ?_ hu
    · rintro u ⟨y, rfl⟩
      have e : (fun g => ∑ j, c j.1 * ψ j (g * y)) = fun g => q (g * y) :=
        funext fun g => (hq (g * y)).symm
      dsimp only
      rw [e]
      exact hqym y
    · exact aestronglyMeasurable_const
    · intro u w _ _ hu hw
      exact hu.add hw
    · intro a u _ hu
      exact hu.const_smul a
  have hψm : ∀ j : ↥t, c j.1 ≠ 0 → AEStronglyMeasurable (fun g => (ψ j g : ℂ)) μ := by
    intro j hj
    have hm := hT _ (Ws31.ResCommute.component_mem_span_translates ψ hψinj (fun j => c j.1) j)
    have e : (fun g => (ψ j g : ℂ)) = fun g => (c j.1)⁻¹ * (c j.1 * ψ j g) := by
      funext g
      rw [← mul_assoc, inv_mul_cancel₀ hj, one_mul]
    rw [e]
    exact hm.const_mul _

  have hfi : Integrable f μ := _hf.integrable_of_hasCompactSupport _hfc
  have hconv : ∀ g, convOp K f q g = ∑ j : ↥t, (c j.1 * ∫ x, (ψ j x : ℂ) * f x ∂μ) * ψ j g := by
    intro g
    have hIj : ∀ j : ↥t, Integrable (fun x => c j.1 * ψ j (g * x) * f x) μ := by
      intro j
      by_cases hj : c j.1 = 0
      · simp only [hj, zero_mul]
        exact integrable_zero _ _ _
      · have hb : Integrable (fun x => (ψ j x : ℂ) * f x) μ :=
          hfi.bdd_mul (hψm j hj) (Filter.Eventually.of_forall fun x => (hψ1 j x).le)
        have := hb.const_mul (c j.1 * ψ j g)
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        show c j.1 * ψ j g * (ψ j x * f x) = c j.1 * ψ j (g * x) * f x
        rw [map_mul]
        ring
    calc convOp K f q g = ∫ x, q (g * x) * f x ∂μ := by simp only [convOp_apply, rightConv_apply, hμ]
      _ = ∫ x, ∑ j : ↥t, c j.1 * ψ j (g * x) * f x ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [hq, Finset.sum_mul]
      _ = ∑ j : ↥t, ∫ x, c j.1 * ψ j (g * x) * f x ∂μ := integral_finsetSum _ (fun j _ => hIj j)
      _ = ∑ j : ↥t, (c j.1 * ∫ x, (ψ j x : ℂ) * f x ∂μ) * ψ j g := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have e : (fun x => c j.1 * ψ j (g * x) * f x) = fun x => (c j.1 * ψ j g) * (ψ j x * f x) := by
            funext x
            rw [map_mul]
            ring
          rw [e, integral_const_mul]
          ring
  have hfun : convOp K f q = ∑ j : ↥t, (c j.1 * ∫ x, (ψ j x : ℂ) * f x ∂μ) • (j.1 : AdelicGL2 (𝓞 K) K → ℂ) := by
    funext g
    rw [hconv g, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hψeq]
  rw [hfun]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  unfold AutomorphicForm.residualSpan
  exact Submodule.subset_span (htS j.2)

end Ws31.ResCommute

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (θ p : AdelicGL2 (𝓞 K) K → ℂ)
    (_hθ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK θ)
    (_hp : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK p)
    (_hpc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (p - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
    (_hpo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (θ g - p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) :
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK (convOp K f p) ∧
    (∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (convOp K f p - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) ∧
    (∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          (convOp K f θ g - convOp K f p g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  obtain ⟨-, -, -, hslab, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ
  have hfin : μ Φ < ⊤ := by
    have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain K α β hα hαβ Φ hFD
    rwa [Set.inter_eq_left.mpr hslab] at h
  haveI : IsFiniteMeasure (μ.restrict Φ) := isFiniteMeasure_restrict.2 hfin.ne
  set P := productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K) with hP
  have hθL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hθ
  have hpL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 _hp

  have hRp : IsAutomorphicFnAt K P ξK (convOp K f p) :=
    AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξu p _hp f _hf _hfc
  have hRθ : IsAutomorphicFnAt K P ξK (convOp K f θ) :=
    AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
      K α β hα hαβ ξK hξc hξu θ _hθ f _hf _hfc
  refine ⟨hRp, ?_, ?_⟩
  ·
    intro ε hε
    obtain ⟨c0, hc0, hRF⟩ :=
      AutomorphicForm.exists_forall_eLpNorm_convOp_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
        K α β hα hαβ ξK hξc hξu f _hf _hfc
    have hc1 : 0 < c0 + 1 := by linarith
    obtain ⟨q₀, hq₀S, hq₀A, hq₀ε⟩ := _hpc (ε / (c0 + 1)) (div_pos hε hc1)
    refine ⟨convOp K f q₀, Ws31.ResCommute.convOp_mem_residualSpan K α β hα hαβ ξK hξu hξc q₀ hq₀S hq₀A f _hf _hfc,
      AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
        K α β hα hαβ ξK hξc hξu q₀ hq₀A f _hf _hfc, ?_⟩

    have hd : IsAutomorphicFnAt K P ξK (p - q₀) := Ws31.ResCommute.isAutomorphicFnAt_sub K α β hα hαβ ξK hξu p q₀ _hp hq₀A
    have hz : IsAutomorphicFnAt K P ξK (fun _ => (0 : ℂ)) := AutomorphicForm.isAutomorphicFnAt_zero K P ξK
    have hae : p =ᵐ[μ.restrict Φ] (p - q₀) + q₀ + (fun _ => (0 : ℂ)) :=
      Filter.Eventually.of_forall fun g => by simp
    have hlin := AutomorphicForm.convOp_eq_add_add_of_ae_eq_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt_of_continuous
      K α β hα hαβ ξK hξc p (p - q₀) q₀ (fun _ => (0 : ℂ)) _hp hd hq₀A hz hae f _hf _hfc
    have hzero : ∀ x, convOp K f (fun _ => (0 : ℂ)) x = 0 := by
      intro x; simp only [convOp_apply, rightConv_apply, zero_mul, integral_zero]
    have hdiff : convOp K f p - convOp K f q₀ = convOp K f (p - q₀) := by
      funext x
      rw [Pi.sub_apply, hlin x, hzero x, add_zero, add_sub_cancel_right]
    rw [hdiff]
    calc eLpNorm (convOp K f (p - q₀)) 2 (μ.restrict Φ)
        ≤ ENNReal.ofReal c0 * eLpNorm (p - q₀) 2 (μ.restrict Φ) := hRF _ hd
      _ ≤ ENNReal.ofReal c0 * ENNReal.ofReal (ε / (c0 + 1)) := by gcongr
      _ = ENNReal.ofReal (c0 * (ε / (c0 + 1))) := (ENNReal.ofReal_mul hc0).symm
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε]
          rw [mul_div_assoc', div_lt_iff₀ hc1]
          nlinarith
  ·
    intro h hh hhS
    have hhL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hh
    have hhΓ := hhL.1.left_invariant
    have hhZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        h (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * h g :=
      fun z g => hhL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
    have hconjh : MemLp (fun g => conj (h g)) 2 (μ.restrict Φ) :=
      Ws31.ResCommute.memLp_two_conj K α β hα hαβ ξK hξu h hh

    have hX : ∀ u : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K P ξK u →
        ∫ g in Φ, convOp K f u g * conj (h g) ∂μ = ∫ x, f x * ∫ g in Φ, u g * conj (h (g * x⁻¹)) ∂μ ∂μ := by
      intro u hu
      have huL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hu
      have huZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          u (centralScalar (𝓞 K) K z * g) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g :=
        fun z g => huL.1.central_transform ⟨z, Subgroup.mem_top z⟩ g
      have hF := Ws31.PairForm.fubini_pairing K α β hα hαβ ξK hξu u h hu hh f _hf _hfc
      have e1 : ∫ g in Φ, convOp K f u g * conj (h g) ∂μ =
          ∫ g in Φ, (∫ x, u (g * x) * f x ∂μ) * conj (h g) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [convOp_apply, rightConv_apply, hμ]
      rw [e1, hF]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      congr 1
      have T := Ws31.Adjoint.setIntegral_mul_conj_comp_mul_eq K α β Φ hslab hFD ξK hξu u h
        huL.1.left_invariant hhΓ huZ hhZ x⁻¹
      rw [inv_inv] at T
      exact T.symm

    have hinner : ∀ x : AdelicGL2 (𝓞 K) K,
        ∫ g in Φ, θ g * conj (h (g * x⁻¹)) ∂μ = ∫ g in Φ, p g * conj (h (g * x⁻¹)) ∂μ := by
      intro x
      have hhx : IsAutomorphicFnAt K P ξK (fun g => h (g * x⁻¹)) :=
        Ws31.PairForm.isAutomorphicFnAt_comp_mul K α β hα hαβ ξK hξu h hh x⁻¹
      have hhxS := Ws31.PairForm.comp_mul_mem_residualSpan K _ ξK h hhS x⁻¹
      have h0 : ∫ g in Φ, (θ g - p g) * conj (h (g * x⁻¹)) ∂μ = 0 := _hpo _ hhx hhxS
      have hconjhx : MemLp (fun g => conj (h (g * x⁻¹))) 2 (μ.restrict Φ) :=
        Ws31.ResCommute.memLp_two_conj K α β hα hαβ ξK hξu _ hhx
      have hIθ : Integrable (fun g => θ g * conj (h (g * x⁻¹))) (μ.restrict Φ) := hθL.2.integrable_mul hconjhx
      have hIp : Integrable (fun g => p g * conj (h (g * x⁻¹))) (μ.restrict Φ) := hpL.2.integrable_mul hconjhx
      rw [← sub_eq_zero, ← integral_sub hIθ hIp]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)).trans h0
      ring
    have hRθL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hRθ
    have hRpL := (lsXiMemberAt_iff _ _ _ _ _ _ _).1 hRp
    have hIθ : Integrable (fun g => convOp K f θ g * conj (h g)) (μ.restrict Φ) := hRθL.2.integrable_mul hconjh
    have hIp : Integrable (fun g => convOp K f p g * conj (h g)) (μ.restrict Φ) := hRpL.2.integrable_mul hconjh
    calc ∫ g in Φ, (convOp K f θ g - convOp K f p g) * conj (h g) ∂μ
        = (∫ g in Φ, convOp K f θ g * conj (h g) ∂μ) - ∫ g in Φ, convOp K f p g * conj (h g) ∂μ := by
          rw [← integral_sub hIθ hIp]
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          dsimp only
          ring
      _ = 0 := by
          rw [hX θ _hθ, hX p _hp]
          simp_rw [hinner]
          exact sub_self _

end S_AutomorphicForm_convOp_residualProjection_of_residualProjection
end P2MW
export P2MW.S_AutomorphicForm_convOp_residualProjection_of_residualProjection (solution)
