-- Prove2me | solution 1 for AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/75a2d3ff-be3e-5a5d-b86e-20efff0d0451

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicVolume
open scoped NNReal

namespace Ws20

namespace CentralHalf

variable {F : Type} [Field F] [NumberField F]

theorem det_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g) = z * z * Matrix.GeneralLinearGroup.det g := by
  rw [map_mul]
  congr 1
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, centralScalar_apply_eq,
    centralScalar_apply_eq, centralScalar_apply_ne (F := F) z (show (0 : Fin 2) ≠ 1 by decide), Units.val_mul]
  ring

theorem rpow_le_max_pow_ceil {a : ℝ} (ha : 0 < a) (y : ℝ) :
    a ^ y ≤ max a a⁻¹ ^ ⌈|y|⌉₊ := by
  have hm1 : 1 ≤ max a a⁻¹ := by
    rcases le_or_gt 1 a with h | h
    · exact h.trans (le_max_left _ _)
    · exact ((one_le_inv₀ ha).mpr h.le).trans (le_max_right _ _)
  have h1 : a ^ y ≤ max a a⁻¹ ^ |y| := by
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      exact Real.rpow_le_rpow ha.le (le_max_left _ _) hy
    · rw [abs_of_neg hy]
      have : a ^ y = a⁻¹ ^ (-y) := by rw [Real.inv_rpow ha.le, Real.rpow_neg ha.le, inv_inv]
      rw [this]
      exact Real.rpow_le_rpow (inv_nonneg.mpr ha.le) (le_max_right _ _) (neg_nonneg.mpr hy.le)
  calc a ^ y ≤ max a a⁻¹ ^ |y| := h1
    _ ≤ max a a⁻¹ ^ ((⌈|y|⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (Nat.le_ceil _)
    _ = max a a⁻¹ ^ ⌈|y|⌉₊ := Real.rpow_natCast _ _

end CentralHalf

theorem norm_le_mul_max_pow_of_central (F : Type) [Field F] [NumberField F]
    (G : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (t : ℝ)
    (hχ : ∀ z : (AdeleRing (𝓞 F) F)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = ideleNorm F z ^ t)
    (hG : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      G (centralScalar (𝓞 F) F z * g) = ((χ z : ℂˣ) : ℂ) * G g)
    (Mb : ℝ)
    (hMb : ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (1 : ℝ) 1 → ‖G g‖ ≤ Mb) :
    ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M := by
  obtain ⟨s, -, hs, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
  refine ⟨max Mb 0, ⌈|t / 2|⌉₊, fun g => ?_⟩
  set a : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det g) with ha_def
  have ha : 0 < a := ideleNorm_pos _

  set ρ : ℝ := a ^ (-(1 / 2 : ℝ)) with hρ_def
  have hρ : 0 < ρ := Real.rpow_pos_of_pos ha _
  set r : ℝ≥0ˣ := Units.mk0 (⟨ρ, hρ.le⟩ : ℝ≥0)
    (NNReal.coe_pos.mp (show (0 : ℝ) < ((⟨ρ, hρ.le⟩ : ℝ≥0) : ℝ) from hρ)).ne' with hr_def
  have hr : ((r : ℝ≥0) : ℝ) = ρ := rfl
  set z : (AdeleRing (𝓞 F) F)ˣ := s r with hz_def
  have hz : ideleNorm F z = ρ := by rw [hz_def, hs, hr]
  have hρρ : ρ * ρ * a = 1 := by
    rw [hρ_def, ← Real.rpow_add ha, ← Real.rpow_add_one ha.ne']
    norm_num

  have hdet : ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * g)) = 1 := by
    rw [CentralHalf.det_centralScalar_mul, ideleNorm_mul, ideleNorm_mul, hz, ← ha_def, hρρ]
  have hb : ‖G (centralScalar (𝓞 F) F z * g)‖ ≤ Mb := hMb _ ⟨hdet.symm.le, hdet.le⟩

  have hρt : 0 < ρ ^ t := Real.rpow_pos_of_pos hρ t
  have hGg : ‖G g‖ ≤ Mb * a ^ (t / 2) := by
    have e : ‖G (centralScalar (𝓞 F) F z * g)‖ = ρ ^ t * ‖G g‖ := by rw [hG, norm_mul, hχ, hz]
    have h1 : ‖G g‖ ≤ Mb / ρ ^ t := by rw [le_div_iff₀ hρt, mul_comm, ← e]; exact hb
    have h2 : (ρ ^ t)⁻¹ = a ^ (t / 2) := by
      rw [← Real.rpow_neg hρ.le, hρ_def, ← Real.rpow_mul ha.le]
      congr 1; ring
    rwa [div_eq_mul_inv, h2] at h1

  have hmax : a ^ (t / 2) ≤ max a a⁻¹ ^ ⌈|t / 2|⌉₊ := CentralHalf.rpow_le_max_pow_ceil ha _
  have hpow_nonneg : 0 ≤ max a a⁻¹ ^ ⌈|t / 2|⌉₊ := pow_nonneg (ha.le.trans (le_max_left _ _)) _
  calc ‖G g‖ ≤ Mb * a ^ (t / 2) := hGg
    _ ≤ max Mb 0 * a ^ (t / 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ha.le _)
    _ ≤ max Mb 0 * max a a⁻¹ ^ ⌈|t / 2|⌉₊ := mul_le_mul_of_nonneg_left hmax (le_max_right _ _)

end Ws20

namespace Ws20
namespace MG0

variable (F : Type) [Field F] [NumberField F]

theorem rightConv_const_mul (c : ℂ) (φ f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F (fun x => c * φ x) f g = c * rightConv F φ f g := by
  simp only [rightConv]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z * z := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, centralScalar_apply_eq,
    centralScalar_apply_eq, centralScalar_apply_ne (F := F) z (show (0 : Fin 2) ≠ 1 by decide), Units.val_mul]
  ring

theorem continuous_centralScalar :
    Continuous (fun z : (AdeleRing (𝓞 F) F)ˣ => centralScalar (𝓞 F) F z) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_pi fun _ : Fin 2 => Units.continuous_val).matrix_diagonal).congr
      fun z => (centralScalar_val (F := F) z).symm
  · refine ((continuous_pi fun _ : Fin 2 => Units.continuous_coe_inv).matrix_diagonal).congr fun z => ?_
    show Matrix.diagonal (fun _ : Fin 2 => ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      = (((centralScalar (𝓞 F) F z)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    rw [← map_inv, centralScalar_val]

theorem centralScalar_unitsMap_algebraMap (u : Fˣ) :
    centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u)
      = globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralScalar, globalPoints, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map,
      Matrix.scalar_apply, Matrix.diagonal]

end Ws20.MG0

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖rightConv F φ f g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M := by
  classical
  have hφ' := hφ
  obtain ⟨⟨⟨hleft, hcentral⟩, -⟩, -⟩ := hφ'
  have hZ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, x ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z := fun x => by
    rw [productionPinsOf_Z]; exact Subgroup.mem_top x

  have hGleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g := by
    intro γ g
    rw [← rightConv_comp_mul_left]
    have h1 : (fun x => φ (globalPoints (𝓞 F) F γ * x)) = φ := funext fun x => hleft γ x
    rw [h1]
  let ι : (AdeleRing (𝓞 F) F)ˣ →* ↥((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z) :=
    { toFun := fun z => ⟨z, hZ z⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := ξ.comp ι
  have hGcent : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (centralScalar (𝓞 F) F z * g) = ((χ z : ℂˣ) : ℂ) * rightConv F φ f g := by
    intro z g
    rw [← rightConv_comp_mul_left]
    have h1 : (fun x => φ (centralScalar (𝓞 F) F z * x)) = fun x => ((χ z : ℂˣ) : ℂ) * φ x :=
      funext fun x => hcentral ⟨z, hZ z⟩ x
    rw [h1, Ws20.MG0.rightConv_const_mul]

  by_cases h0 : ∀ g : AdelicGL2 (𝓞 F) F, rightConv F φ f g = 0
  · exact ⟨0, 0, fun g => by simp [h0 g]⟩
  push Not at h0
  obtain ⟨g₁, hg₁⟩ := h0

  have hGcont : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  have hχval : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      ((χ z : ℂˣ) : ℂ) = rightConv F φ f (centralScalar (𝓞 F) F z * g₁) * (rightConv F φ f g₁)⁻¹ := by
    intro z
    rw [hGcent z g₁, mul_inv_cancel_right₀ hg₁]
  have hc1 : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((χ z : ℂˣ) : ℂ) := by
    have h2 : (fun z : (AdeleRing (𝓞 F) F)ˣ => ((χ z : ℂˣ) : ℂ)) =
        fun z => rightConv F φ f (centralScalar (𝓞 F) F z * g₁) * (rightConv F φ f g₁)⁻¹ := funext hχval
    rw [h2]
    exact (hGcont.comp ((Ws20.MG0.continuous_centralScalar F).mul continuous_const)).mul continuous_const
  have hχc : Continuous χ := by
    refine Units.continuous_iff.2 ⟨hc1, ?_⟩
    have h3 : (fun z : (AdeleRing (𝓞 F) F)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((χ z : ℂˣ) : ℂ)⁻¹ :=
      funext fun z => Units.val_inv_eq_inv_val _
    rw [h3]
    exact hc1.inv₀ fun z => (χ z).ne_zero

  have hχ1 : IsIdeleClassChar (𝓞 F) F χ := by
    intro v
    have h := hGcent (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) v) g₁
    rw [Ws20.MG0.centralScalar_unitsMap_algebraMap, hGleft] at h
    have h2 : ((χ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) v) : ℂˣ) : ℂ) = 1 := by
      have h4 := h.symm
      rw [mul_comm] at h4

      exact (mul_right_inj' hg₁).mp (h4.trans (mul_one _).symm)
    exact Units.val_eq_one.mp h2
  obtain ⟨t, ht⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F χ hχ1 hχc
  obtain ⟨Mb, hMb⟩ := AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
    F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf 1 1 one_pos
  exact Ws20.norm_le_mul_max_pow_of_central F (rightConv F φ f) χ t ht hGcent Mb hMb

end S_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow (solution)
