-- Prove2me | solution 1 for AutomorphicForm.exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/bb2a2ec2-eb9b-5fc2-88b5-d9e30a1e191d

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_AutomorphicForm_exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedSpace_apply
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

noncomputable section

namespace C5K5b

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

def avg (G : AdelicGL2 (𝓞 F) F → ℂ) (B : AdeleRing (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun h => ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)

theorem avg_spec (G : AdelicGL2 (𝓞 F) F → ℂ) (B : AdeleRing (𝓞 F) F → ℂ) :
    ∀ h : AdelicGL2 (𝓞 F) F, avg F G B h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)) := fun _ => rfl

theorem det_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of])

theorem det_diagOne (b : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne b : AdelicGL2 (𝓞 F) F) = b :=
  Units.ext (by simp [diagOne, Matrix.GeneralLinearGroup.val_det_apply])

def wt (M : ℕ) (b : (AdeleRing (𝓞 F) F)ˣ) : ℝ := max (ideleNorm F b) (ideleNorm F b)⁻¹ ^ M

theorem wt_nonneg (M : ℕ) (b : (AdeleRing (𝓞 F) F)ˣ) : 0 ≤ wt F M b :=
  pow_nonneg ((ideleNorm_pos b).le.trans (le_max_left _ _)) _

theorem norm_avg_le {G : AdelicGL2 (𝓞 F) F → ℂ} {C₀ : ℝ} {M₀ : ℕ}
    (hMG : ∀ g : AdelicGL2 (𝓞 F) F, ‖G g‖ ≤ C₀ * wt F M₀ (Matrix.GeneralLinearGroup.det g))
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F) (h : AdelicGL2 (𝓞 F) F) :
    ‖avg F G B h‖ ≤ (∫ x, ‖B x‖ ∂(adelicAddHaar (𝓞 F) F)) * (C₀ * wt F M₀ (Matrix.GeneralLinearGroup.det h)) := by
  have hBi : Integrable B (adelicAddHaar (𝓞 F) F) :=
    NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F (adelicAddHaar (𝓞 F) F) hB
  unfold avg
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hBi.norm.mul_const _)
    (ae_of_all _ fun x => ?_)
  show ‖B x * G (h * unipotentGL2 x)‖ ≤ ‖B x‖ * (C₀ * wt F M₀ (Matrix.GeneralLinearGroup.det h))
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := hMG (h * unipotentGL2 x)
  rwa [map_mul, det_unipotentGL2, mul_one] at this

theorem norm_whittakerCoefficient_avg_diagOne_le
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {G : AdelicGL2 (𝓞 F) F → ℂ} {C₀ : ℝ} {M₀ : ℕ}
    (hMG : ∀ g : AdelicGL2 (𝓞 F) F, ‖G g‖ ≤ C₀ * wt F M₀ (Matrix.GeneralLinearGroup.det g))
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (α : F) (b : (AdeleRing (𝓞 F) F)ˣ) :
    ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (avg F G B) α (diagOne b)‖
      ≤ (∫ x, ‖B x‖ ∂(adelicAddHaar (𝓞 F) F)) * C₀ * wt F M₀ b := by
  haveI : IsProbabilityMeasure (productionPinsOf F D U gen (adelicBox F)).ν :=
    isProbabilityMeasure_productionPinsOf_ν F D U gen (adelicBox F)
      (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne
  set K : ℝ := (∫ x, ‖B x‖ ∂(adelicAddHaar (𝓞 F) F)) * C₀ * wt F M₀ b with hKdef
  have hbound : ∀ x : AdeleRing (𝓞 F) F,
      ‖avg F G B (unipotentGL2 x * diagOne b) * ψ (-((algebraMap F (AdeleRing (𝓞 F) F)) α * x))‖ ≤ K := by
    intro x
    rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]
    have h := norm_avg_le F hMG hB (unipotentGL2 x * diagOne b)
    rwa [map_mul, det_unipotentGL2, one_mul, det_diagOne, ← mul_assoc] at h
  unfold whittakerCoefficient
  refine (norm_integral_le_of_norm_le_const (ae_of_all _ hbound)).trans (le_of_eq ?_)
  rw [probReal_univ, mul_one]

def lam (a : F) (e : mixedEmbedding.mixedSpace F) (b : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) * e)

def coef (a : F) (e : mixedEmbedding.mixedSpace F) (b : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((2 * Real.pi * lam F a e b : ℝ) : ℂ) * Complex.I

theorem norm_coef (a : F) (e : mixedEmbedding.mixedSpace F) (b : (AdeleRing (𝓞 F) F)ˣ) :
    ‖coef F a e b‖ = |2 * Real.pi * lam F a e b| := by
  rw [coef, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]

theorem norm_prod_coef (a : F) (L : List (mixedEmbedding.mixedSpace F)) (b : (AdeleRing (𝓞 F) F)ˣ) :
    ‖(L.map fun e => coef F a e b).prod‖ = (L.map fun e => |2 * Real.pi * lam F a e b|).prod := by
  induction L with
  | nil => simp
  | cons e L ih => rw [List.map_cons, List.prod_cons, norm_mul, norm_coef, ih, List.map_cons, List.prod_cons]

def Good (M : ℕ) (V : (AdeleRing (𝓞 F) F)ˣ → ℝ) : Prop := ∃ C : ℝ, ∀ b, V b ≤ C * wt F M b

def GoodL (M : ℕ) (a : F) (V : (AdeleRing (𝓞 F) F)ˣ → ℝ) : Prop :=
  ∀ L : List (mixedEmbedding.mixedSpace F),
    Good F M (fun b => (L.map fun e => |2 * Real.pi * lam F a e b|).prod * V b)

variable {F}

theorem prod_abs_nonneg (a : F) (L : List (mixedEmbedding.mixedSpace F)) (b : (AdeleRing (𝓞 F) F)ˣ) :
    0 ≤ (L.map fun e => |2 * Real.pi * lam F a e b|).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _

theorem Good.congr {M : ℕ} {V V' : (AdeleRing (𝓞 F) F)ˣ → ℝ} (h : ∀ b, V b = V' b) (hV : Good F M V) :
    Good F M V' := by
  obtain ⟨C, hC⟩ := hV; exact ⟨C, fun b => h b ▸ hC b⟩

theorem Good.mono {M : ℕ} {V V' : (AdeleRing (𝓞 F) F)ˣ → ℝ} (h : ∀ b, V b ≤ V' b) (hV : Good F M V') :
    Good F M V := by
  obtain ⟨C, hC⟩ := hV; exact ⟨C, fun b => (h b).trans (hC b)⟩

theorem Good.add {M : ℕ} {V V' : (AdeleRing (𝓞 F) F)ˣ → ℝ} (hV : Good F M V) (hV' : Good F M V') :
    Good F M (fun b => V b + V' b) := by
  obtain ⟨C, hC⟩ := hV; obtain ⟨C', hC'⟩ := hV'
  exact ⟨C + C', fun b => by rw [add_mul]; exact add_le_add (hC b) (hC' b)⟩

theorem Good.const_mul {M : ℕ} {V : (AdeleRing (𝓞 F) F)ˣ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hV : Good F M V) :
    Good F M (fun b => c * V b) := by
  obtain ⟨C, hC⟩ := hV
  exact ⟨c * C, fun b => by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hC b) hc⟩

theorem Good.zero (M : ℕ) : Good F M (fun _ => 0) := ⟨0, fun b => by rw [zero_mul]⟩

theorem GoodL.congr {M : ℕ} {a : F} {V V' : (AdeleRing (𝓞 F) F)ˣ → ℝ} (h : ∀ b, V b = V' b)
    (hV : GoodL F M a V) : GoodL F M a V' := fun L =>
  (hV L).congr fun b => by rw [h b]

theorem GoodL.good {M : ℕ} {a : F} {V : (AdeleRing (𝓞 F) F)ˣ → ℝ} (hV : GoodL F M a V) : Good F M V :=
  (hV []).congr fun b => by simp

theorem GoodL.add {M : ℕ} {a : F} {V V' : (AdeleRing (𝓞 F) F)ˣ → ℝ} (hV : GoodL F M a V) (hV' : GoodL F M a V') :
    GoodL F M a (fun b => V b + V' b) := fun L =>
  ((hV L).add (hV' L)).congr fun b => by ring

theorem GoodL.const_mul {M : ℕ} {a : F} {V : (AdeleRing (𝓞 F) F)ˣ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hV : GoodL F M a V) : GoodL F M a (fun b => c * V b) := fun L =>
  ((hV L).const_mul hc).congr fun b => by ring

theorem GoodL.mono {M : ℕ} {a : F} {V V' : (AdeleRing (𝓞 F) F)ˣ → ℝ} (h : ∀ b, V b ≤ V' b)
    (hV : GoodL F M a V') : GoodL F M a V := fun L =>
  (hV L).mono fun b => mul_le_mul_of_nonneg_left (h b) (prod_abs_nonneg a L b)

theorem GoodL.zero (M : ℕ) (a : F) : GoodL F M a (fun _ => 0) := fun L =>
  (Good.zero M).congr fun b => by rw [mul_zero]

theorem GoodL.absLam_mul {M : ℕ} {a : F} {V : (AdeleRing (𝓞 F) F)ˣ → ℝ} (hV : GoodL F M a V)
    (e : mixedEmbedding.mixedSpace F) : GoodL F M a (fun b => |2 * Real.pi * lam F a e b| * V b) := fun L =>
  (hV (e :: L)).congr fun b => by rw [List.map_cons, List.prod_cons]; ring

theorem GoodL.pow_mul {M : ℕ} {a : F} {μ : (AdeleRing (𝓞 F) F)ˣ → ℝ}
    (hμ : ∀ V : (AdeleRing (𝓞 F) F)ˣ → ℝ, GoodL F M a V → GoodL F M a (fun b => μ b * V b))
    {V : (AdeleRing (𝓞 F) F)ˣ → ℝ} (hV : GoodL F M a V) (n : ℕ) :
    GoodL F M a (fun b => μ b ^ n * V b) := by
  induction n with
  | zero => exact hV.congr fun b => by rw [pow_zero, one_mul]
  | succ n ih => exact (hμ _ ih).congr fun b => by rw [pow_succ]; ring

theorem GoodL.prod_pow_mul {M : ℕ} {a : F} {κ : Type} {μ : κ → (AdeleRing (𝓞 F) F)ˣ → ℝ}
    (hμ : ∀ (w : κ) (V : (AdeleRing (𝓞 F) F)ˣ → ℝ), GoodL F M a V → GoodL F M a (fun b => μ w b * V b))
    (s : Finset κ) (m : κ → ℕ) {V : (AdeleRing (𝓞 F) F)ˣ → ℝ} (hV : GoodL F M a V) :
    GoodL F M a (fun b => (∏ w ∈ s, μ w b ^ m w) * V b) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hV.congr fun b => by rw [Finset.prod_empty, one_mul]
  | @insert w s hw ih =>
    exact (GoodL.pow_mul (hμ w) ih (m w)).congr fun b => by rw [Finset.prod_insert hw]; ring

variable (F)

section Class

variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    {G : AdelicGL2 (𝓞 F) F → ℂ} (hGc : Continuous G)
    (hMGex : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), G (globalPoints (𝓞 F) F γ * g) = G g)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {a : F} (ha : a ≠ 0)
    (hψa : ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))

include hGc hMGex hinv hψ ha hψa in

theorem iter (L : List (mixedEmbedding.mixedSpace F)) {B : AdeleRing (𝓞 F) F → ℂ}
    (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F) :
    ∃ BL : AdeleRing (𝓞 F) F → ℂ, BL ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (avg F G BL) 1 (diagOne b)
          = (L.map fun e => coef F a e b).prod *
            whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (avg F G B) 1 (diagOne b) := by
  induction L with
  | nil => exact ⟨B, hB, fun b => by rw [List.map_nil, List.prod_nil, one_mul]⟩
  | cons e L ih =>
    obtain ⟨BL, hBL, hW⟩ := ih
    obtain ⟨B', hB', h1⟩ :=
      AutomorphicForm.exists_mem_schwartzBruhat_whittakerCoefficient_unipotentAverage_diagOne_eq_trace_mul
        F D U gen G hGc hMGex hinv BL hBL (avg F G BL) (avg_spec F G BL) ψ hψ a ha hψa e
    refine ⟨B', hB', fun b => ?_⟩
    rw [h1 (avg F G B') (avg_spec F G B') b, hW b, List.map_cons, List.prod_cons, coef, lam]
    ring

include hGc hMGex hinv hψ ha hψa in

theorem goodL_norm_whittakerCoefficient {C₀ : ℝ} {M₀ : ℕ}
    (hMG : ∀ g : AdelicGL2 (𝓞 F) F, ‖G g‖ ≤ C₀ * wt F M₀ (Matrix.GeneralLinearGroup.det g))
    {B : AdeleRing (𝓞 F) F → ℂ} (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F) :
    GoodL F M₀ a (fun b =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (avg F G B) 1 (diagOne b)‖) := by
  intro L
  obtain ⟨BL, hBL, hW⟩ := iter F D U gen hGc hMGex hinv hψ ha hψa L hB
  refine ⟨(∫ x, ‖BL x‖ ∂(adelicAddHaar (𝓞 F) F)) * C₀, fun b => ?_⟩
  show (L.map fun e => |2 * Real.pi * lam F a e b|).prod *
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (avg F G B) 1 (diagOne b)‖ ≤ _
  rw [← norm_prod_coef, ← norm_mul, ← hW b]
  exact norm_whittakerCoefficient_avg_diagOne_le F D U gen hψ hMG hBL 1 b

end Class

section Axes

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F}

open scoped Classical in

def eR (w : {w : InfinitePlace F // w.IsReal}) : mixedEmbedding.mixedSpace F := (Pi.single w 1, 0)
open scoped Classical in

def eC1 (w : {w : InfinitePlace F // w.IsComplex}) : mixedEmbedding.mixedSpace F := (0, Pi.single w 1)
open scoped Classical in

def eCI (w : {w : InfinitePlace F // w.IsComplex}) : mixedEmbedding.mixedSpace F := (0, Pi.single w Complex.I)

open scoped Classical in
theorem trace_mul_eR (z : mixedEmbedding.mixedSpace F) (w : {w : InfinitePlace F // w.IsReal}) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (z * eR w) = z.1 w := by
  rw [NumberField.mixedEmbedding.trace_mixedSpace_apply]
  simp [eR, Pi.single_apply, Finset.sum_ite_eq']

open scoped Classical in
theorem trace_mul_eC1 (z : mixedEmbedding.mixedSpace F) (w : {w : InfinitePlace F // w.IsComplex}) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (z * eC1 w) = 2 * (z.2 w).re := by
  rw [NumberField.mixedEmbedding.trace_mixedSpace_apply]
  simp [eC1, Pi.single_apply, Finset.sum_ite_eq', apply_ite Complex.re]

open scoped Classical in
theorem trace_mul_eCI (z : mixedEmbedding.mixedSpace F) (w : {w : InfinitePlace F // w.IsComplex}) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (z * eCI w) = -(2 * (z.2 w).im) := by
  rw [NumberField.mixedEmbedding.trace_mixedSpace_apply]
  simp [eCI, Pi.single_apply, Finset.sum_ite_eq', apply_ite Complex.re]

omit [NumberField F] in

theorem norm_apply_of_isReal (x : InfiniteAdeleRing F) (w : {w : InfinitePlace F // w.IsReal}) :
    ‖x w.1‖ = |(InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 w| := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, ← Real.norm_eq_abs]
  exact ((isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) _).symm

omit [NumberField F] in

theorem norm_apply_of_isComplex (x : InfiniteAdeleRing F) (w : {w : InfinitePlace F // w.IsComplex}) :
    ‖x w.1‖ = ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 w‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact ((isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _).symm

variable (F)

open scoped Classical in

def axisSum (a : F) (w : InfinitePlace F) (b : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  if hw : w.IsReal then |2 * Real.pi * lam F a (eR ⟨w, hw⟩) b|
  else |2 * Real.pi * lam F a (eC1 ⟨w, not_isReal_iff_isComplex.mp hw⟩) b| +
    |2 * Real.pi * lam F a (eCI ⟨w, not_isReal_iff_isComplex.mp hw⟩) b|

theorem axisSum_nonneg (a : F) (w : InfinitePlace F) (b : (AdeleRing (𝓞 F) F)ˣ) : 0 ≤ axisSum F a w b := by
  unfold axisSum; split_ifs <;> positivity

variable {F} in

theorem GoodL.axisSum_mul {M : ℕ} {a : F} (w : InfinitePlace F) (V : (AdeleRing (𝓞 F) F)ˣ → ℝ)
    (hV : GoodL F M a V) : GoodL F M a (fun b => axisSum F a w b * V b) := by
  classical
  by_cases hw : w.IsReal
  · exact (hV.absLam_mul (eR ⟨w, hw⟩)).congr fun b => by rw [axisSum, dif_pos hw]
  · exact ((hV.absLam_mul (eC1 ⟨w, not_isReal_iff_isComplex.mp hw⟩)).add
      (hV.absLam_mul (eCI ⟨w, not_isReal_iff_isComplex.mp hw⟩))).congr fun b => by
        rw [axisSum, dif_neg hw, add_mul]

theorem exists_norm_le_mul_axisSum {a : F} (ha : a ≠ 0) :
    ∃ κ : InfinitePlace F → ℝ, (∀ w, 0 ≤ κ w) ∧
      ∀ (w : InfinitePlace F) (b : (AdeleRing (𝓞 F) F)ˣ), ‖(b : AdeleRing (𝓞 F) F).1 w‖ ≤ κ w * axisSum F a w b := by
  classical
  set A : mixedEmbedding.mixedSpace F :=
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) a⁻¹) with hAdef
  have ha' : (a⁻¹ : F) ≠ 0 := inv_ne_zero ha
  have hcoe : ∀ w : InfinitePlace F, (algebraMap F (InfiniteAdeleRing F) a⁻¹) w ≠ 0 := fun w => by
    rw [InfiniteAdeleRing.algebraMap_apply, ← norm_pos_iff, NumberField.InfinitePlace.Completion.norm_coe]
    exact w.pos_iff.mpr ha'
  have hA1 : ∀ w : {w : InfinitePlace F // w.IsReal}, A.1 w ≠ 0 := fun w => by
    rw [hAdef, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (map_ne_zero _).mpr (hcoe w.1)
  have hA2 : ∀ w : {w : InfinitePlace F // w.IsComplex}, A.2 w ≠ 0 := fun w => by
    rw [hAdef, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (map_ne_zero _).mpr (hcoe w.1)
  refine ⟨fun w => if hw : w.IsReal then |A.1 ⟨w, hw⟩|⁻¹ / (2 * Real.pi)
      else ‖A.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖⁻¹ / (4 * Real.pi), fun w => ?_, fun w b => ?_⟩
  · dsimp only
    split_ifs <;> positivity

  set Zb : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (b : AdeleRing (𝓞 F) F).1
    with hZbdef
  have hz : InfiniteAdeleRing.ringEquiv_mixedSpace F
      (algebraMap F (InfiniteAdeleRing F) a⁻¹ * (b : AdeleRing (𝓞 F) F).1) = A * Zb := by
    rw [map_mul]
  have h2π : 0 < 2 * Real.pi := by positivity
  by_cases hw : w.IsReal
  · simp only [dif_pos hw, axisSum]
    rw [lam, hz, trace_mul_eR, norm_apply_of_isReal _ ⟨w, hw⟩]
    show |Zb.1 ⟨w, hw⟩| ≤ |A.1 ⟨w, hw⟩|⁻¹ / (2 * Real.pi) * |2 * Real.pi * (A * Zb).1 ⟨w, hw⟩|
    rw [Prod.fst_mul, Pi.mul_apply, abs_mul (2 * Real.pi), abs_of_pos h2π,
      abs_mul (A.1 ⟨w, hw⟩)]
    have hA := abs_pos.mpr (hA1 ⟨w, hw⟩)
    rw [div_mul_eq_mul_div, le_div_iff₀ h2π]
    calc |Zb.1 ⟨w, hw⟩| * (2 * Real.pi)
        = |A.1 ⟨w, hw⟩|⁻¹ * (2 * Real.pi * (|A.1 ⟨w, hw⟩| * |Zb.1 ⟨w, hw⟩|)) := by field_simp
      _ ≤ _ := le_rfl
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    simp only [dif_neg hw, axisSum]
    rw [lam, lam, hz, trace_mul_eC1, trace_mul_eCI, norm_apply_of_isComplex _ ⟨w, hw'⟩]
    show ‖Zb.2 ⟨w, hw'⟩‖ ≤ ‖A.2 ⟨w, hw'⟩‖⁻¹ / (4 * Real.pi) *
      (|2 * Real.pi * (2 * ((A * Zb).2 ⟨w, hw'⟩).re)| + |2 * Real.pi * -(2 * ((A * Zb).2 ⟨w, hw'⟩).im)|)
    rw [Prod.snd_mul, Pi.mul_apply]
    set u : ℂ := A.2 ⟨w, hw'⟩ * Zb.2 ⟨w, hw'⟩ with hudef
    have hA := norm_pos_iff.mpr (hA2 ⟨w, hw'⟩)
    have hu : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    have hnorm : ‖Zb.2 ⟨w, hw'⟩‖ = ‖u‖ / ‖A.2 ⟨w, hw'⟩‖ := by
      rw [hudef, norm_mul, mul_div_cancel_left₀ _ hA.ne']
    have e1 : |2 * Real.pi * (2 * u.re)| = 4 * Real.pi * |u.re| := by
      rw [abs_mul (2 * Real.pi), abs_of_pos h2π, abs_mul 2, abs_two]; ring
    have e2 : |2 * Real.pi * -(2 * u.im)| = 4 * Real.pi * |u.im| := by
      rw [abs_mul (2 * Real.pi), abs_of_pos h2π, abs_neg, abs_mul 2, abs_two]; ring
    rw [hnorm, e1, e2, div_le_iff₀ hA]
    calc ‖u‖ ≤ |u.re| + |u.im| := hu
      _ = ‖A.2 ⟨w, hw'⟩‖⁻¹ / (4 * Real.pi) * (4 * Real.pi * |u.re| + 4 * Real.pi * |u.im|)
            * ‖A.2 ⟨w, hw'⟩‖ := by
          field_simp

end Axes

theorem rightConv_globalPoints_mul {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  congr 1
  funext x
  exact hφ γ x

end C5K5b

end

open C5K5b in
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
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ f (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℕ, ∀ m : InfinitePlace F → ℕ, ∃ C : ℝ, ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∏ w : InfinitePlace F, ‖((b : AdeleRing (𝓞 F) F).1 w)‖ ^ m w) *
        ‖whittakerCoefficient F
            (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne b)‖
          ≤ C * max (ideleNorm F b) (ideleNorm F b)⁻¹ ^ M := by
  classical

  have hGc : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  obtain ⟨C₀, M₀, hMG⟩ :=
    AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf
  have hMGex : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖rightConv F φ f g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M := ⟨C₀, M₀, hMG⟩
  have hMG' : ∀ g : AdelicGL2 (𝓞 F) F, ‖rightConv F φ f g‖ ≤ C₀ * wt F M₀ (Matrix.GeneralLinearGroup.det g) := hMG
  have hls : IsLsXiFunction (𝓞 F) F _ ξ φ := by
    letI := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
    exact ((lsXiMemberAt_iff _ _ _ _ ξ _ φ).mp hφ.1).1
  have hinv : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g :=
    fun γ g => rightConv_globalPoints_mul F hls.left_invariant f γ g

  obtain ⟨a, ha, hψa⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  obtain ⟨κ, hκ, hnorm⟩ := exists_norm_le_mul_axisSum F ha

  obtain rfl : Φ = avg F (rightConv F φ f) B := funext hΦ
  refine ⟨M₀, fun m => ?_⟩
  have base : GoodL F M₀ a (fun b => ‖whittakerCoefficient F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ (avg F (rightConv F φ f) B) 1 (diagOne b)‖) :=
    goodL_norm_whittakerCoefficient F _ _ _ hGc hMGex hinv hψ ha hψa hMG' hB
  obtain ⟨C, hC⟩ :=
    (GoodL.prod_pow_mul (fun w V hV => GoodL.axisSum_mul w V hV) Finset.univ m base).good
  refine ⟨(∏ w, κ w ^ m w) * C, fun b => ?_⟩
  have hW := hC b
  dsimp only at hW
  have hprod : (∏ w : InfinitePlace F, ‖((b : AdeleRing (𝓞 F) F).1 w)‖ ^ m w)
      ≤ (∏ w, κ w ^ m w) * ∏ w, axisSum F a w b ^ m w := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _) fun w _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm w b) _
  calc (∏ w : InfinitePlace F, ‖((b : AdeleRing (𝓞 F) F).1 w)‖ ^ m w) * _
      ≤ ((∏ w, κ w ^ m w) * ∏ w, axisSum F a w b ^ m w) * _ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = (∏ w, κ w ^ m w) * ((∏ w, axisSum F a w b ^ m w) * _) := mul_assoc _ _ _
    _ ≤ (∏ w, κ w ^ m w) * (C * wt F M₀ b) :=
        mul_le_mul_of_nonneg_left hW (Finset.prod_nonneg fun w _ => pow_nonneg (hκ w) _)
    _ = (∏ w, κ w ^ m w) * C * max (ideleNorm F b) (ideleNorm F b)⁻¹ ^ M₀ := by rw [wt, mul_assoc]

end S_AutomorphicForm_exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_prod_norm_pow_mul_norm_whittakerCoefficient_one_diagOne_unipotentAverage_le (solution)
