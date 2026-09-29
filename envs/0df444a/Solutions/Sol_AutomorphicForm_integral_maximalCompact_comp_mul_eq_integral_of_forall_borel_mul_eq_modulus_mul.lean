-- Prove2me | solution 1 for AutomorphicForm.integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/28dfaf15-a974-5feb-85eb-0e2b89ee7fa1

import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace P2mK2aInvariance

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔾" => AdelicGL2 (𝓞 F) F
local notation "𝔹" => adelicBorel (𝓞 F) F
local notation "𝕂" => adelicMaximalCompact F

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

def E (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : 𝔾 :=
  unipotentGL2 p.2.2 * centralScalar (𝓞 F) F p.2.1 * diagOne p.1

theorem centralScalar_coe_apply (z : 𝔸ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) i j = if i = j then (z : 𝔸) else 0 := by
  change (Matrix.scalar (Fin 2) (z : 𝔸)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

theorem E_coe (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ((E F p : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) =
      !![(p.2.1 : 𝔸) * (p.1 : 𝔸), p.2.2 * (p.2.1 : 𝔸); 0, (p.2.1 : 𝔸)] := by
  obtain ⟨t, z, x⟩ := p
  unfold E
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, unipotentGL2_coe,
    centralScalar_coe_apply, diagOne_coe_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem E_apply_00 (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ((E F p : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 = (p.2.1 : 𝔸) * (p.1 : 𝔸) := by
  rw [E_coe]; rfl

theorem E_apply_01 (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ((E F p : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = p.2.2 * (p.2.1 : 𝔸) := by
  rw [E_coe]; rfl

theorem E_apply_10 (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ((E F p : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := by
  rw [E_coe]; rfl

theorem E_apply_11 (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ((E F p : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 = (p.2.1 : 𝔸) := by
  rw [E_coe]; rfl

theorem E_mem (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : E F p ∈ 𝔹 := by
  rw [mem_borelSubgroup_iff, E_apply_10]

def e (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : 𝔹 := ⟨E F p, E_mem F p⟩

@[scoped simp] theorem coe_e (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : ((e F p : 𝔹) : 𝔾) = E F p := rfl

theorem borelDiagSnd_e (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : borelDiagSnd (e F p) = p.2.1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val, coe_e, E_apply_11]

theorem borelDiagFst_e (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : borelDiagFst (e F p) = p.2.1 * p.1 := by
  apply Units.ext
  rw [borelDiagFst_apply_val, coe_e, E_apply_00, Units.val_mul]

def xCoord (b : 𝔹) : 𝔸 :=
  ((b : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 * (((borelDiagSnd b)⁻¹ : 𝔸ˣ) : 𝔸)

theorem xCoord_e (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : xCoord F (e F p) = p.2.2 := by
  unfold xCoord
  rw [borelDiagSnd_e, coe_e, E_apply_01, mul_assoc, Units.mul_inv, mul_one]

theorem E_one : E F (1, (1, 0)) = 1 := by
  apply Units.ext
  rw [E_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem E_mul_E (p q : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    E F p * E F q = E F (p.1 * q.1, (p.2.1 * q.2.1, p.2.2 + (p.1 : 𝔸) * q.2.2)) := by
  obtain ⟨t, z, x⟩ := p
  obtain ⟨t', z', x'⟩ := q
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, E_coe, E_coe, E_coe]
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

scoped instance secondCountable_adele : SecondCountableTopology 𝔸 := NumberField.AdeleRing.secondCountableTopology F

scoped instance secondCountable_adele_op : SecondCountableTopology 𝔸ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountable_idele : SecondCountableTopology 𝔸ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_adele_op : LocallyCompactSpace 𝔸ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace

scoped instance locallyCompact_idele : LocallyCompactSpace 𝔸ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountable_gl : SecondCountableTopology 𝔾 :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F

theorem isClosed_adelicBorel : IsClosed ((𝔹 : Subgroup 𝔾) : Set 𝔾) := by
  have h : ((𝔹 : Subgroup 𝔾) : Set 𝔾) = (fun g : 𝔾 => (g : Matrix (Fin 2) (Fin 2) 𝔸) 1 0) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, mem_borelSubgroup_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rw [h]
  have hc : Continuous fun g : 𝔾 => (g : Matrix (Fin 2) (Fin 2) 𝔸) := Units.continuous_val
  exact isClosed_singleton.preimage (hc.matrix_elem 1 0)

theorem continuous_unipotentGL2 : Continuous fun x : 𝔸 => (unipotentGL2 x : 𝔾) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun x : 𝔸 => ((unipotentGL2 x : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸)
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun x : 𝔸 => (((unipotentGL2 x : 𝔾)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸)
    have : ∀ x : 𝔸, (((unipotentGL2 x : 𝔾)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) = !![1, -x; 0, 1] := fun x => rfl
    simp_rw [this]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_centralScalar : Continuous fun z : 𝔸ˣ => (centralScalar (𝓞 F) F z : 𝔾) := by
  change Continuous (Units.map (Matrix.scalar (Fin 2) : 𝔸 →+* Matrix (Fin 2) (Fin 2) 𝔸).toMonoidHom)
  refine Continuous.units_map _ ?_
  change Continuous fun a : 𝔸 => Matrix.scalar (Fin 2) a
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem continuous_diagOne : Continuous fun t : 𝔸ˣ => (diagOne t : 𝔾) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun t : 𝔸ˣ => ((diagOne t : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸)
    refine continuous_matrix fun i j => ?_
    simp only [diagOne_coe_apply, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · change Continuous fun t : 𝔸ˣ => (((diagOne t : 𝔾)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸)
    have : ∀ t : 𝔸ˣ, (((diagOne t : 𝔾)⁻¹ : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) =
        Matrix.diagonal ![((t⁻¹ : 𝔸ˣ) : 𝔸), 1] := fun t => rfl
    simp_rw [this]
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_E : Continuous (E F) :=
  (((continuous_unipotentGL2 F).comp (continuous_snd.comp continuous_snd)).mul
    ((continuous_centralScalar F).comp (continuous_fst.comp continuous_snd))).mul
    ((continuous_diagOne F).comp continuous_fst)

theorem continuous_entry (i j : Fin 2) : Continuous fun b : 𝔹 => ((b : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) i j :=
  ((Units.continuous_val : Continuous fun g : 𝔾 => (g : Matrix (Fin 2) (Fin 2) 𝔸)).comp
    continuous_subtype_val).matrix_elem i j

theorem continuous_borelDiagFst : Continuous fun b : 𝔹 => (borelDiagFst b : 𝔸ˣ) := by
  refine Units.continuous_iff.2 ⟨continuous_entry F 0 0, ?_⟩
  change Continuous fun b : 𝔹 => (((b⁻¹ : 𝔹) : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0
  exact (continuous_entry F 0 0).comp continuous_inv

theorem continuous_borelDiagSnd : Continuous fun b : 𝔹 => (borelDiagSnd b : 𝔸ˣ) := by
  refine Units.continuous_iff.2 ⟨continuous_entry F 1 1, ?_⟩
  change Continuous fun b : 𝔹 => (((b⁻¹ : 𝔹) : 𝔾) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1
  exact (continuous_entry F 1 1).comp continuous_inv

theorem continuous_xCoord : Continuous (xCoord F) :=
  (continuous_entry F 0 1).mul (Units.continuous_val.comp ((continuous_borelDiagSnd F).inv))

theorem continuous_tCoord : Continuous fun b : 𝔹 => borelDiagFst b * (borelDiagSnd b)⁻¹ :=
  (continuous_borelDiagFst F).mul (continuous_borelDiagSnd F).inv

theorem exists_box_of_isCompact {S : Set 𝔾} (hS : IsCompact S) :
    ∃ (S₁ : Set 𝔸ˣ) (S₂ : Set 𝔸ˣ) (S₃ : Set 𝔸), IsCompact S₁ ∧ IsCompact S₂ ∧ IsCompact S₃ ∧
      ∀ q, E F q ∈ S → q ∈ S₁ ×ˢ (S₂ ×ˢ S₃) := by
  set S' : Set 𝔹 := ((↑) : 𝔹 → 𝔾) ⁻¹' S with hS'
  have hS'c : IsCompact S' := (isClosed_adelicBorel F).isClosedEmbedding_subtypeVal.isCompact_preimage hS
  refine ⟨(fun b : 𝔹 => borelDiagFst b * (borelDiagSnd b)⁻¹) '' S', (fun b : 𝔹 => borelDiagSnd b) '' S',
    xCoord F '' S', hS'c.image (continuous_tCoord F), hS'c.image (continuous_borelDiagSnd F),
    hS'c.image (continuous_xCoord F), ?_⟩
  rintro ⟨t, z, x⟩ hq
  have hp : e F (t, (z, x)) ∈ S' := hq
  refine ⟨⟨e F (t, (z, x)), hp, ?_⟩, ⟨e F (t, (z, x)), hp, ?_⟩, ⟨e F (t, (z, x)), hp, ?_⟩⟩
  · change borelDiagFst (e F (t, (z, x))) * (borelDiagSnd (e F (t, (z, x))))⁻¹ = t
    rw [borelDiagFst_e, borelDiagSnd_e, mul_inv_cancel_comm]
  · change borelDiagSnd (e F (t, (z, x))) = z
    rw [borelDiagSnd_e]
  · change xCoord F (e F (t, (z, x))) = x
    rw [xCoord_e]

theorem measurable_E [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ] :
    Measurable (E F) := by
  have hu : Measurable fun x : 𝔸 => (unipotentGL2 x : 𝔾) := (continuous_unipotentGL2 F).measurable
  have hc : Measurable fun z : 𝔸ˣ => (centralScalar (𝓞 F) F z : 𝔾) := (continuous_centralScalar F).measurable
  have hd : Measurable fun t : 𝔸ˣ => (diagOne t : 𝔾) := (continuous_diagOne F).measurable
  exact ((hu.comp (measurable_snd.comp measurable_snd)).mul
    (hc.comp (measurable_fst.comp measurable_snd))).mul (hd.comp measurable_fst)

theorem measurable_E_mul [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ] :
    Measurable fun p : (𝔸ˣ × (𝔸ˣ × 𝔸)) × 𝔾 => E F p.1 * p.2 :=
  ((measurable_E F).comp measurable_fst).mul measurable_snd

def Aη [MeasurableSpace 𝔸] [MeasurableSpace 𝔸ˣ] (dx : Measure 𝔸) (dz dt : Measure 𝔸ˣ)
    (η : 𝔾 → ℝ≥0∞) (g : 𝔾) : ℝ≥0∞ :=
  ∫⁻ q, η (E F q * g) ∂(dt.prod (dz.prod dx))

theorem measurable_Aη [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    {η : 𝔾 → ℝ≥0∞} (hη : Measurable η) : Measurable (Aη F dx dz dt η) := by
  unfold Aη
  exact (hη.comp (measurable_E_mul F)).lintegral_prod_left'

def shift (p q : 𝔸ˣ × (𝔸ˣ × 𝔸)) : 𝔸ˣ × (𝔸ˣ × 𝔸) :=
  (q.1 * p.1, (q.2.1 * p.2.1, q.2.2 + (q.1 : 𝔸) * p.2.2))

theorem shift_apply (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) (t z : 𝔸ˣ) (x : 𝔸) :
    shift F p (t, (z, x)) = (t * p.1, (z * p.2.1, x + (t : 𝔸) * p.2.2)) := rfl

theorem measurable_shift [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) : Measurable (shift F p) := by
  unfold shift
  refine (measurable_fst.mul_const _).prodMk (((measurable_fst.comp measurable_snd).mul_const _).prodMk ?_)
  exact (measurable_snd.comp measurable_snd).add
    ((Units.continuous_val.measurable.comp measurable_fst).mul_const _)

theorem lintegral_shift [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    (H : 𝔸ˣ × (𝔸ˣ × 𝔸) → ℝ≥0∞) (hH : Measurable H) (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ∫⁻ q, H (shift F p q) ∂(dt.prod (dz.prod dx)) = ∫⁻ q, H q ∂(dt.prod (dz.prod dx)) := by
  have hHs : Measurable fun q => H (shift F p q) := hH.comp (measurable_shift F p)
  rw [lintegral_prod _ hHs.aemeasurable, lintegral_prod _ hH.aemeasurable]
  have hslice : ∀ t : 𝔸ˣ,
      ∫⁻ zx : 𝔸ˣ × 𝔸, H (shift F p (t, zx)) ∂(dz.prod dx) = ∫⁻ zx : 𝔸ˣ × 𝔸, H (t * p.1, zx) ∂(dz.prod dx) := by
    intro t
    have hm1 : Measurable fun zx : 𝔸ˣ × 𝔸 => H (shift F p (t, zx)) := hHs.comp measurable_prodMk_left
    have hm2 : Measurable fun zx : 𝔸ˣ × 𝔸 => H (t * p.1, zx) := hH.comp measurable_prodMk_left
    rw [lintegral_prod (μ := dz) (ν := dx) (fun zx : 𝔸ˣ × 𝔸 => H (shift F p (t, zx))) hm1.aemeasurable,
      lintegral_prod (μ := dz) (ν := dx) (fun zx : 𝔸ˣ × 𝔸 => H (t * p.1, zx)) hm2.aemeasurable]
    have hx : ∀ z : 𝔸ˣ, ∫⁻ x, H (shift F p (t, (z, x))) ∂dx = ∫⁻ x, H (t * p.1, (z * p.2.1, x)) ∂dx := by
      intro z
      simp only [shift_apply]
      exact lintegral_add_right_eq_self (μ := dx) (fun x => H (t * p.1, (z * p.2.1, x))) ((t : 𝔸) * p.2.2)
    have hx' : ∀ z : 𝔸ˣ, ∫⁻ x, H (shift F p (t, (z, x))) ∂dx =
        (fun z' : 𝔸ˣ => ∫⁻ x, H (t * p.1, (z', x)) ∂dx) (z * p.2.1) := hx
    change ∫⁻ z, ∫⁻ x, H (shift F p (t, (z, x))) ∂dx ∂dz = ∫⁻ z, ∫⁻ x, H (t * p.1, (z, x)) ∂dx ∂dz
    simp_rw [hx']
    exact lintegral_mul_right_eq_self (μ := dz) (fun z' => ∫⁻ x, H (t * p.1, (z', x)) ∂dx) p.2.1
  have hslice' : ∀ t : 𝔸ˣ, ∫⁻ zx : 𝔸ˣ × 𝔸, H (shift F p (t, zx)) ∂(dz.prod dx) =
      (fun t' : 𝔸ˣ => ∫⁻ zx : 𝔸ˣ × 𝔸, H (t', zx) ∂(dz.prod dx)) (t * p.1) := hslice
  change ∫⁻ t, ∫⁻ zx, H (shift F p (t, zx)) ∂(dz.prod dx) ∂dt = ∫⁻ t, ∫⁻ zx, H (t, zx) ∂(dz.prod dx) ∂dt
  simp_rw [hslice']
  exact lintegral_mul_right_eq_self (μ := dt) (fun t' => ∫⁻ zx, H (t', zx) ∂(dz.prod dx)) p.1

theorem Aη_E_mul [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    {η : 𝔾 → ℝ≥0∞} (hη : Measurable η) (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾) :
    Aη F dx dz dt η (E F p * g) = Aη F dx dz dt η g := by
  have hHm : Measurable (fun q : 𝔸ˣ × (𝔸ˣ × 𝔸) => η (E F q * g)) := hη.comp ((measurable_E F).mul_const g)
  unfold Aη
  rw [← lintegral_shift F dx dz dt (fun q : 𝔸ˣ × (𝔸ˣ × 𝔸) => η (E F q * g)) hHm p]
  refine lintegral_congr fun q => ?_
  change η (E F q * (E F p * g)) = η (E F (shift F p q) * g)
  rw [← mul_assoc, E_mul_E]
  rfl

theorem Aη_indicator_ne_zero [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    {O : Set 𝔾} (hO : IsOpen O) {g : 𝔾} (hg : g ∈ O) :
    Aη F dx dz dt (O.indicator 1) g ≠ 0 := by
  unfold Aη
  set U : Set (𝔸ˣ × (𝔸ˣ × 𝔸)) := (fun q => E F q * g) ⁻¹' O with hU
  have hUo : IsOpen U := hO.preimage ((continuous_E F).mul continuous_const)
  have hmem : ((1 : 𝔸ˣ), ((1 : 𝔸ˣ), (0 : 𝔸))) ∈ U := by
    change E F (1, (1, 0)) * g ∈ O
    rwa [E_one, one_mul]
  have hind : ∀ q : 𝔸ˣ × (𝔸ˣ × 𝔸), O.indicator (1 : 𝔾 → ℝ≥0∞) (E F q * g) = U.indicator 1 q := by
    intro q
    by_cases h : E F q * g ∈ O
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ U from h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show q ∉ U from h)]
  simp_rw [hind]
  rw [lintegral_indicator_one hUo.measurableSet]
  exact (hUo.measure_pos _ ⟨_, hmem⟩).ne'

theorem Aη_indicator_ne_top [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    {O : Set 𝔾} (hO : IsCompact (closure O)) (g : 𝔾) :
    Aη F dx dz dt (O.indicator 1) g ≠ ⊤ := by
  unfold Aη

  set S : Set 𝔾 := (fun y => y * g⁻¹) '' closure O with hS
  have hSc : IsCompact S := hO.image (continuous_mul_const _)
  obtain ⟨S₁, S₂, S₃, h₁, h₂, h₃, hbox⟩ := exists_box_of_isCompact F hSc
  have hle : ∀ q : 𝔸ˣ × (𝔸ˣ × 𝔸),
      O.indicator (1 : 𝔾 → ℝ≥0∞) (E F q * g) ≤ (S₁ ×ˢ (S₂ ×ˢ S₃)).indicator 1 q := by
    intro q
    by_cases h : E F q * g ∈ O
    · have hq : E F q ∈ S := ⟨E F q * g, subset_closure h, by simp⟩
      rw [Set.indicator_of_mem h, Set.indicator_of_mem (hbox q hq)]
      exact le_rfl
    · rw [Set.indicator_of_notMem h]; exact bot_le
  have hmeas : MeasurableSet (S₁ ×ˢ (S₂ ×ˢ S₃)) :=
    h₁.isClosed.measurableSet.prod (h₂.isClosed.measurableSet.prod h₃.isClosed.measurableSet)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
  rw [lintegral_indicator_one hmeas, Measure.prod_prod, Measure.prod_prod]
  exact (ENNReal.mul_lt_top h₁.measure_lt_top (ENNReal.mul_lt_top h₂.measure_lt_top h₃.measure_lt_top)).ne

theorem lintegral_reorder [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    (H : 𝔸ˣ × (𝔸ˣ × 𝔸) → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ x, ∫⁻ z, ∫⁻ t, H (t, (z, x)) ∂dt ∂dz ∂dx = ∫⁻ t, ∫⁻ z, ∫⁻ x, H (t, (z, x)) ∂dx ∂dz ∂dt := by
  have hH2 : Measurable fun p : 𝔸ˣ × (𝔸ˣ × 𝔸) => H (p.1, p.2) := hH
  have h1 : ∫⁻ t, ∫⁻ z, ∫⁻ x, H (t, (z, x)) ∂dx ∂dz ∂dt = ∫⁻ t, ∫⁻ p, H (t, p) ∂(dz.prod dx) ∂dt := by
    refine lintegral_congr fun t => ?_
    exact (lintegral_prod (μ := dz) (ν := dx) (fun p : 𝔸ˣ × 𝔸 => H (t, p))
      (hH.comp measurable_prodMk_left).aemeasurable).symm
  have h2 : ∫⁻ t, ∫⁻ p, H (t, p) ∂(dz.prod dx) ∂dt = ∫⁻ p, ∫⁻ t, H (t, p) ∂dt ∂(dz.prod dx) :=
    lintegral_lintegral_swap (μ := dt) (ν := dz.prod dx) (f := fun t p => H (t, p)) hH2.aemeasurable
  have hI : Measurable fun p : 𝔸ˣ × 𝔸 => ∫⁻ t, H (t, p) ∂dt := hH2.lintegral_prod_left'
  have h3 : ∫⁻ p, ∫⁻ t, H (t, p) ∂dt ∂(dz.prod dx) = ∫⁻ z, ∫⁻ x, ∫⁻ t, H (t, (z, x)) ∂dt ∂dx ∂dz :=
    lintegral_prod (μ := dz) (ν := dx) (fun p : 𝔸ˣ × 𝔸 => ∫⁻ t, H (t, p) ∂dt) hI.aemeasurable
  have hI2 : Measurable fun p : 𝔸ˣ × 𝔸 => ∫⁻ t, H (t, (p.1, p.2)) ∂dt := hI
  have h4 : ∫⁻ z, ∫⁻ x, ∫⁻ t, H (t, (z, x)) ∂dt ∂dx ∂dz = ∫⁻ x, ∫⁻ z, ∫⁻ t, H (t, (z, x)) ∂dt ∂dz ∂dx :=
    lintegral_lintegral_swap (μ := dz) (ν := dx) (f := fun z x => ∫⁻ t, H (t, (z, x)) ∂dt) hI2.aemeasurable
  rw [h1, h2, h3, h4]

theorem key [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    (c : ℝ≥0∞)
    (hP2 : ∀ f : 𝔾 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ t, ∫⁻ z, ∫⁻ x,
          (∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : 𝔾)) ∂(maximalCompactHaar F)) *
            ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ ∂dx ∂dz ∂dt)
    {η : 𝔾 → ℝ≥0∞} (hη : Measurable η)
    (hA : ∀ k : 𝕂, Aη F dx dz dt η k ≠ 0 ∧ Aη F dx dz dt η k ≠ ⊤)
    {Ψ : 𝔾 → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hlaw : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾), Ψ (E F q * g) = (distribHaarChar 𝔸 q.1 : ℝ≥0∞) * Ψ g) :
    ∫⁻ g, η g * (Aη F dx dz dt η g)⁻¹ * Ψ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
      c * ∫⁻ k, Ψ (k : 𝔾) ∂(maximalCompactHaar F) := by
  haveI : IsFiniteMeasure (maximalCompactHaar F) := CompactSpace.isFiniteMeasure
  set A := Aη F dx dz dt η with hAdef
  have hAm : Measurable A := measurable_Aη F dx dz dt hη
  set f : 𝔾 → ℝ≥0∞ := fun g => η g * (A g)⁻¹ * Ψ g with hf
  have hfm : Measurable f := (hη.mul hAm.inv).mul hΨ
  rw [hP2 f hfm]

  set G : (𝔸ˣ × (𝔸ˣ × 𝔸)) → 𝕂 → ℝ≥0∞ := fun q k => η (E F q * k) * ((A k)⁻¹ * Ψ k) with hG
  have hGm : Measurable (Function.uncurry G) := by
    have hk : Measurable fun p : (𝔸ˣ × (𝔸ˣ × 𝔸)) × 𝕂 => ((p.2 : 𝕂) : 𝔾) :=
      continuous_subtype_val.measurable.comp measurable_snd
    have h1 : Measurable fun p : (𝔸ˣ × (𝔸ˣ × 𝔸)) × 𝕂 => η (E F p.1 * (p.2 : 𝔾)) :=
      hη.comp (((measurable_E F).comp measurable_fst).mul hk)
    exact h1.mul ((hAm.comp hk).inv.mul (hΨ.comp hk))
  have hcancel : ∀ (t z : 𝔸ˣ) (x : 𝔸),
      (∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : 𝔾)) ∂(maximalCompactHaar F)) *
          ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ =
        ∫⁻ k, G (t, (z, x)) k ∂(maximalCompactHaar F) := by
    intro t z x
    have hm : Measurable fun k : 𝕂 => f (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : 𝔾)) :=
      hfm.comp (continuous_subtype_val.measurable.const_mul _)
    rw [← lintegral_mul_const _ hm]
    refine lintegral_congr fun k => ?_
    change η (E F (t, (z, x)) * k) * (A (E F (t, (z, x)) * k))⁻¹ * Ψ (E F (t, (z, x)) * k) *
        ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ = η (E F (t, (z, x)) * k) * ((A k)⁻¹ * Ψ k)
    rw [hAdef, Aη_E_mul F dx dz dt hη, hlaw]
    have hd0 : (distribHaarChar 𝔸 t : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (distribHaarChar_pos).ne'
    have hdt : (distribHaarChar 𝔸 t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    calc η (E F (t, (z, x)) * k) * (Aη F dx dz dt η k)⁻¹ * ((distribHaarChar 𝔸 t : ℝ≥0∞) * Ψ k) *
          ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹
        = η (E F (t, (z, x)) * k) * ((Aη F dx dz dt η k)⁻¹ * Ψ k) *
            ((distribHaarChar 𝔸 t : ℝ≥0∞) * ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹) := by ring
      _ = η (E F (t, (z, x)) * k) * ((Aη F dx dz dt η k)⁻¹ * Ψ k) := by
          rw [ENNReal.mul_inv_cancel hd0 hdt, mul_one]
  simp_rw [hcancel]

  have hGq : Measurable fun q : 𝔸ˣ × (𝔸ˣ × 𝔸) => ∫⁻ k, G q k ∂(maximalCompactHaar F) :=
    hGm.lintegral_prod_right'
  have h3 : ∫⁻ t, ∫⁻ z, ∫⁻ x, ∫⁻ k, G (t, (z, x)) k ∂(maximalCompactHaar F) ∂dx ∂dz ∂dt =
      ∫⁻ q, ∫⁻ k, G q k ∂(maximalCompactHaar F) ∂(dt.prod (dz.prod dx)) := by
    rw [lintegral_prod _ hGq.aemeasurable]
    refine lintegral_congr fun t => ?_
    exact (lintegral_prod (μ := dz) (ν := dx) (fun y : 𝔸ˣ × 𝔸 => ∫⁻ k, G (t, y) k ∂(maximalCompactHaar F))
      (hGq.comp measurable_prodMk_left).aemeasurable).symm
  rw [h3, lintegral_lintegral_swap hGm.aemeasurable]
  congr 1
  refine lintegral_congr fun k => ?_
  have hm : Measurable fun q : 𝔸ˣ × (𝔸ˣ × 𝔸) => η (E F q * (k : 𝔾)) :=
    hη.comp ((measurable_E F).mul_const _)
  change ∫⁻ q, η (E F q * (k : 𝔾)) * ((A k)⁻¹ * Ψ k) ∂(dt.prod (dz.prod dx)) = Ψ k
  rw [lintegral_mul_const _ hm]
  change A k * ((A k)⁻¹ * Ψ k) = Ψ k
  rw [← mul_assoc, ENNReal.mul_inv_cancel (hA k).1 (hA k).2, one_mul]

theorem lintegral_comp_mul_eq [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hP2 : ∀ f : 𝔾 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ t, ∫⁻ z, ∫⁻ x,
          (∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : 𝔾)) ∂(maximalCompactHaar F)) *
            ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ ∂dx ∂dz ∂dt)
    {Ψ : 𝔾 → ℝ≥0∞} (hΨ : Measurable Ψ)
    (hlaw : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾), Ψ (E F q * g) = (distribHaarChar 𝔸 q.1 : ℝ≥0∞) * Ψ g)
    (x : 𝔾) :
    ∫⁻ k, Ψ ((k : 𝔾) * x) ∂(maximalCompactHaar F) = ∫⁻ k, Ψ (k : 𝔾) ∂(maximalCompactHaar F) := by
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F

  have hC : IsCompact ((𝕂 : Set 𝔾) ∪ (fun k : 𝔾 => k * x) '' (𝕂 : Set 𝔾)) :=
    (isCompact_adelicMaximalCompact F).union ((isCompact_adelicMaximalCompact F).image (continuous_mul_const x))
  obtain ⟨O, hO, hCO, hOc⟩ := exists_isOpen_superset_and_isCompact_closure hC
  set η : 𝔾 → ℝ≥0∞ := O.indicator 1 with hηdef
  have hη : Measurable η := measurable_one.indicator hO.measurableSet
  have hA1 : ∀ k : 𝕂, Aη F dx dz dt η k ≠ 0 ∧ Aη F dx dz dt η k ≠ ⊤ := fun k =>
    ⟨Aη_indicator_ne_zero F dx dz dt hO (hCO (Or.inl k.2)), Aη_indicator_ne_top F dx dz dt hOc _⟩

  set ηx : 𝔾 → ℝ≥0∞ := fun g => η (g * x) with hηx
  have hηxm : Measurable ηx := hη.comp (measurable_mul_const x)
  have hAx : ∀ g : 𝔾, Aη F dx dz dt ηx g = Aη F dx dz dt η (g * x) := by
    intro g
    unfold Aη
    simp only [hηx, mul_assoc]
  have hA2 : ∀ k : 𝕂, Aη F dx dz dt ηx k ≠ 0 ∧ Aη F dx dz dt ηx k ≠ ⊤ := by
    intro k
    rw [hAx]
    exact ⟨Aη_indicator_ne_zero F dx dz dt hO (hCO (Or.inr ⟨k, k.2, rfl⟩)),
      Aη_indicator_ne_top F dx dz dt hOc _⟩
  set Ψx : 𝔾 → ℝ≥0∞ := fun g => Ψ (g * x) with hΨx
  have hΨxm : Measurable Ψx := hΨ.comp (measurable_mul_const x)
  have hlawx : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾), Ψx (E F q * g) = (distribHaarChar 𝔸 q.1 : ℝ≥0∞) * Ψx g := by
    intro q g
    simp only [hΨx, mul_assoc]
    exact hlaw q (g * x)
  have e1 := key F dx dz dt c hP2 hη hA1 hΨ hlaw
  have e2 := key F dx dz dt c hP2 hηxm hA2 hΨxm hlawx
  have e3 : ∫⁻ g, ηx g * (Aη F dx dz dt ηx g)⁻¹ * Ψx g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫⁻ g, η g * (Aη F dx dz dt η g)⁻¹ * Ψ g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    simp_rw [hAx]
    exact lintegral_mul_right_eq_self (fun g => η g * (Aη F dx dz dt η g)⁻¹ * Ψ g) x
  have h : c * ∫⁻ k, Ψ ((k : 𝔾) * x) ∂(maximalCompactHaar F) = c * ∫⁻ k, Ψ (k : 𝔾) ∂(maximalCompactHaar F) := by
    rw [← e1, ← e3, e2]
  exact (ENNReal.mul_right_inj hc0 hctop).mp h

theorem modulus_E (p : 𝔸ˣ × (𝔸ˣ × 𝔸)) :
    ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar 𝔸)).toHomUnits
          (borelDiagFst (⟨E F p, E_mem F p⟩ : 𝔹)) : ℝˣ) : ℝ) /
        ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar 𝔸)).toHomUnits
          (borelDiagSnd (⟨E F p, E_mem F p⟩ : 𝔹)) : ℝˣ) : ℝ) =
      ((distribHaarChar 𝔸 p.1 : ℝ≥0) : ℝ) := by
  rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits]
  change ((distribHaarChar 𝔸 (borelDiagFst (e F p)) : ℝ≥0) : ℝ) /
      ((distribHaarChar 𝔸 (borelDiagSnd (e F p)) : ℝ≥0) : ℝ) = _
  rw [borelDiagFst_e, borelDiagSnd_e, map_mul, NNReal.coe_mul]
  have h : ((distribHaarChar 𝔸 p.2.1 : ℝ≥0) : ℝ) ≠ 0 := (NNReal.coe_pos.mpr distribHaarChar_pos).ne'
  field_simp

theorem integral_real_comp_mul_eq [MeasurableSpace 𝔸] [BorelSpace 𝔸] [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ]
    (dx : Measure 𝔸) [dx.IsAddHaarMeasure] (dz dt : Measure 𝔸ˣ) [dz.IsHaarMeasure] [dt.IsHaarMeasure]
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hP2 : ∀ f : 𝔾 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ t, ∫⁻ z, ∫⁻ x,
          (∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : 𝔾)) ∂(maximalCompactHaar F)) *
            ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ ∂dx ∂dz ∂dt)
    {ψ : 𝔾 → ℝ} (hψc : Continuous ψ)
    (hlaw : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾), ψ (E F q * g) = ((distribHaarChar 𝔸 q.1 : ℝ≥0) : ℝ) * ψ g)
    (x : 𝔾) :
    ∫ k, ψ ((k : 𝔾) * x) ∂(maximalCompactHaar F) = ∫ k, ψ (k : 𝔾) ∂(maximalCompactHaar F) := by
  have hint : ∀ y : 𝔾, Integrable (fun k : 𝕂 => ψ ((k : 𝔾) * y)) (maximalCompactHaar F) := fun y =>
    ((hψc.comp (continuous_mul_const y)).comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint1 : Integrable (fun k : 𝕂 => ψ (k : 𝔾)) (maximalCompactHaar F) := by
    simpa using hint 1

  have hpos : ∀ (s : ℝ) (hs : s = 1 ∨ s = -1),
      ∫⁻ k, ENNReal.ofReal (s * ψ ((k : 𝔾) * x)) ∂(maximalCompactHaar F) =
        ∫⁻ k, ENNReal.ofReal (s * ψ (k : 𝔾)) ∂(maximalCompactHaar F) := by
    intro s _
    have hm : Measurable fun g : 𝔾 => ENNReal.ofReal (s * ψ g) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul hψc.measurable)
    refine lintegral_comp_mul_eq F dx dz dt c hc0 hctop hP2 hm ?_ x
    intro q g
    rw [hlaw, mul_left_comm, ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint x),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint1]
  have h1 := hpos 1 (Or.inl rfl)
  have h2 := hpos (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at h1 h2
  rw [h1, h2]

theorem main
    (Φ : 𝔾 → ℂ) (hΦc : Continuous Φ)
    (hΦ : ∀ (b : 𝔾) (hb : b ∈ 𝔹) (g : 𝔾),
      Φ (b * g) =
        ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar 𝔸)).toHomUnits
              (borelDiagFst (⟨b, hb⟩ : 𝔹)) : ℝˣ) : ℝ) /
            ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar 𝔸)).toHomUnits
              (borelDiagSnd (⟨b, hb⟩ : 𝔹)) : ℝˣ) : ℝ) : ℝ) : ℂ) * Φ g)
    (x : 𝔾) :
    ∫ k, Φ ((k : 𝔾) * x) ∂(maximalCompactHaar F) = ∫ k, Φ (k : 𝔾) ∂(maximalCompactHaar F) := by

  letI : MeasurableSpace 𝔸 := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace 𝔸 := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  letI : MeasurableSpace 𝔸ˣ := NumberField.Idele.ideleBorel F
  haveI : BorelSpace 𝔸ˣ := NumberField.Idele.borelSpace_ideleBorel F
  haveI : (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set dx : Measure 𝔸 := NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F with hdx
  haveI : dx.IsAddHaarMeasure := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  set dz : Measure 𝔸ˣ := NumberField.Idele.idelicHaar F with hdz
  haveI : dz.IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar F
  obtain ⟨c, hc0, hctop, h62⟩ := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa F

  have hdens : ∀ t : 𝔸ˣ, ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) =
      ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ := by
    intro t
    have hpos : 0 < ((distribHaarChar 𝔸 t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr distribHaarChar_pos
    change ENNReal.ofReal (((distribHaarChar 𝔸 t : ℝ≥0) : ℝ)⁻¹) = _
    rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_coe_nnreal]
  have hdm : Measurable fun t : 𝔸ˣ => ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ := by
    have h : (fun t : 𝔸ˣ => ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹) =
        fun t => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) := funext fun t => (hdens t).symm
    rw [h]
    exact ENNReal.measurable_ofReal.comp ((NumberField.TateGlobal.continuous_ideleNorm F).measurable.inv)

  have hP2 : ∀ f : 𝔾 → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ t, ∫⁻ z, ∫⁻ x,
          (∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t * (k : 𝔾)) ∂(maximalCompactHaar F)) *
            ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ ∂dx ∂dz ∂dz := by
    intro f hf
    rw [h62 f hf]
    congr 1

    have hin : ∀ (x : 𝔸) (u t : 𝔸ˣ),
        ∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : 𝔾)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) ∂(maximalCompactHaar F) =
          (∫⁻ k, f (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : 𝔾)) ∂(maximalCompactHaar F)) *
            ((distribHaarChar 𝔸 t : ℝ≥0∞))⁻¹ := by
      intro x u t
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hdens]
    simp_rw [hin]

    have hK : Measurable fun p : (𝔸ˣ × (𝔸ˣ × 𝔸)) × 𝕂 => f (E F p.1 * (p.2 : 𝔾)) :=
      hf.comp (((measurable_E F).comp measurable_fst).mul (continuous_subtype_val.measurable.comp measurable_snd))
    have hH : Measurable fun q : 𝔸ˣ × (𝔸ˣ × 𝔸) =>
        (∫⁻ k, f (E F q * (k : 𝔾)) ∂(maximalCompactHaar F)) * ((distribHaarChar 𝔸 q.1 : ℝ≥0∞))⁻¹ :=
      hK.lintegral_prod_right'.mul (hdm.comp measurable_fst)
    exact lintegral_reorder F dx dz dz (fun q : 𝔸ˣ × (𝔸ˣ × 𝔸) =>
      (∫⁻ k, f (E F q * (k : 𝔾)) ∂(maximalCompactHaar F)) * ((distribHaarChar 𝔸 q.1 : ℝ≥0∞))⁻¹) hH

  have hlawC : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾),
      Φ (E F q * g) = ((((distribHaarChar 𝔸 q.1 : ℝ≥0) : ℝ) : ℝ) : ℂ) * Φ g := by
    intro q g
    rw [hΦ (E F q) (E_mem F q) g, modulus_E]
  have hre : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾),
      (Φ (E F q * g)).re = ((distribHaarChar 𝔸 q.1 : ℝ≥0) : ℝ) * (Φ g).re := by
    intro q g; rw [hlawC, Complex.re_ofReal_mul]
  have him : ∀ (q : 𝔸ˣ × (𝔸ˣ × 𝔸)) (g : 𝔾),
      (Φ (E F q * g)).im = ((distribHaarChar 𝔸 q.1 : ℝ≥0) : ℝ) * (Φ g).im := by
    intro q g; rw [hlawC, Complex.im_ofReal_mul]
  have eRe := integral_real_comp_mul_eq F dx dz dz c hc0 hctop hP2 (Complex.continuous_re.comp hΦc) hre x
  have eIm := integral_real_comp_mul_eq F dx dz dz c hc0 hctop hP2 (Complex.continuous_im.comp hΦc) him x

  have hint : ∀ y : 𝔾, Integrable (fun k : 𝕂 => Φ ((k : 𝔾) * y)) (maximalCompactHaar F) := fun y =>
    ((hΦc.comp (continuous_mul_const y)).comp continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint1 : Integrable (fun k : 𝕂 => Φ (k : 𝔾)) (maximalCompactHaar F) := by simpa using hint 1
  apply Complex.ext
  · have a := integral_re (hint x)
    have b := integral_re hint1
    simp only [RCLike.re_to_complex] at a b
    rw [← a, ← b]
    exact eRe
  · have a := integral_im (hint x)
    have b := integral_im hint1
    simp only [RCLike.im_to_complex] at a b
    rw [← a, ← b]
    exact eIm

end P2mK2aInvariance
p2m_reactivate "P2MW.S_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul.P2mK2aInvariance"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul.P2mK2aInvariance"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (Φ : AdelicGL2 (𝓞 K) K → ℂ) (_hΦc : Continuous Φ)
      (_hΦ : ∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ AutomorphicForm.adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
        Φ (b * g) =
          ((((αm (AutomorphicForm.borelDiagFst (⟨b, hb⟩ : ↥(AutomorphicForm.adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
              ((αm (AutomorphicForm.borelDiagSnd (⟨b, hb⟩ : ↥(AutomorphicForm.adelicBorel (𝓞 K) K))) : ℝˣ) :
                ℝ) : ℝ) : ℂ) * Φ g)
      (x : AdelicGL2 (𝓞 K) K),
      ∫ k, Φ ((k : AdelicGL2 (𝓞 K) K) * x) ∂(AutomorphicForm.maximalCompactHaar K) =
        ∫ k, Φ (k : AdelicGL2 (𝓞 K) K) ∂(AutomorphicForm.maximalCompactHaar K) := by
  intro αm Φ hΦc hΦ x
  exact P2mK2aInvariance.main K Φ hΦc hΦ x

end S_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
end P2MW
export P2MW.S_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul (solution)
