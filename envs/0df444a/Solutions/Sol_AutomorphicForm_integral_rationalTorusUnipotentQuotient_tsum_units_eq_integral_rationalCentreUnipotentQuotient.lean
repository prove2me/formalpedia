-- Prove2me | solution 1 for AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/da9e7b50-47a6-5f4e-bb02-e63320aa6a9f

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_iUnion_inv_smul_of_leftCosetRepresentatives
import Theorems.Thm_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
import Theorems.Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
import Theorems.Thm_AutomorphicForm_existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isClosed_rationalCentreUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.AutomorphicForm"
open Filter Topology
open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure rationalCentre rationalCentreUnipotent RationalCentreUnipotentQuotient rationalCentreUnipotentHaar rationalCentreUnipotentQuotientMeasure toAdelicUnipotent unipotentGL2 unipotentGL2_coe unipotentGL2Hom AdelicGL2 globalPoints borelSubgroup unipotentGL2_mem_borelSubgroup globalPoints_apply existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup isFundamentalDomain_boxSheet_rationalCentreUnipotent isFundamentalDomain_boxSheet_rationalTorusUnipotent isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalCentreUnipotent isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

namespace TorusUnfoldC9C

set_option linter.deprecated false in
theorem measurable_tsum_complex {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  classical
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  let A : ℕ → Finset ι := fun n => (Finset.range n).preimage e (he.injOn)
  have hAmono : Monotone A := by
    intro m n hmn i hi
    simp only [A, Finset.mem_preimage, Finset.mem_range] at hi ⊢
    exact lt_of_lt_of_le hi hmn
  have hAex : ∀ i, ∃ n, i ∈ A n := fun i => ⟨e i + 1, by simp [A]⟩
  have hA : Tendsto A atTop atTop := tendsto_atTop_finset_of_monotone hAmono hAex
  let M : Set α := {x | Summable fun i => f i x}
  have key : ∀ x, (Summable fun i => f i x) ↔ (∑' i, (‖f i x‖₊ : ℝ≥0∞)) ≠ ⊤ := fun x => by
    rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    simp only [coe_nnnorm]
    exact summable_norm_iff.symm
  have hM : MeasurableSet M := by
    have hmeas : Measurable fun x => ∑' i, (‖f i x‖₊ : ℝ≥0∞) :=
      Measurable.ennreal_tsum fun i => (hf i).nnnorm.coe_nnreal_ennreal
    have : M = (fun x => ∑' i, (‖f i x‖₊ : ℝ≥0∞)) ⁻¹' {⊤}ᶜ := by
      ext x
      simp only [M, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact key x
    rw [this]
    exact hmeas (measurableSet_singleton ⊤).compl
  let t : ℕ → α → ℂ := fun n => M.indicator fun x => ∑ i ∈ A n, f i x
  have ht : ∀ n, Measurable (t n) := fun n => (Finset.measurable_sum _ fun i _ => hf i).indicator hM
  have hlim : ∀ x, Tendsto (fun n => t n x) atTop (𝓝 (∑' i, f i x)) := by
    intro x
    by_cases hx : x ∈ M
    · have h1 : (fun n => t n x) = (fun s : Finset ι => ∑ i ∈ s, f i x) ∘ A := by
        funext n; simp only [t, Set.indicator_of_mem hx, Function.comp_apply]
      rw [h1]
      exact (Summable.hasSum hx).comp hA
    · have h1 : (fun n => t n x) = fun _ => 0 := by
        funext n; simp only [t, Set.indicator_of_notMem hx]
      rw [h1, tsum_eq_zero_of_not_summable hx]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable ht (tendsto_pi_nhds.mpr hlim)

theorem enorm_tsum_le {ι : Type*} (f : ι → ℂ) : ‖∑' i, f i‖ₑ ≤ ∑' i, ‖f i‖ₑ := by
  by_cases h : Summable f
  · have hn : Summable fun i => ‖f i‖₊ := by
      rw [← NNReal.summable_coe]; simp only [coe_nnnorm]; exact summable_norm_iff.mpr h
    calc ‖∑' i, f i‖ₑ = ((‖∑' i, f i‖₊ : ℝ≥0) : ℝ≥0∞) := rfl
      _ ≤ ((∑' i, ‖f i‖₊ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (nnnorm_tsum_le hn)
      _ = ∑' i, ‖f i‖ₑ := by rw [ENNReal.coe_tsum hn]; rfl
  · rw [tsum_eq_zero_of_not_summable h, enorm_zero]
    exact bot_le

variable (F : Type) [Field F] [NumberField F]

def ratCentralHom : Fˣ →* AdelicGL2 (𝓞 F) F :=
  (globalPoints (𝓞 F) F).comp (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom)

def diagHom : Fˣ →* AdelicGL2 (𝓞 F) F :=
  (globalPoints (𝓞 F) F).comp (diagOne (A := F))

theorem ratCentralHom_apply_entry (a : Fˣ) (i j : Fin 2) :
    ((ratCentralHom F a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then algebraMap F (AdeleRing (𝓞 F) F) a else 0 := by
  change algebraMap F (AdeleRing (𝓞 F) F) ((Matrix.scalar (Fin 2) (a : F)) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem diagHom_apply_entry (a : Fˣ) (i j : Fin 2) :
    ((diagHom F a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (if i = 0 then algebraMap F (AdeleRing (𝓞 F) F) a else 1) else 0 := by
  change algebraMap F (AdeleRing (𝓞 F) F) ((diagOne a : Matrix (Fin 2) (Fin 2) F) i j) = _
  rw [diagOne_coe_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem ratCentralHom_comm (a : Fˣ) (g : AdelicGL2 (𝓞 F) F) : ratCentralHom F a * g = g * ratCentralHom F a := by
  refine Units.ext ?_
  change (Matrix.scalar (Fin 2) ((a : Fˣ) : F)).map (algebraMap F (AdeleRing (𝓞 F) F)) *
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * (Matrix.scalar (Fin 2) ((a : Fˣ) : F)).map (algebraMap F (AdeleRing (𝓞 F) F))
  have : (Matrix.scalar (Fin 2) ((a : Fˣ) : F)).map (algebraMap F (AdeleRing (𝓞 F) F)) =
      Matrix.scalar (Fin 2) (algebraMap F (AdeleRing (𝓞 F) F) a) := by
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [this]
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem unipotentGL2_mul_diagHom (a : Fˣ) (y : AdeleRing (𝓞 F) F) :
    unipotentGL2 y * diagHom F a = diagHom F a * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ((a⁻¹ : Fˣ) : F) * y) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, diagHom_apply_entry, diagHom_apply_entry, diagHom_apply_entry,
    diagHom_apply_entry, unipotentGL2_coe]
  have hinv : algebraMap F (AdeleRing (𝓞 F) F) (a : F) * algebraMap F (AdeleRing (𝓞 F) F) ((a : F)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ a.ne_zero, map_one]
  fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hinv]

theorem diagHom_mul_unipotentGL2 (a : Fˣ) (u : AdeleRing (𝓞 F) F) :
    diagHom F a * unipotentGL2 u = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u) * diagHom F a := by
  rw [unipotentGL2_mul_diagHom, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ a.ne_zero,
    map_one, one_mul]

theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 F) F) := by
  intro x y h
  apply Units.ext
  ext i j
  have := congrArg (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) h
  simp only [globalPoints_apply] at this
  exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F)) this

def leftStabilizer (f : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {x | ∀ g, f (x * g) = f g}
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc, ha, hb]
  one_mem' := by
    intro g
    rw [one_mul]
  inv_mem' := by
    intro a ha g
    rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

abbrev scalarUnipotent : Subgroup (GL (Fin 2) F) :=
  (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom).range ⊔ (unipotentGL2Hom (R := F)).range

abbrev ratP : Subgroup (AdelicGL2 (𝓞 F) F) :=
  rationalCentre F ⊔ ((globalPoints (𝓞 F) F).comp (unipotentGL2Hom (R := F))).range

theorem ratP_eq_map : ratP F = (scalarUnipotent F).map (globalPoints (𝓞 F) F) := by
  rw [Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp]

omit [NumberField F] in
theorem scalarUnipotent_le_borel : scalarUnipotent F ≤ borelSubgroup F := by
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    show (Matrix.scalar (Fin 2) ((a : Fˣ) : F)) 1 0 = 0
    simp
  · rintro _ ⟨t, rfl⟩
    exact unipotentGL2_mem_borelSubgroup _

theorem ratP_le_borelMap : ratP F ≤ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  rw [ratP_eq_map]
  exact Subgroup.map_mono (scalarUnipotent_le_borel F)

theorem diagHom_mem_borelMap (a : Fˣ) : diagHom F a ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  refine ⟨diagOne a, ?_, rfl⟩
  show (diagOne a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]; simp

theorem existsUnique_repr (γ : (borelSubgroup F).map (globalPoints (𝓞 F) F)) :
    ∃! a : Fˣ, (((⟨diagHom F a, diagHom_mem_borelMap F a⟩ : (borelSubgroup F).map (globalPoints (𝓞 F) F))⁻¹ * γ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) ∈ ratP F := by
  obtain ⟨b, hb, hbγ⟩ := γ.2
  have h := existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup F b hb
  refine (existsUnique_congr fun a => ?_).mp h
  rw [ratP_eq_map]
  have hval : (((⟨diagHom F a, diagHom_mem_borelMap F a⟩ : (borelSubgroup F).map (globalPoints (𝓞 F) F))⁻¹ * γ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) =
      globalPoints (𝓞 F) F ((diagOne a)⁻¹ * b) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hbγ]
    rfl
  rw [hval, Subgroup.mem_map_iff_mem (globalPoints_injective F)]

theorem main
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F))
    (k : AdelicGL2 (𝓞 F) F → ℂ) (hk : Measurable k)
    (hkH : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k (h * g) = k g)
    (hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    Integrable (fun q : RationalCentreUnipotentQuotient F => k q.out) (rationalCentreUnipotentQuotientMeasure F) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q : RationalCentreUnipotentQuotient F, k q.out ∂(rationalCentreUnipotentQuotientMeasure F) := by

  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.symm.countable_iff.mp inferInstance
  haveI : Countable Fˣ := Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set Bm : Subgroup (AdelicGL2 (𝓞 F) F) := (borelSubgroup F).map (globalPoints (𝓞 F) F) with hBm
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F).1
  haveI := (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F).2
  haveI := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).1
  haveI := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).2

  obtain ⟨hPle, hPcount, hT₁m, hT₁fd, hT₁int⟩ := isFundamentalDomain_boxSheet_rationalCentreUnipotent F
  obtain ⟨hBle, hBcount, hT₂m, hT₂fd, hT₂int⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  haveI : Countable (ratP F) := hPcount
  haveI : Countable Bm := hBcount

  have hδ : ∀ a : Fˣ, globalPoints (𝓞 F) F (diagOne a) = diagHom F a := fun a => rfl
  set K₃ : AdelicGL2 (𝓞 F) F → ℂ := fun g => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) with hK₃
  have hK₃m : Measurable K₃ :=
    measurable_tsum_complex fun a => hk.comp (measurable_const_mul (globalPoints (𝓞 F) F (diagOne a)))

  have hkδn : ∀ (a : Fˣ) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      k (diagHom F a * (unipotentGL2 u * g)) = k (diagHom F a * g) := by
    intro a u g
    rw [← mul_assoc, diagHom_mul_unipotentGL2, mul_assoc]
    exact hkH (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u))
      (Subgroup.mem_sup_right ⟨Multiplicative.ofAdd (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u), rfl⟩) (diagHom F a * g)
  have hkδz : ∀ (a z : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      k (diagHom F a * (ratCentralHom F z * g)) = k (diagHom F a * g) := by
    intro a z g
    rw [← mul_assoc, ← ratCentralHom_comm, mul_assoc]
    exact hkH (ratCentralHom F z) (Subgroup.mem_sup_left ⟨z, rfl⟩) (diagHom F a * g)
  have hK₃inv : rationalTorusUnipotent F ≤ leftStabilizer F K₃ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨z, rfl⟩ g
      show ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (_ * g)) = ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g)
      exact tsum_congr fun a => hkδz a z g
    · rintro _ ⟨a₀, rfl⟩ g
      show ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (diagHom F a₀ * g)) =
        ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g)
      have h1 : ∀ a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (diagHom F a₀ * g)) = k (diagHom F (a * a₀) * g) := by
        intro a; rw [hδ, ← mul_assoc, ← map_mul]
      simp_rw [h1]
      exact (Equiv.mulRight a₀).tsum_eq (fun b => k (diagHom F b * g))
    · rintro _ ⟨t, rfl⟩ g
      show ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (unipotentGL2 t.toAdd * g)) =
        ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g)
      exact tsum_congr fun a => hkδn a _ g
  have hK₃H₂ : ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, K₃ (h * g) = K₃ g :=
    fun h hh g => hK₃inv hh g
  have hK₃B : ∀ γ ∈ Bm, ∀ g : AdelicGL2 (𝓞 F) F, K₃ (γ * g) = K₃ g := fun γ hγ g => hK₃H₂ γ (hBle hγ) g

  set R : Fˣ → Bm := fun a => ⟨diagHom F a, diagHom_mem_borelMap F a⟩ with hR_def
  have hR : ∀ γ : Bm, ∃! a : Fˣ, (((R a)⁻¹ * γ : Bm) : AdelicGL2 (𝓞 F) F) ∈ ratP F := existsUnique_repr F
  have hFD₂ : IsFundamentalDomain (ratP F) (⋃ a : Fˣ, ((R a : AdelicGL2 (𝓞 F) F)⁻¹) • 𝓕B) μ :=
    MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μ Bm (ratP F) (ratP_le_borelMap F)
      𝓕B h𝓕B R hR
  obtain ⟨hC1l, hC1b⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives μ Bm
      (ratP F) (ratP_le_borelMap F) 𝓕B h𝓕B R hR
  have hRinv : ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F), ((R a : AdelicGL2 (𝓞 F) F))⁻¹ • g = diagHom F a⁻¹ * g := by
    intro a g
    rw [smul_eq_mul, hR_def]
    simp only [map_inv]
  have hreidx_e : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' a : Fˣ, ‖k (((R a : AdelicGL2 (𝓞 F) F))⁻¹ • g)‖ₑ) = ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ := by
    intro g
    simp_rw [hRinv, hδ]
    exact (Equiv.inv Fˣ).tsum_eq (fun a => ‖k (diagHom F a * g)‖ₑ)
  have hreidx : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' a : Fˣ, k (((R a : AdelicGL2 (𝓞 F) F))⁻¹ • g)) = K₃ g := by
    intro g
    simp_rw [hRinv, hK₃, hδ]
    exact (Equiv.inv Fˣ).tsum_eq (fun a => k (diagHom F a * g))
  have hnormfin : ∫⁻ g in ⋃ a : Fˣ, ((R a : AdelicGL2 (𝓞 F) F)⁻¹) • 𝓕B, ‖k g‖ₑ ∂μ < ∞ := by
    rw [hC1l _ hk.enorm]
    simp_rw [hreidx_e]
    exact hfin
  obtain ⟨-, -, hA⟩ := hC1b k hk.aestronglyMeasurable (by simp_rw [hreidx_e]; exact hfin)
  simp_rw [hreidx] at hA

  have hkP : ∀ γ ∈ ratP F, ∀ g : AdelicGL2 (𝓞 F) F, k (γ * g) = k g := fun γ hγ g => hkH γ (hPle hγ) g
  obtain ⟨-, hIB, hB⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ
      (rationalCentreUnipotent F) (isClosed_rationalCentreUnipotent F) (rationalCentreUnipotentHaar F)
      (ratP F) hPle k hk hkP _ hFD₂ _ hT₁fd hnormfin
  have hmass₁ : rationalCentreUnipotentHaar F
      ((fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F) = 1 := by
    have h := hT₁int (fun _ => 1) measurable_const
    rw [setLIntegral_one, setLIntegral_one, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne] at h
    exact h
  have hfib₁ : ∀ q : RationalCentreUnipotentQuotient F,
      (∫ x in (fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F,
        k ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalCentreUnipotentHaar F)) = k q.out := by
    intro q
    have : (fun x : rationalCentreUnipotent F => k ((x : AdelicGL2 (𝓞 F) F) * q.out)) = fun _ => k q.out :=
      funext fun x => hkH x x.2 _
    rw [this, setIntegral_const]
    simp [Measure.real, hmass₁]
  simp_rw [hfib₁] at hIB hB

  have hK₃fin : ∫⁻ g in 𝓕B, ‖K₃ g‖ₑ ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun g => enorm_tsum_le _) hfin
  obtain ⟨-, hIC, hC⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ
      (rationalTorusUnipotent F) (isClosed_rationalTorusUnipotent F) (rationalTorusUnipotentHaar F)
      Bm hBle K₃ hK₃m hK₃B 𝓕B h𝓕B _ hT₂fd hK₃fin
  have hmass₂ : rationalTorusUnipotentHaar F
      ((fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F) = 1 := by
    have h := hT₂int (fun _ => 1) measurable_const
    rw [setLIntegral_one, setLIntegral_one, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne] at h
    exact h
  have hfib₂ : ∀ q : RationalTorusUnipotentQuotient F,
      (∫ x in (fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F,
        K₃ ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F)) = K₃ q.out := by
    intro q
    have : (fun x : rationalTorusUnipotent F => K₃ ((x : AdelicGL2 (𝓞 F) F) * q.out)) = fun _ => K₃ q.out :=
      funext fun x => hK₃H₂ x x.2 _
    rw [this, setIntegral_const]
    simp [Measure.real, hmass₂]
  simp_rw [hfib₂] at hIC hC

  refine ⟨hIB, hIC, hC.symm, ?_⟩
  rw [hA.symm.trans hB]
  rfl

end TorusUnfoldC9C

end AutomorphicForm

end

theorem solution
    (F : Type) [Field F] [NumberField F]
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F))
    (k : AdelicGL2 (𝓞 F) F → ℂ) (hk : Measurable k)
    (hkH : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k (h * g) = k g)
    (hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    Integrable (fun q : RationalCentreUnipotentQuotient F => k q.out) (rationalCentreUnipotentQuotientMeasure F) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q : RationalCentreUnipotentQuotient F, k q.out ∂(rationalCentreUnipotentQuotientMeasure F) :=
  AutomorphicForm.TorusUnfoldC9C.main F 𝓕B h𝓕B k hk hkH hfin

end S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
end P2MW
export P2MW.S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient (solution)
