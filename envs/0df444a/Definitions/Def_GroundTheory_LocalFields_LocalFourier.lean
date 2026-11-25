-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalFourier
-- name    : GroundTheory_LocalFields_LocalFourier
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:48.229256+00:00
-- url     : https://prove2.me/theorems/046cbce9-4cc1-4a78-a88c-bfcf3ef68dc9
-- title:
--   Local Fourier
-- statement:
--   Definitions and structural lemmas for Local Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourier.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_continuous_modulus
import Theorems.Thm_GroundTheory_LocalField_integrable_mul_char_of_mem_schwartzBruhat
import Theorems.Thm_GroundTheory_LocalField_lintegral_comp_mul_left
import Theorems.Thm_GroundTheory_LocalField_localFourier_mem_schwartzBruhat
import Theorems.Thm_GroundTheory_LocalField_measurable_modulus
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_mul
import Theorems.Thm_GroundTheory_LocalField_modulus_ne_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard_nnreal
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section SelfDual
variable [MeasurableSpace K] [BorelSpace K]
def selfDualMeasure (ψ : AddChar K Circle) : Measure K :=
  ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2)) • haarIntegers K
omit [MeasurableSpace K] [BorelSpace K] in
theorem selfDualMeasure_coeff_ne_zero (ψ : AddChar K Circle) :
    ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2)) ≠ 0 :=
  (NNReal.rpow_pos (zero_lt_one.trans one_lt_residueCard_nnreal)).ne'
instance (ψ : AddChar K Circle) : (selfDualMeasure ψ).IsAddHaarMeasure := by
  unfold selfDualMeasure
  exact IsAddHaarMeasure.nnreal_smul (haarIntegers K) (selfDualMeasure_coeff_ne_zero ψ)
variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
def fourierSB (μ : Measure K) [μ.IsAddHaarMeasure] : schwartzBruhat K →ₗ[ℂ] schwartzBruhat K where
  toFun f := ⟨localFourier μ ψ f, localFourier_mem_schwartzBruhat μ hψ hψ1 f.2⟩
  map_add' f g := Subtype.ext <| funext fun y => by
    show ∫ x, ((f : K → ℂ) x + (g : K → ℂ) x) * (ψ (x * y) : ℂ) ∂μ =
      ∫ x, (f : K → ℂ) x * (ψ (x * y) : ℂ) ∂μ + ∫ x, (g : K → ℂ) x * (ψ (x * y) : ℂ) ∂μ
    simp only [add_mul]
    exact integral_add (integrable_mul_char_of_mem_schwartzBruhat μ hψ f.2 y)
      (integrable_mul_char_of_mem_schwartzBruhat μ hψ g.2 y)
  map_smul' c f := Subtype.ext <| funext fun y => by
    show ∫ x, (c * (f : K → ℂ) x) * (ψ (x * y) : ℂ) ∂μ = c * ∫ x, (f : K → ℂ) x * (ψ (x * y) : ℂ) ∂μ
    simp only [mul_assoc]
    exact integral_const_mul c _
end SelfDual
section Multiplicative
variable [MeasurableSpace K] [BorelSpace K]
theorem measurableEmbedding_units_val : MeasurableEmbedding (Units.val : Kˣ → K) where
  injective := Units.val_injective
  measurable := comap_measurable _
  measurableSet_image' := by
    rintro _ ⟨t, ht, rfl⟩
    have : (Units.val : Kˣ → K) '' (Units.val ⁻¹' t) = t ∩ {0}ᶜ := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, u.ne_zero⟩
      · rintro ⟨hx, hx0⟩
        exact ⟨Units.mk0 x hx0, hx, rfl⟩
    rw [this]
    exact ht.inter (measurableSet_singleton 0).compl
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K]
  [BorelSpace K] in
theorem range_units_val : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact u.ne_zero
  · intro hx
    exact ⟨Units.mk0 x hx, rfl⟩
omit [MeasurableSpace K] [BorelSpace K] in

theorem isOpenEmbedding_units_val : IsOpenEmbedding (Units.val : Kˣ → K) :=
  ⟨Units.isEmbedding_val₀, by rw [range_units_val]; exact isOpen_compl_singleton⟩
variable (K) in

def multHaarConst : ℝ≥0∞ := (1 - ((residueCard K : ℝ≥0∞))⁻¹)⁻¹
omit [MeasurableSpace K] [BorelSpace K] in
theorem one_sub_inv_residueCard_ne_zero : (1 : ℝ≥0∞) - ((residueCard K : ℝ≥0∞))⁻¹ ≠ 0 :=
  (tsub_pos_of_lt (ENNReal.inv_lt_one.mpr (by exact_mod_cast one_lt_residueCard))).ne'
omit [MeasurableSpace K] [BorelSpace K] in
theorem multHaarConst_ne_zero : multHaarConst K ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
omit [MeasurableSpace K] [BorelSpace K] in
theorem multHaarConst_ne_top : multHaarConst K ≠ ∞ :=
  ENNReal.inv_ne_top.mpr one_sub_inv_residueCard_ne_zero
variable (K) in

def multHaar : Measure Kˣ :=
  Measure.comap Units.val
    (multHaarConst K • (haarIntegers K).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹)
theorem measurable_modulus_inv : Measurable fun x : K => ((modulus x : ℝ≥0∞))⁻¹ :=
  measurable_modulus.coe_nnreal_ennreal.inv
theorem multHaar_apply (s : Set Kˣ) :
    multHaar K s =
      multHaarConst K * ∫⁻ x in Units.val '' s, ((modulus x : ℝ≥0∞))⁻¹ ∂(haarIntegers K) := by
  rw [multHaar, measurableEmbedding_units_val.comap_apply, Measure.smul_apply, withDensity_apply',
    smul_eq_mul]
instance : (multHaar K).IsMulLeftInvariant := by
  constructor
  intro a
  ext s hs
  have hmeas : Measurable fun u : Kˣ => a * u := by
    rw [← measurableEmbedding_units_val.measurable_comp_iff]
    exact (measurable_const_mul (a : K)).comp measurableEmbedding_units_val.measurable
  rw [Measure.map_apply hmeas hs, multHaar_apply, multHaar_apply]
  congr 1
  have himg : Units.val '' ((fun u => a * u) ⁻¹' s) =
      (fun x : K => (a : K) * x) ⁻¹' (Units.val '' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨a * u, hu, by simp⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨a⁻¹ * v, by simpa using hv, ?_⟩
      simp only [Units.val_mul, hvx]
      rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [himg]
  have hS : MeasurableSet (Units.val '' s) :=
    measurableEmbedding_units_val.measurableSet_image.mpr hs
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  have hm0 : (modulus (a : K) : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero ha0)
  have hmt : (modulus (a : K) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  rw [← lintegral_indicator (hS.preimage (measurable_const_mul _)), ← lintegral_indicator hS]
  have hpt : ∀ x, ((fun x : K => (a : K) * x) ⁻¹' (Units.val '' s)).indicator
      (fun x => ((modulus x : ℝ≥0∞))⁻¹) x =
      (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((a : K) * x) *
        (modulus (a : K) : ℝ≥0∞) := by
    intro x
    by_cases hx : (a : K) * x ∈ Units.val '' s
    · rw [Set.indicator_of_mem (show x ∈ (fun x : K => (a : K) * x) ⁻¹' (Units.val '' s) from hx),
        Set.indicator_of_mem hx, modulus_mul, ENNReal.coe_mul,
        ENNReal.mul_inv (Or.inl hm0) (Or.inl hmt), mul_comm, ← mul_assoc,
        ENNReal.mul_inv_cancel hm0 hmt, one_mul]
    · rw [Set.indicator_of_notMem
        (show x ∉ (fun x : K => (a : K) * x) ⁻¹' (Units.val '' s) from hx),
        Set.indicator_of_notMem hx, zero_mul]
  calc ∫⁻ x, ((fun x : K => (a : K) * x) ⁻¹' (Units.val '' s)).indicator
        (fun x => ((modulus x : ℝ≥0∞))⁻¹) x ∂(haarIntegers K)
      = ∫⁻ x, (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) ((a : K) * x) *
          (modulus (a : K) : ℝ≥0∞) ∂(haarIntegers K) := lintegral_congr hpt
    _ = ((modulus (a : K) : ℝ≥0∞))⁻¹ * ∫⁻ y, (Units.val '' s).indicator
          (fun y => ((modulus y : ℝ≥0∞))⁻¹) y * (modulus (a : K) : ℝ≥0∞) ∂(haarIntegers K) :=
        lintegral_comp_mul_left (haarIntegers K) ha0
          (fun y => (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) y *
            (modulus (a : K) : ℝ≥0∞))
    _ = ∫⁻ y, (Units.val '' s).indicator (fun y => ((modulus y : ℝ≥0∞))⁻¹) y
          ∂(haarIntegers K) := by
        rw [lintegral_mul_const' _ _ hmt, mul_comm _ (modulus (a : K) : ℝ≥0∞), ← mul_assoc,
          ENNReal.inv_mul_cancel hm0 hmt, one_mul]
instance : IsFiniteMeasureOnCompacts (multHaar K) := by
  constructor
  intro C hC
  rw [multHaar_apply]
  refine ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr multHaarConst_ne_top) ?_
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  have hC' : IsCompact (Units.val '' C) := hC.image Units.continuous_val
  obtain ⟨u, -, hmin⟩ := hC.exists_isMinOn hne
    (continuous_modulus.comp Units.continuous_val).continuousOn
  have hδ : modulus (u : K) ≠ 0 := modulus_ne_zero u.ne_zero
  calc ∫⁻ x in Units.val '' C, ((modulus x : ℝ≥0∞))⁻¹ ∂(haarIntegers K)
      ≤ ∫⁻ x in Units.val '' C, ((modulus (u : K) : ℝ≥0∞))⁻¹ ∂(haarIntegers K) := by
        refine setLIntegral_mono' hC'.isClosed.measurableSet ?_
        rintro _ ⟨v, hv, rfl⟩
        exact ENNReal.inv_le_inv.mpr (ENNReal.coe_le_coe.mpr (hmin hv))
    _ = ((modulus (u : K) : ℝ≥0∞))⁻¹ * haarIntegers K (Units.val '' C) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr
        (pos_iff_ne_zero.mpr hδ))) hC'.measure_lt_top
instance : IsOpenPosMeasure (multHaar K) := by
  constructor
  intro U hU hne
  rw [multHaar_apply]
  refine mul_ne_zero multHaarConst_ne_zero ?_
  have hU' : IsOpen (Units.val '' U) := isOpenEmbedding_units_val.isOpenMap U hU
  have hpos : 0 < haarIntegers K (Units.val '' U) := hU'.measure_pos _ (hne.image _)
  apply ne_of_gt
  rw [lintegral_pos_iff_support measurable_modulus_inv]
  have : Function.support (fun x : K => ((modulus x : ℝ≥0∞))⁻¹) = Set.univ := by
    ext x
    simp [Function.mem_support]
  rw [this, Measure.restrict_apply_univ]
  exact hpos
instance : (multHaar K).IsHaarMeasure where
end Multiplicative
end GroundTheory.LocalField


