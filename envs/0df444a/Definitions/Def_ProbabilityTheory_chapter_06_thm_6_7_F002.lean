-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_06_thm_6_7_F002
-- name    : ProbabilityTheory_chapter_06_thm_6_7_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T21:30:45.596421+00:00
-- url     : https://prove2.me/theorems/ec716748-0773-4f44-819d-bd20f4d2dcb5
-- title:
--   Chapter 6, thm_6_7: supporting Lean bundle F002
-- statement:
--   Supporting Lean declarations for Chapter 6, source module `thm_6_7`: `thm_6_7_complex`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_7.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_6_F000
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory

namespace Thm67Support

private lemma realCoe_textbookIntegrable_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  unfold textbookIntegrable;
  constructor;
  · intro h_integrable
    have h_integrable_pos : MeasureTheory.Integrable (fun ω => max (f ω) 0) μ := by
      refine' ⟨ hfm.aemeasurable.max aemeasurable_const |> fun h => h.aestronglyMeasurable, _ ⟩;
      convert h_integrable.1 using 1;
      simp +decide [ hasFiniteIntegral_iff_norm, Def65Support.posLIntegral ];
      simp +decide [Def65Support.posPart, abs_of_nonneg]
    have h_integrable_neg : MeasureTheory.Integrable (fun ω => max (-f ω) 0) μ := by
      refine' ⟨ _, _ ⟩;
      · exact Measurable.aestronglyMeasurable ( by measurability );
      · convert h_integrable.2 using 1;
        simp +decide [ hasFiniteIntegral_iff_norm, Def65Support.negLIntegral ];
        simp +decide [Def65Support.negPart, abs_of_nonneg];
    convert h_integrable_pos.sub h_integrable_neg using 1 ; ext ω ; simp +decide [ max_def ] ; split_ifs <;> linarith;
  · intro hf;
    constructor;
    · refine' lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun ω => _ ) _;
      exact fun ω => ENNReal.ofReal |f ω|;
      · unfold Def65Support.posPart;
        cases abs_cases ( f ω ) <;> simp +decide [ * ];
        rw [ ENNReal.ofReal_eq_zero.mpr ( by linarith ) ] ; norm_num;
      · convert hf.abs.lintegral_lt_top using 1;
    · refine' MeasureTheory.Integrable.lintegral_lt_top _;
      convert hf.neg using 1
      rfl

private lemma def66Real_textbookIntegrable_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfm : Measurable f) :
    Def66RealSupport.textbookIntegrable μ (fun ω => (f ω : EReal)) ↔ Integrable f μ := by
  convert realCoe_textbookIntegrable_iff hfm using 1
  rfl

private lemma textbookIntegral_realCoe_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    textbookIntegral μ (fun ω => (f ω : EReal)) = some ((∫ ω, f ω ∂μ : ℝ) : EReal) := by
  unfold textbookIntegral
  simp +decide [Def65Support.posLIntegral, Def65Support.negLIntegral]
  split_ifs with h
  · exfalso
    have hfinite : Def65Support.negLIntegral μ (fun ω => (f ω : EReal)) ≠ ⊤ := by
      convert hf.neg.lintegral_lt_top.ne using 1
      rfl
    exact hfinite h.2
  · have h_pos_neg : ∫⁻ ω, Def65Support.posPart (fun ω => (f ω : EReal)) ω ∂μ = ENNReal.ofReal (∫ ω, max (f ω) 0 ∂μ) ∧ ∫⁻ ω, Def65Support.negPart (fun ω => (f ω : EReal)) ω ∂μ = ENNReal.ofReal (∫ ω, max (-f ω) 0 ∂μ) := by
      constructor <;> rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      any_goals filter_upwards [ ] using fun _ => le_max_right _ _;
      · congr with ω ; simp +decide [ Def65Support.posPart ];
      · exact hf.pos_part;
      · congr with ω ; simp +decide [ Def65Support.negPart ];
      · exact hf.neg.pos_part;
    have hpos : 0 ≤ ∫ ω, max (f ω) 0 ∂μ := integral_nonneg (fun ω => le_max_right _ _)
    have hneg : 0 ≤ ∫ ω, max (-f ω) 0 ∂μ := integral_nonneg (fun ω => le_max_right _ _)
    have hp : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ).toReal = ∫ ω, max (f ω) 0 ∂μ := by
      simpa [Def65Support.posPart, ENNReal.toReal_ofReal hpos] using
        congrArg ENNReal.toReal h_pos_neg.1
    have hn : (∫⁻ ω, ENNReal.ofReal (-f ω) ∂μ).toReal = ∫ ω, max (-f ω) 0 ∂μ := by
      simpa [Def65Support.negPart, ENNReal.toReal_ofReal hneg] using
        congrArg ENNReal.toReal h_pos_neg.2
    simp only [h_pos_neg.1, h_pos_neg.2]
    norm_cast
    rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, hp, hn]
    simp [ENNReal.ofReal, Real.toNNReal, hpos, hneg, EReal.coe_nnreal_eq_coe_real]

private lemma def66Real_textbookValue_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) :
    Def66RealSupport.textbookValue μ (fun ω => (f ω : EReal)) = ∫ ω, f ω ∂μ := by
  have := @Thm67Support.textbookIntegral_realCoe_eq_some_integral Ω _ μ f hf;
  unfold textbookIntegral at this;
  split_ifs at this ; simp_all +decide [ Def66RealSupport.textbookValue ];
  convert congr_arg EReal.toReal this using 1
  · rfl
  · rfl

private lemma complexTextbookIntegral_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) (hZ : Integrable Z μ) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  rw [ complexTextbookIntegral ];
  split_ifs with hZ';
  · rw [ def66Real_textbookValue_eq_integral, def66Real_textbookValue_eq_integral ];
    · rw [ ← integral_re_add_im hZ ] ;
      norm_num [ mul_comm ];
    · exact hZ.im;
    · exact hZ.re;
  · contrapose! hZ';
    exact ⟨ def66Real_textbookIntegrable_iff ( Complex.measurable_re.comp hZm ) |>.2 hZ.re, def66Real_textbookIntegrable_iff ( Complex.measurable_im.comp hZm ) |>.2 hZ.im ⟩

end Thm67Support

/--
## Theorem 6.7 for the complex-valued textbook integral.

If `Z` and `W` are measurable and textbook-integrable complex-valued functions, then:

* their pointwise sum `fun ω => Z ω + W ω` is textbook-integrable;
* the textbook integral of the sum is the sum of the textbook integrals;
* for every scalar `α : ℂ`, the scalar multiple `fun ω => α * Z ω` is textbook-integrable;
* the textbook integral of the scalar multiple is `α` times the textbook integral of `Z`.

The equalities are stated using `Option.map₂` and `Option.map`, since
`complexTextbookIntegral` returns an optional value.
-/
private theorem complexTextbookIntegrable_iff_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Z : Ω → ℂ} (hZm : Measurable Z) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ := by
  refine' ⟨ _, fun h => _ ⟩;
  · intro hZ_integrable
    obtain ⟨hZ_re, hZ_im⟩ := hZ_integrable
    have hZ_re_integrable : Integrable (fun ω => (Z ω).re) μ := by
      convert Thm67Support.def66Real_textbookIntegrable_iff _ |>.1 hZ_re using 1;
      exact Complex.measurable_re.comp hZm
    have hZ_im_integrable : Integrable (fun ω => (Z ω).im) μ := by
      exact Thm67Support.def66Real_textbookIntegrable_iff ( Complex.measurable_im.comp hZm ) |>.1 hZ_im;
    convert hZ_re_integrable.ofReal.add ( hZ_im_integrable.ofReal.smul_const Complex.I ) using 1 ;
    rfl
    ext; simp  [Complex.ext_iff]
    any_goals exact ℝ
    all_goals first | infer_instance | simp +decide
  · constructor;
    · convert Thm67Support.def66Real_textbookIntegrable_iff ( Complex.measurable_re.comp hZm ) |>.2 ( h.re ) using 1;
      rfl
    · convert Thm67Support.def66Real_textbookIntegrable_iff ( show Measurable fun ω => ( Z ω |> Complex.im ) from Complex.measurable_im.comp hZm ) |>.2 ( h.im ) using 1

private theorem thm_6_7_complex_source_local {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℂ} (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : complexTextbookIntegrable μ Z) (hW : complexTextbookIntegrable μ W) (α : ℂ) :
    complexTextbookIntegrable μ (fun ω => Z ω + W ω) ∧
      complexTextbookIntegral μ (fun ω => Z ω + W ω) =
        Option.map₂ (fun z w => z + w) (complexTextbookIntegral μ Z) (complexTextbookIntegral μ W) ∧
      complexTextbookIntegrable μ (fun ω => α * Z ω) ∧
      complexTextbookIntegral μ (fun ω => α * Z ω) =
        Option.map (fun z => α * z) (complexTextbookIntegral μ Z) := by
  refine' ⟨ _, _, _, _ ⟩;
  · convert complexTextbookIntegrable_iff_integrable ( show Measurable fun ω => Z ω + W ω from hZm.add hWm ) |>.2 ( Integrable.add ( complexTextbookIntegrable_iff_integrable hZm |>.1 hZ ) ( complexTextbookIntegrable_iff_integrable hWm |>.1 hW ) ) using 1;
  · have hZi : Integrable Z μ := (complexTextbookIntegrable_iff_integrable hZm).1 hZ
    have hWi : Integrable W μ := (complexTextbookIntegrable_iff_integrable hWm).1 hW
    have hsum : Integrable (fun ω => Z ω + W ω) μ := hZi.add hWi
    change complexTextbookIntegral μ (Z + W) = _
    rw [Thm67Support.complexTextbookIntegral_eq_some_integral (hZm.add hWm) hsum,
      Thm67Support.complexTextbookIntegral_eq_some_integral hZm hZi,
      Thm67Support.complexTextbookIntegral_eq_some_integral hWm hWi]
    simp [MeasureTheory.integral_add hZi hWi]
  · convert ( complexTextbookIntegrable_iff_integrable ( show Measurable fun ω => α * Z ω from measurable_const.mul hZm ) ) |>.2 ( MeasureTheory.Integrable.const_mul ( show MeasureTheory.Integrable Z μ from ?_ ) α ) using 1;
    exact complexTextbookIntegrable_iff_integrable hZm |>.1 hZ;
  · -- By definition of complexTextbookIntegral, we know that
    have h_integrable : Integrable (fun ω => α * Z ω) μ := by
      exact MeasureTheory.Integrable.const_mul ( by simpa using ( complexTextbookIntegrable_iff_integrable hZm ).mp hZ ) α;
    rw [ Thm67Support.complexTextbookIntegral_eq_some_integral, Thm67Support.complexTextbookIntegral_eq_some_integral ];
    · simp [ MeasureTheory.integral_const_mul ];
    · exact hZm;
    · exact (complexTextbookIntegrable_iff_integrable hZm).mp hZ;
    · exact measurable_const.mul hZm;
    · exact h_integrable

theorem thm_6_7_complex' {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Z W : Ω → ℂ} (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : complexTextbookIntegrable μ Z) (hW : complexTextbookIntegrable μ W) (α : ℂ) :
    complexTextbookIntegrable μ (fun ω => Z ω + W ω) ∧
      complexTextbookIntegral μ (fun ω => Z ω + W ω) =
        Option.map₂ (fun z w => z + w) (complexTextbookIntegral μ Z) (complexTextbookIntegral μ W) ∧
      complexTextbookIntegrable μ (fun ω => α * Z ω) ∧
      complexTextbookIntegral μ (fun ω => α * Z ω) =
        Option.map (fun z => α * z) (complexTextbookIntegral μ Z) := by
  exact thm_6_7_complex_source_local μ hZm hWm hZ hW α


