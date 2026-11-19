-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharTotal_F002
-- name    : LevyStochCalc_Probability_CharTotal_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:33:01.563506+00:00
-- url     : https://prove2.me/theorems/9d558756-46d1-48e2-bb46-db92c54ee8eb
-- title:
--   Source declarations: LevyStochCalc.Probability.CharTotal
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CharTotal. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CharTotal_F000
import Definitions.Def_LevyStochCalc_Probability_CharTotal_F001
import Definitions.Def_SourceProof_6eb041053be17661a552d578

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters separate `L¹` densities

An integrable function on an inner-product space that integrates to zero against every character
`v ↦ exp(i⟪v, w⟫)` vanishes almost everywhere. Splitting the function into positive and negative
parts turns the hypothesis into an equality of the characteristic functions of two finite
measures, which `MeasureTheory.Measure.ext_of_charFun` reads as an equality of the measures.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Probability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

/-! ### Totality in `L²` -/

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A character is bounded, hence in `L²` of a finite measure. -/
theorem memLp_char (μ : Measure V) [IsFiniteMeasure μ] (w : V) :
    MemLp (fun v => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)) 2 μ := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]
/-- The character at `w`, as an element of `L²`. -/
noncomputable def charLp (μ : Measure V) [IsFiniteMeasure μ] (w : V) : Lp ℂ 2 μ :=
  (memLp_char μ w).toLp _
/-- **The characters are total in `L²` of a finite measure.** -/
theorem topologicalClosure_span_charLp (μ : Measure V) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (charLp μ))).topologicalClosure = ⊤ := by
  have horth : (Submodule.span ℂ (Set.range (charLp μ)))ᗮ = ⊥ := by
   refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
   have hgint : Integrable (g : V → ℂ) μ := (Lp.memLp g).integrable one_le_two
   have hzero : ∀ w : V,
       ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (g : V → ℂ) v ∂μ = 0 := by
     intro w
     have hmem : charLp μ (-w) ∈ Submodule.span ℂ (Set.range (charLp μ)) :=
       Submodule.subset_span ⟨-w, rfl⟩
     have hinner : (inner ℂ (charLp μ (-w)) g : ℂ) = 0 :=
       (Submodule.mem_orthogonal _ _).mp hg _ hmem
     rw [L2.inner_def] at hinner
     refine Eq.trans (integral_congr_ae ?_) hinner
     filter_upwards [(memLp_char μ (-w)).coeFn_toLp] with v hv
     rw [show ((charLp μ (-w)) : V → ℂ) v = Complex.exp ((⟪v, -w⟫ : ℝ) * Complex.I) from hv,
       RCLike.inner_apply, char_neg v w]
     simp [mul_comm]
   exact (Lp.eq_zero_iff_ae_eq_zero).mpr (_root_.Prove2MeSourceProof.h_6eb041053be17661a552d578 hgint hzero)
  exact Submodule.topologicalClosure_eq_top_iff.mpr horth
/-! ### Transfer along a random vector -/

/-- **Characters of a random vector separate the variables it generates.** An integrable
`σ(X)`-measurable function integrating to zero against every character of `X` vanishes a.e.
Doob–Dynkin factors it through `X`, and the law of `X` is a finite measure on `V`. -/
theorem ae_eq_zero_of_integral_char_comp_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → V} (hX : Measurable X) {Z : Ω → ℂ}
    (hZ : Integrable Z P)
    (hZmeas : StronglyMeasurable[MeasurableSpace.comap X inferInstance] Z)
    (h : ∀ w : V, ∫ ω, Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) * Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by
  obtain ⟨g, hgm, hgeq⟩ := StronglyMeasurable.exists_eq_measurable_comp hZmeas
  haveI : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
  have hZg : Z = fun ω => g (X ω) := hgeq
  have hgint : Integrable g (P.map X) := by
    rw [integrable_map_measure hgm.aestronglyMeasurable hX.aemeasurable]
    simpa [Function.comp_def, ← hZg] using hZ
  have hcont : ∀ w : V, Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    fun w => Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  have hzero : ∀ w : V,
      ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v ∂(P.map X) = 0 := by
    intro w
    have hphi : AEStronglyMeasurable
        (fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v) (P.map X) :=
      AEStronglyMeasurable.mul ((hcont w).aestronglyMeasurable) hgm.aestronglyMeasurable
    rw [integral_map hX.aemeasurable hphi]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) (h w)
    simp [hZg]
  have hg0 := _root_.Prove2MeSourceProof.h_6eb041053be17661a552d578 hgint hzero
  have hset : MeasurableSet {v : V | g v = 0} :=
    hgm.measurable (measurableSet_singleton (0 : ℂ))
  have := (ae_map_iff hX.aemeasurable hset).mp hg0
  rw [hZg]
  exact this
/-! ### Set integrals over the σ-algebra generated by a random vector

The transfer lemma above needs `Z` to be measurable for `σ(X)`. When it is not — the case the
predictable representation property meets, where `Z` is measurable for a much larger σ-algebra —
the characters still say something: the complex measure `Z dP` pushed forward by `X` has
vanishing Fourier transform, so `Z` integrates to zero over every set `X` generates.
-/

section Comap

variable {Ω : Type*} [MeasurableSpace Ω]

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The characteristic function of a density-weighted law of `X`. -/
theorem charFun_map_withDensity_ofReal {P : Measure Ω} {X : Ω → V} (hX : Measurable X)
    {u : Ω → ℝ} (hu : AEMeasurable u P) (w : V) :
    charFun ((P.withDensity fun ω => ENNReal.ofReal (u ω)).map X) w
      = ∫ ω, Real.toNNReal (u ω) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) ∂P := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  rw [charFun_apply, integral_map hX.aemeasurable hcont.aestronglyMeasurable]
  exact integral_withDensity_eq_integral_smul₀ (f := fun ω => Real.toNNReal (u ω))
    hu.real_toNNReal _
/-- **The weighted laws agree.** A real integrable weight whose character integrals against `X`
vanish gives the same pushforward from its positive and its negative part. -/
theorem map_withDensity_eq_of_integral_char_comp_smul_eq_zero {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → V} (hX : Measurable X) {u : Ω → ℝ} (hu : Integrable u P)
    (h : ∀ w : V, ∫ ω, u ω • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) ∂P = 0) :
    (P.withDensity fun ω => ENNReal.ofReal (u ω)).map X
      = (P.withDensity fun ω => ENNReal.ofReal (-(u ω))).map X := by
  haveI : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (u ω)) :=
    isFiniteMeasure_withDensity_ofReal hu.2
  haveI : IsFiniteMeasure (P.withDensity fun ω => ENNReal.ofReal (-(u ω))) :=
    isFiniteMeasure_withDensity_ofReal (f := fun ω => -(u ω)) hu.neg.2
  haveI : IsFiniteMeasure ((P.withDensity fun ω => ENNReal.ofReal (u ω)).map X) :=
    Measure.isFiniteMeasure_map _ X
  haveI : IsFiniteMeasure ((P.withDensity fun ω => ENNReal.ofReal (-(u ω))).map X) :=
    Measure.isFiniteMeasure_map _ X
  refine Measure.ext_of_charFun (funext fun w => ?_)
  rw [charFun_map_withDensity_ofReal hX hu.aemeasurable w,
    charFun_map_withDensity_ofReal (u := fun ω => -(u ω)) hX hu.aemeasurable.neg w]
  have hsplit : ∀ ω : Ω,
      (Real.toNNReal (u ω) : ℝ) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I)
        = u ω • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I)
          + (Real.toNNReal (-(u ω)) : ℝ) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) := by
    intro ω
    rw [← add_smul]
    congr 1
    simp only [Real.coe_toNNReal']
    rcases le_total 0 (u ω) with hv | hv
    · rw [max_eq_left hv, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hv, max_eq_left (by linarith)]; ring
  have hsmulL : ∀ ω : Ω, (Real.toNNReal (u ω) : ℝ≥0) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I)
      = (Real.toNNReal (u ω) : ℝ) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) :=
    fun ω => NNReal.smul_def _ _
  have hsmulR : ∀ ω : Ω,
      (Real.toNNReal (-(u ω)) : ℝ≥0) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I)
        = (Real.toNNReal (-(u ω)) : ℝ) • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) :=
    fun ω => NNReal.smul_def _ _
  simp only [hsmulL, hsmulR, hsplit]
  rw [integral_add (integrable_charComp_smul hX hu w)
    (integrable_charComp_smul hX (integrable_toNNReal_coe (z := fun ω : Ω => -(u ω)) hu.neg) w),
    h w, zero_add]
end Comap

/-! ### Real and imaginary parts against a unimodular conjugation-closed family -/

omit [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
  [SecondCountableTopology V] in
/-- If a family of unimodular functions is closed under conjugation as `w ↦ -w`, then a function
integrating to zero against all of them does so with its real and imaginary parts separately. -/
theorem integral_smul_re_im_eq_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : V → α → ℂ} (hEmeas : ∀ w, AEStronglyMeasurable (E w) μ)
    (hEnorm : ∀ w a, ‖E w a‖ = 1) (hEconj : ∀ w a, E (-w) a = (starRingEnd ℂ) (E w a))
    {Z : α → ℂ} (hZ : Integrable Z μ) (h : ∀ w, ∫ a, E w a * Z a ∂μ = 0) :
    (∀ w, ∫ a, (Z a).re • E w a ∂μ = 0) ∧ (∀ w, ∫ a, (Z a).im • E w a ∂μ = 0) := by
  have hint : ∀ (w : V) {Y : α → ℂ}, Integrable Y μ → Integrable (fun a => E w a * Y a) μ := by
    intro w Y hY
    refine Integrable.mono' hY.norm ((hEmeas w).mul hY.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun a => ?_)
    simp [hEnorm w a]
  have hconj : ∀ w, ∫ a, E w a * (starRingEnd ℂ) (Z a) ∂μ = 0 := by
    intro w
    have hthis : (starRingEnd ℂ) (∫ a, E (-w) a * Z a ∂μ) = 0 := by rw [h (-w), map_zero]
    rw [← integral_conj] at hthis
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)) hthis
    rw [map_mul, hEconj w a]
    simp
  constructor
  · intro w
    have hsum : ∀ a : α, (Z a).re • E w a
        = (2 : ℂ)⁻¹ * (E w a * Z a + E w a * (starRingEnd ℂ) (Z a)) := by
      intro a
      have hc : Z a + (starRingEnd ℂ) (Z a) = ((2 * (Z a).re : ℝ) : ℂ) := Complex.add_conj _
      rw [Complex.real_smul, ← mul_add, hc]
      push_cast
      ring
    simp only [hsum]
    rw [integral_const_mul, integral_add (hint w hZ) (hint w (integrable_conj hZ)),
      h w, hconj w, add_zero, mul_zero]
  · intro w
    have hsum : ∀ a : α, (Z a).im • E w a
        = (2 * Complex.I)⁻¹ * (E w a * Z a - E w a * (starRingEnd ℂ) (Z a)) := by
      intro a
      have hc : Z a - (starRingEnd ℂ) (Z a) = ((2 * (Z a).im : ℝ) : ℂ) * Complex.I :=
        Complex.sub_conj _
      rw [Complex.real_smul, ← mul_sub, hc]
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      push_cast
      ring
    simp only [hsum]
    rw [integral_const_mul, integral_sub (hint w hZ) (hint w (integrable_conj hZ)),
      h w, hconj w, sub_zero, mul_zero]
/-! ### Vanishing set integrals over what a random vector generates -/

section SetIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Vanishing set integrals, real weight.** A real integrable weight whose character integrals
against `X` all vanish integrates to zero over every set of the σ-algebra `X` generates. -/
theorem setIntegral_eq_zero_of_integral_char_comp_smul_eq_zero {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → V} (hX : Measurable X) {u : Ω → ℝ} (hu : Integrable u P)
    (h : ∀ w : V, ∫ ω, u ω • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I) ∂P = 0)
    {s : Set Ω} (hs : MeasurableSet[MeasurableSpace.comap X inferInstance] s) :
    ∫ ω in s, u ω ∂P = 0 := by
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hmeas : MeasurableSet (X ⁻¹' B) := hX hB
  have hmap := map_withDensity_eq_of_integral_char_comp_smul_eq_zero hX hu h
  have hsplit : (P.withDensity fun ω => ENNReal.ofReal (u ω)) (X ⁻¹' B)
      = (P.withDensity fun ω => ENNReal.ofReal (-(u ω))) (X ⁻¹' B) := by
    rw [← Measure.map_apply hX hB, ← Measure.map_apply hX hB, hmap]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu.restrict,
    ← withDensity_apply _ hmeas, ← withDensity_apply _ hmeas, hsplit, sub_self]
end SetIntegral

end LevyStochCalc.Probability


