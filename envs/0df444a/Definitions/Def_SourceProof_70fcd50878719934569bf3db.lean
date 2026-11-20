-- Prove2me | Definitions.Def_SourceProof_70fcd50878719934569bf3db
-- name    : SourceProof_70fcd50878719934569bf3db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T23:44:46.246357+00:00
-- url     : https://prove2.me/theorems/b274409e-4ccc-4c81-b259-ef0389e32ebe
-- title:
--   LevyStochCalc source module: SourceProof_70fcd50878719934569bf3db
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_markSimple_adapted_within` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkApprox` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001
import Definitions.Def_SourceProof_010d482425efb705a03802af

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] in

theorem _root_.Prove2MeSourceProof.h_70fcd50878719934569bf3db
    {m0 : MeasurableSpace Ω} {P : @Measure Ω m0} [@IsFiniteMeasure Ω m0 P]
    {ν : Measure E} [SigmaFinite ν]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (h : Ω → E → ℝ)
    (h_meas : @Measurable (Ω × E) ℝ (m.prod inferInstance) _ (fun q => h q.1 q.2))
    {C : ℝ} (h_bdd : ∀ ω e, |h ω e| ≤ C)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω e, e ∉ S → h ω e = 0)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ (K : ℕ) (B : Fin K → Set E) (c : Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, B k ⊆ S) ∧
      (∀ k, @Measurable Ω ℝ m _ (c k)) ∧
      (∀ k, ∃ M, ∀ ω, |c k ω| ≤ M) ∧
      ∫⁻ ω, ∫⁻ e, (‖h ω e
          - ∑ k, c k ω * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P ≤ δ := by
  classical
  -- finite product measure on the trimmed space.
  haveI hPt : IsFiniteMeasure (P.trim hm) := MeasureTheory.isFiniteMeasure_trim hm
  haveI hνS : IsFiniteMeasure (ν.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hSfin⟩
  set μ : @Measure (Ω × E) (m.prod inferInstance) := (P.trim hm).prod (ν.restrict S) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  set f : Ω × E → ℝ := fun q => h q.1 q.2 with hf
  -- `f ∈ L²(μ)`: bounded on a finite measure.
  have hmem : MeasureTheory.MemLp f 2 μ := by
    refine MeasureTheory.MemLp.mono_exponent ?_ (le_top)
    refine MeasureTheory.memLp_top_of_bound h_meas.aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs]; exact h_bdd q.1 q.2)
  -- tolerance `ε' = √δ`, so `ε'² = δ`.
  set ε' : ℝ≥0∞ := δ ^ (1 / 2 : ℝ) with hε'
  have hε'0 : ε' ≠ 0 := by
    rw [hε', Ne, ENNReal.rpow_eq_zero_iff]; push Not
    exact ⟨fun h0 => absurd h0 hδ, fun _ => by norm_num⟩
  obtain ⟨g, hg_rs, hg_err⟩ :=
    @LevyStochCalc.Poisson.Compensated.rectSimple_dense_L2 Ω m E _ μ _ f hmem ε' hε'0
  obtain ⟨K, a, A, B, hA, hB, hgeq⟩ := @_root_.Prove2MeSourceProof.h_010d482425efb705a03802af Ω m E _ g hg_rs
  -- repackage into a `Fin`-indexed mark-simple family (mark sides ∩ S).
  refine ⟨K, fun k => B k ∩ S, fun k ω => a k * (A k).indicator (fun _ => (1 : ℝ)) ω,
    fun k => (hB k).inter hS, fun k => Set.inter_subset_right, ?_, ?_, ?_⟩
  · intro k
    exact measurable_const.mul (Measurable.indicator measurable_const (hA k))
  · exact fun k => ⟨|a k|, fun ω => by
      rw [abs_mul]
      calc |a k| * |(A k).indicator (fun _ => (1 : ℝ)) ω|
          ≤ |a k| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [Set.indicator_apply]; split_ifs <;> simp
        _ = |a k| := mul_one _⟩
  -- the eval reproduces `g · 𝟙_S` in the mark.
  have heval : ∀ ω e, (∑ k, (a k * (A k).indicator (fun _ => (1 : ℝ)) ω)
        * (B k ∩ S).indicator (fun _ => (1 : ℝ)) e)
      = g (ω, e) * S.indicator (fun _ => (1 : ℝ)) e := by
    intro ω e
    rw [hgeq ω e, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (B k ∩ S).indicator (fun _ => (1 : ℝ)) e
          = (B k).indicator (fun _ => (1 : ℝ)) e * S.indicator (fun _ => (1 : ℝ)) e from by
      simp only [Set.indicator_apply, Set.mem_inter_iff]
      by_cases hk : e ∈ B k <;> by_cases hs : e ∈ S <;> simp [hk, hs]]
    ring
  -- transfer the `L²` bound through the trim bridge; the difference is supported on `S`.
  have hg_meas : @Measurable (Ω × E) ℝ (m.prod inferInstance) _ g :=
    @LevyStochCalc.Poisson.Compensated.IsRectSimple.measurable Ω m E _ g hg_rs
  have hFmeas : @Measurable (Ω × E) ℝ≥0∞ (m.prod inferInstance) _
      (fun q => (‖f q - g q‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp (h_meas.sub hg_meas).nnnorm).pow_const 2
  have hpt : ∀ ω e, (‖h ω e - ∑ k, (a k * (A k).indicator (fun _ => (1 : ℝ)) ω)
        * (B k ∩ S).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2
      = S.indicator (fun e' => (‖h ω e' - g (ω, e')‖₊ : ℝ≥0∞) ^ 2) e := by
    intro ω e
    rw [heval ω e]
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he, Set.indicator_of_mem he, mul_one]
    · rw [Set.indicator_of_notMem he, mul_zero, sub_zero, hsupp ω e he,
      Set.indicator_of_notMem he]
      simp
  calc ∫⁻ ω, ∫⁻ e, (‖h ω e - ∑ k, (a k * (A k).indicator (fun _ => (1 : ℝ)) ω)
          * (B k ∩ S).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
      = ∫⁻ ω, ∫⁻ e in S, (‖h ω e - g (ω, e)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P := by
        refine lintegral_congr (fun ω => ?_)
        rw [← MeasureTheory.lintegral_indicator hS]
        exact lintegral_congr (fun e => hpt ω e)
    _ = ∫⁻ q, (‖f q - g q‖₊ : ℝ≥0∞) ^ 2 ∂((P.trim hm).prod (ν.restrict S)) :=
        (LevyStochCalc.Poisson.Compensated.lintegral_prod_trim_left hm hFmeas).symm
    _ ≤ δ := by
        rw [← hμ]
        have hsq : MeasureTheory.eLpNorm (f - g) 2 μ ^ (2 : ℝ)
            = ∫⁻ q, (‖f q - g q‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
          have hL := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
            (μ := μ) (p := (2 : ℝ≥0)) (f := f - g) (by norm_num)
          rw [show ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
            show ((2 : ℝ≥0) : ℝ) = (2 : ℝ) from by norm_num] at hL
          rw [hL]; refine lintegral_congr (fun q => ?_)
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
        calc ∫⁻ q, (‖f q - g q‖₊ : ℝ≥0∞) ^ 2 ∂μ
            = MeasureTheory.eLpNorm (f - g) 2 μ ^ (2 : ℝ) := hsq.symm
          _ ≤ ε' ^ (2 : ℝ) := ENNReal.rpow_le_rpow hg_err (by norm_num)
          _ = δ := by
              rw [hε', ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 from by norm_num,
                ENNReal.rpow_one]
end LevyStochCalc.Poisson.Compensated


