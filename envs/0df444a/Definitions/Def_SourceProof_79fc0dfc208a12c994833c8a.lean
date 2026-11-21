-- Prove2me | Definitions.Def_SourceProof_79fc0dfc208a12c994833c8a
-- name    : SourceProof_79fc0dfc208a12c994833c8a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:02:02.577732+00:00
-- url     : https://prove2.me/theorems/3baf339f-a5f4-417a-b302-e3652a76abd2
-- title:
--   LevyStochCalc source module: SourceProof_79fc0dfc208a12c994833c8a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.compensatedProfile_ae_eq_integral_sub_of_measurable` comes from the `LevyStochCalc.Poisson.CompensatedProfileRaw` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_590c988163634556081c71db
import Definitions.Def_SourceProof_6984d0dce12206fd688ba936

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral of an integrable mark profile is pathwise

Let `N` be a Poisson random measure on `[0, ∞) × E` with `σ`-finite intensity `ν`, possibly
`ν(E) = ∞`, and let `f ∈ L¹(ν) ∩ L²(ν)` be a deterministic mark profile. Over a step `(a, b]`,
`0 ≤ a ≤ b`, almost surely `f` is integrable on `(a, b] × E` against `N(ω)` and the compensated
integral of `f` is the raw integral minus its compensator:

  `∫_E f(e) ΔÑ(de) = ∫_{(a, b] × E} f(e) N(ω)(ds, de) − (b − a) ∫_E f dν`.

The mean measure of `N` is its reference intensity (Campbell's formula), so the raw integral of
`|f|` over the step has mean `(b − a) ‖f‖_{L¹(ν)}`. At a simple profile the identity is the
definition of the compensated step integral. Simple functions converging to `f` both in `L¹(ν)`
and in `L²(ν)` then carry the identity to `f`: the compensated integrals converge in `L²(P)` and
the raw integrals minus their compensators converge in `L¹(P)`.

## Main statements

* `LevyStochCalc.Poisson.PoissonRandomMeasure.bind_N` — the mean measure of a Poisson random
  measure is its reference intensity.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.lintegral_lintegral_N` — Campbell's formula.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.ae_integrableOn_cell` — an integrable mark profile
  is almost surely integrable on a step times the mark space.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_integral_sub` — the compensated integral of a
  mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus its compensator.
* `LevyStochCalc.Poisson.compensatedProfileRepr_ae_eq_integral_sub` — the same for the
  representative of the compensated integral for a sub-σ-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The mean measure -/

namespace PoissonRandomMeasure

variable (N : PoissonRandomMeasure P ν)

end PoissonRandomMeasure

/-! ### Simple profiles -/

/-! ### The pathwise identity -/


theorem _root_.Prove2MeSourceProof.h_79fc0dfc208a12c994833c8a (N : PoissonRandomMeasure P ν)
    {f : E → ℝ} (hfm : Measurable f) (hf1 : Integrable f ν) (hf2 : MemLp f 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N f a b =ᵐ[P] fun ω =>
      (∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) - (b - a) * ∫ e, f e ∂ν := by
  set Φ : (E → ℝ) → Ω → ℝ := fun g ω =>
    (∫ q in Set.Ioc a b ×ˢ Set.univ, g q.2 ∂(N.N ω)) - (b - a) * ∫ e, g e ∂ν with hΦ
  -- simple functions converging to `f` in `L¹(ν)` and in `L²(ν)`
  set g : ℕ → SimpleFunc E ℝ := fun n =>
    SimpleFunc.approxOn f hfm Set.univ 0 (Set.mem_univ 0) n with hgdef
  have hg2 : ∀ n, MemLp (g n) 2 ν := fun n =>
    SimpleFunc.memLp_approxOn hfm hf2 (Set.mem_univ 0) MemLp.zero' n
  have hg1 : ∀ n, Integrable (g n) ν := fun n => memLp_one_iff_integrable.1
    (SimpleFunc.memLp_approxOn hfm (memLp_one_iff_integrable.2 hf1) (Set.mem_univ 0)
      MemLp.zero' n)
  have hL2 : Tendsto (fun n => eLpNorm (⇑(g n) - f) 2 ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hfm (Set.mem_univ 0) (by norm_num)
      (by simp) (by simpa using hf2.2)
  have hL1 : Tendsto (fun n => eLpNorm (⇑(g n) - f) 1 ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hfm (Set.mem_univ 0) (by norm_num)
      (by simp) (by simpa using (memLp_one_iff_integrable.2 hf1).2)
  set G : ℕ → LevyStochCalc.Poisson.SimpleProfile E ν := fun n => LevyStochCalc.Poisson.SimpleProfile.ofSimpleFunc (hg2 n) with hGdef
  have hGf : ∀ n, (G n).toFun = g n := fun n => funext fun e =>
    LevyStochCalc.Poisson.SimpleProfile.toFun_ofSimpleFunc (hg2 n) e
  have hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (𝓝 0) := by
    refine hL2.congr fun n => ?_
    rw [hGf n]
    rfl
  -- the compensated step integrals are pathwise
  have hstep : ∀ n, (G n).stepIntegral N a b =ᵐ[P] Φ (g n) := fun n => by
    have h := _root_.Prove2MeSourceProof.h_590c988163634556081c71db N (G n) ha hab
    rw [hGf n] at h
    exact h
  -- the `L¹(P)` bound on the pathwise functional
  have hbound : ∀ n, ∫⁻ ω, ‖Φ (g n) ω - Φ f ω‖ₑ ∂P
      ≤ ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν
        + ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν := by
    intro n
    have hdm : Measurable (⇑(g n) - f) := (g n).measurable.sub hfm
    have hpt : ∀ᵐ ω ∂P, ‖Φ (g n) ω - Φ f ω‖ₑ
        ≤ (∫⁻ q in Set.Ioc a b ×ˢ Set.univ, ‖(⇑(g n) - f) q.2‖ₑ ∂(N.N ω))
          + ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν := by
      filter_upwards [N.ae_integrableOn_cell_of_measurable (g n).measurable (hg1 n) ha b,
        N.ae_integrableOn_cell_of_measurable hfm hf1 ha b] with ω h1 h2
      have hsplit : Φ (g n) ω - Φ f ω
          = (∫ q in Set.Ioc a b ×ˢ Set.univ, (⇑(g n) - f) q.2 ∂(N.N ω))
            - (b - a) * ∫ e, (⇑(g n) - f) e ∂ν := by
        simp only [hΦ, Pi.sub_apply]
        rw [integral_sub h1 h2, integral_sub (hg1 n) hf1]
        ring
      rw [hsplit]
      refine enorm_sub_le.trans (add_le_add (enorm_integral_le_lintegral_enorm _) ?_)
      rw [enorm_mul, Real.enorm_of_nonneg (sub_nonneg.2 hab), eLpNorm_one_eq_lintegral_enorm]
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      N.lintegral_setLIntegral_N_cell hdm.enorm ha b, eLpNorm_one_eq_lintegral_enorm]
  -- the two limits
  have hJm := (LevyStochCalc.Poisson.memLp_compensatedProfile N f a b).aestronglyMeasurable
  have hXm : ∀ n, AEStronglyMeasurable ((G n).stepIntegral N a b) P :=
    fun n => ((G n).memLp_stepIntegral N ha b).aestronglyMeasurable
  have hΦm : AEStronglyMeasurable (Φ f) P :=
    (N.aestronglyMeasurable_setIntegral_cell hfm hf1 ha b).sub aestronglyMeasurable_const
  have h1 : Tendsto (fun n => ∫⁻ ω, ‖LevyStochCalc.Poisson.compensatedProfile N f a b ω
      - (G n).stepIntegral N a b ω‖ₑ ∂P) atTop (𝓝 0) := by
    have hJ := LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile N hf2 ha hab G hG
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJ (fun n => zero_le)
      fun n => ?_
    refine (LevyStochCalc.Poisson.lintegral_enorm_le_eLpNorm_two (hJm.sub (hXm n))).trans (le_of_eq ?_)
    exact eLpNorm_sub_comm _ _ 2 P
  have h2 : Tendsto (fun n => ∫⁻ ω, ‖(G n).stepIntegral N a b ω - Φ f ω‖ₑ ∂P)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν
        + ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν) atTop (𝓝 0) := by
      have hmul := ENNReal.Tendsto.const_mul hL1
        (Or.inr (show ENNReal.ofReal (b - a) ≠ ⊤ from ENNReal.ofReal_ne_top))
      rw [mul_zero] at hmul
      simpa using hmul.add hmul
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      fun n => ?_
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hbound n)
    filter_upwards [hstep n] with ω hω
    rw [hω]
  exact _root_.Prove2MeSourceProof.h_6984d0dce12206fd688ba936 hJm hΦm hXm h1 h2
section Repr

variable {Ω' : Type u} (m : MeasurableSpace Ω') [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

end Repr

end LevyStochCalc.Poisson


