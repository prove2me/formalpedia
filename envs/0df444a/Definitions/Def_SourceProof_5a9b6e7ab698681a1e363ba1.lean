-- Prove2me | Definitions.Def_SourceProof_5a9b6e7ab698681a1e363ba1
-- name    : SourceProof_5a9b6e7ab698681a1e363ba1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:52:25.479473+00:00
-- url     : https://prove2.me/theorems/818e7645-16eb-4ca3-b43e-51c38499e1fa
-- title:
--   LevyStochCalc source module: SourceProof_5a9b6e7ab698681a1e363ba1
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_of_vanishing_gt` comes from the `LevyStochCalc.Ito.CompensatedLocalityWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a time window

Restricting a marked integrand to a window `(c, t]` preserves admissibility and yields the
increment of the compensated integral across that window; an integrand vanishing after a
positive time `c` has an integral that no longer moves after `c`, the hit indicator of a
stopping time at `c` factors out of the integral over `(c, t]`, and the integral is additive in
the integrand, over differences and over finite sums.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one measurable_uncurry_indIoc hitInd
  abs_hitInd_le_one stronglyMeasurable_hitInd sq_nnnorm_add_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_5a9b6e7ab698681a1e363ba1 {c t : ℝ} (hc : 0 < c) (hct : c ≤ t)
    (hφ : ∀ ω s e, c < s → φ ω s e = 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      =ᵐ[P] stochasticIntegral N ℱ hℱ φ hm hp hq c := by
  set M := LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ hm hp hq with hMdef
  have hmart : Martingale M ℱ P := _root_.Prove2MeSourceProof.h_278d2487462db88d9db97988 N ℱ hℱ φ hm hp hq
  have hMt : MemLp (M t) 2 P := LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq t
  have hMc : MemLp (M c) 2 P := LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq c
  have hMtInt : Integrable (M t) P := hMt.integrable one_le_two
  have hMcInt : Integrable (M c) P := hMc.integrable one_le_two
  have hct_int : Integrable (fun ω => M c ω * M t ω) P := hMc.integrable_mul hMt
  have hcc_int : Integrable (fun ω => M c ω * M c ω) P := hMc.integrable_mul hMc
  have htt_int : Integrable (fun ω => M t ω * M t ω) P := hMt.integrable_mul hMt
  -- the cross moment is the second moment at the earlier time
  have hcross : ∫ ω, M c ω * M t ω ∂P = ∫ ω, M c ω * M c ω ∂P := by
    have hce : P[(fun ω => M c ω * M t ω) | ℱ c]
        =ᵐ[P] fun ω => M c ω * (P[M t | ℱ c]) ω :=
      condExp_mul_of_stronglyMeasurable_left (hmart.stronglyMeasurable c) hct_int hMtInt
    have hmc : P[M t | ℱ c] =ᵐ[P] M c := hmart.condExp_ae_eq hct
    rw [← integral_condExp (ℱ.le c)]
    refine integral_congr_ae (hce.trans ?_)
    filter_upwards [hmc] with ω hω
    rw [hω]
  -- the second moments agree, by the isometry and the vanishing after `c`
  have hwin : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) c, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    have hdisj : Disjoint (Set.Icc (0 : ℝ) c) (Set.Ioc c t) :=
      Set.disjoint_left.2 fun s hs hs' => absurd hs'.1 (not_lt.2 hs.2)
    rw [← Set.Icc_union_Ioc_eq_Icc hc.le hct, lintegral_union measurableSet_Ioc hdisj,
      setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞))
        (fun s hs => by simp [hφ ω s _ hs.1]), lintegral_zero, add_zero]
  have hsq : ∀ {r : ℝ}, 0 ≤ r → ∫ ω, M r ω * M r ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) r, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
    intro r hr
    rw [← LevyStochCalc.Poisson.Compensated.process_lintegral_sq' N ℱ hℱ φ hm hp hq hr,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => mul_self_nonneg _)
        ((LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq r).aestronglyMeasurable.mul
          (LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq r).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← sq, show ((‖M r ω‖₊ : ℝ≥0∞)) = ‖M r ω‖ₑ from rfl,
      Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hsame : ∫ ω, M t ω * M t ω ∂P = ∫ ω, M c ω * M c ω ∂P := by
    rw [hsq (hc.le.trans hct), hsq hc.le]
    congr 1
    exact lintegral_congr hwin
  -- hence the increment has zero second moment
  have hzero : ∫ ω, (M t ω - M c ω) * (M t ω - M c ω) ∂P = 0 := by
    have hexp : (fun ω => (M t ω - M c ω) * (M t ω - M c ω))
        = fun ω => M t ω * M t ω - (2 : ℝ) * (M c ω * M t ω) + M c ω * M c ω := by
      funext ω; ring
    have h1 : Integrable (fun ω => M t ω * M t ω - (2 : ℝ) * (M c ω * M t ω)) P :=
      htt_int.sub (hct_int.const_mul 2)
    rw [hexp, integral_add h1 hcc_int, integral_sub htt_int (hct_int.const_mul 2),
      integral_const_mul, hcross, hsame]
    ring
  have hdiff : Integrable (fun ω => (M t ω - M c ω) * (M t ω - M c ω)) P :=
    (hMt.sub hMc).integrable_mul (hMt.sub hMc)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg _) hdiff).mp hzero
  filter_upwards [hae, LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq t,
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq c] with ω hω ht' hc'
  have h0 : M t ω - M c ω = 0 := mul_self_eq_zero.mp hω
  rw [ht', hc']
  linarith
end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Linear

end LevyStochCalc.Poisson.Compensated


