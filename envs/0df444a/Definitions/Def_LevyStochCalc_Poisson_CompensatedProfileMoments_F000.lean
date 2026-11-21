-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedProfileMoments_F000
-- name    : LevyStochCalc_Poisson_CompensatedProfileMoments_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:35:17.702973+00:00
-- url     : https://prove2.me/theorems/482cde76-25cd-462b-af33-2040388e3f2d
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedProfileMoments
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedProfileMoments. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProfile_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# First and second moments of the compensated integral of a mark profile

The compensated integral of a simple mark profile over a step is a linear combination of
compensated counts, each of mean zero, and the `L²(P)` pairing of two such integrals over a
common step is the step length times the `L²(ν)` pairing of their mark functions. Both
identities pass to the `L²` limits that define the compensated integral of a square-integrable
mark profile: over the step `(a, b]` the mean of `J(f)` vanishes and

  `E[J(f) J(g)] = (b − a) ∫ f g dν`,   `E[J(f)²] = (b − a) ∫ f² dν`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral` — the mean of the compensated
  step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integral_compensatedProfile` — the mean of the compensated integral of
  a square-integrable mark profile over a step.
* `LevyStochCalc.Poisson.integral_compensatedProfile_mul` — the `L²(P)` pairing of the
  compensated integrals of two square-integrable mark profiles over a common step.
* `LevyStochCalc.Poisson.integral_compensatedProfile_sq` — the second moment of the compensated
  integral of a square-integrable mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Passing an `L²` pairing to the limit -/

/-- The second moment of a square-integrable function through its `L²` seminorm. -/
private theorem integral_sq_eq_toReal_eLpNorm_sq {α : Type*} [MeasurableSpace α]
    {m : Measure α} {F : α → ℝ} (hF : MemLp F 2 m) :
    ∫ x, F x ^ 2 ∂m = ((eLpNorm F 2 m).toReal) ^ 2 := by
  have h0 : 0 ≤ ∫ x, F x ^ 2 ∂m := integral_nonneg fun x => sq_nonneg _
  have hE : eLpNorm F 2 m = (ENNReal.ofReal (∫ x, F x ^ 2 ∂m)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num,
      ← Compensated.lintegral_sq_eq_ofReal_integral hF]
    refine congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (lintegral_congr fun x => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [hE, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal h0, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt h0]
/-- Cauchy–Schwarz for two square-integrable real functions. -/
private theorem integral_abs_mul_le_sqrt {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F H : α → ℝ} (hF : MemLp F 2 m) (hH : MemLp H 2 m) :
    ∫ x, |F x| * |H x| ∂m
      ≤ Real.sqrt (∫ x, F x ^ 2 ∂m) * Real.sqrt (∫ x, H x ^ 2 ∂m) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hF' : MemLp (fun x => |F x|) (ENNReal.ofReal 2) m := by
    rw [h2]; simpa [Real.norm_eq_abs] using hF.norm
  have hH' : MemLp (fun x => |H x|) (ENNReal.ofReal 2) m := by
    rw [h2]; simpa [Real.norm_eq_abs] using hH.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := m) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (Eventually.of_forall fun x => abs_nonneg (F x))
    (Eventually.of_forall fun x => abs_nonneg (H x)) hF' hH'
  have hconv : ∀ K : α → ℝ, ∫ x, |K x| ^ (2 : ℝ) ∂m = ∫ x, K x ^ 2 ∂m := by
    intro K
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change |K x| ^ (2 : ℝ) = K x ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  rw [hconv F, hconv H] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h
/-- Cauchy–Schwarz for the integral of a product of two square-integrable real functions. -/
private theorem abs_integral_mul_le {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F H : α → ℝ} (hF : MemLp F 2 m) (hH : MemLp H 2 m) :
    |∫ x, F x * H x ∂m| ≤ Real.sqrt (∫ x, F x ^ 2 ∂m) * Real.sqrt (∫ x, H x ^ 2 ∂m) := by
  refine abs_integral_le_integral_abs.trans ?_
  rw [show ∫ x, |F x * H x| ∂m = ∫ x, |F x| * |H x| ∂m from
    integral_congr_ae (Eventually.of_forall fun x => abs_mul (F x) (H x))]
  exact integral_abs_mul_le_sqrt hF hH
/-- The `L²` distance to the limit of a sequence converging in `L²`, in second-moment form,
tends to zero. -/
private theorem tendsto_sqrt_integral_sub_sq {α : Type*} [MeasurableSpace α] {m : Measure α}
    {X : ℕ → α → ℝ} {X' : α → ℝ} (hd : ∀ n, MemLp (fun x => X n x - X' x) 2 m)
    (hc : Tendsto (fun n => eLpNorm (fun x => X n x - X' x) 2 m) atTop (nhds 0)) :
    Tendsto (fun n => Real.sqrt (∫ x, (X n x - X' x) ^ 2 ∂m)) atTop (nhds 0) := by
  have heq : ∀ n, Real.sqrt (∫ x, (X n x - X' x) ^ 2 ∂m)
      = (eLpNorm (fun x => X n x - X' x) 2 m).toReal := by
    intro n
    rw [integral_sq_eq_toReal_eLpNorm_sq (hd n), Real.sqrt_sq ENNReal.toReal_nonneg]
  simp_rw [heq]
  have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hc
  simpa [Function.comp_def] using h
/-- **The `L²` pairing is continuous along `L²` convergence in each argument.** -/
private theorem tendsto_integral_mul_of_tendsto_L2 {α : Type*} [MeasurableSpace α]
    {m : Measure α} {X Y : ℕ → α → ℝ} {X' Y' : α → ℝ} (hX : ∀ n, MemLp (X n) 2 m)
    (hY : ∀ n, MemLp (Y n) 2 m) (hX' : MemLp X' 2 m) (hY' : MemLp Y' 2 m)
    (hXc : Tendsto (fun n => eLpNorm (fun x => X n x - X' x) 2 m) atTop (nhds 0))
    (hYc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, X n x * Y n x ∂m) atTop (nhds (∫ x, X' x * Y' x ∂m)) := by
  have hdX : ∀ n, MemLp (fun x => X n x - X' x) 2 m := fun n => (hX n).sub hX'
  have hdY : ∀ n, MemLp (fun x => Y n x - Y' x) 2 m := fun n => (hY n).sub hY'
  have hbound : ∀ n, ‖(∫ x, X n x * Y n x ∂m) - ∫ x, X' x * Y' x ∂m‖
      ≤ Real.sqrt (∫ x, (X n x - X' x) ^ 2 ∂m) * Real.sqrt (∫ x, (Y n x - Y' x) ^ 2 ∂m)
        + Real.sqrt (∫ x, (X n x - X' x) ^ 2 ∂m) * Real.sqrt (∫ x, Y' x ^ 2 ∂m)
        + Real.sqrt (∫ x, X' x ^ 2 ∂m) * Real.sqrt (∫ x, (Y n x - Y' x) ^ 2 ∂m) := by
    intro n
    have h1 : Integrable (fun x => (X n x - X' x) * (Y n x - Y' x)) m :=
      (hdX n).integrable_mul (hdY n)
    have h2 : Integrable (fun x => (X n x - X' x) * Y' x) m := (hdX n).integrable_mul hY'
    have h3 : Integrable (fun x => X' x * (Y n x - Y' x)) m := hX'.integrable_mul (hdY n)
    have h12 : Integrable (fun x => (X n x - X' x) * (Y n x - Y' x)
        + (X n x - X' x) * Y' x) m := h1.add h2
    have hs1 : ∫ x, ((X n x - X' x) * (Y n x - Y' x) + (X n x - X' x) * Y' x) ∂m
        = (∫ x, (X n x - X' x) * (Y n x - Y' x) ∂m) + ∫ x, (X n x - X' x) * Y' x ∂m :=
      integral_add h1 h2
    have hs2 : ∫ x, (((X n x - X' x) * (Y n x - Y' x) + (X n x - X' x) * Y' x)
          + X' x * (Y n x - Y' x)) ∂m
        = (∫ x, ((X n x - X' x) * (Y n x - Y' x) + (X n x - X' x) * Y' x) ∂m)
          + ∫ x, X' x * (Y n x - Y' x) ∂m :=
      integral_add h12 h3
    have hs3 : (∫ x, X n x * Y n x ∂m) - ∫ x, X' x * Y' x ∂m
        = ∫ x, (((X n x - X' x) * (Y n x - Y' x) + (X n x - X' x) * Y' x)
          + X' x * (Y n x - Y' x)) ∂m := by
      have hXY : Integrable (fun x => X n x * Y n x) m := (hX n).integrable_mul (hY n)
      have hX'Y' : Integrable (fun x => X' x * Y' x) m := hX'.integrable_mul hY'
      rw [← integral_sub hXY hX'Y']
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [Real.norm_eq_abs, hs3, hs2, hs1]
    refine (abs_add_three _ _ _).trans ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact abs_integral_mul_le (hdX n) (hdY n)
    · exact abs_integral_mul_le (hdX n) hY'
    · exact abs_integral_mul_le hX' (hdY n)
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  have hx := tendsto_sqrt_integral_sub_sq hdX hXc
  have hy := tendsto_sqrt_integral_sub_sq hdY hYc
  have h := ((hx.mul hy).add (hx.mul_const (Real.sqrt (∫ x, Y' x ^ 2 ∂m)))).add
    (hy.const_mul (Real.sqrt (∫ x, X' x ^ 2 ∂m)))
  simpa using h
/-- The integral is continuous along `L²` convergence on a probability measure. -/
private theorem tendsto_integral_of_tendsto_L2 {X : ℕ → Ω → ℝ} {X' : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hX' : MemLp X' 2 P)
    (hXc : Tendsto (fun n => eLpNorm (fun ω => X n ω - X' ω) 2 P) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (nhds (∫ ω, X' ω ∂P)) := by
  have hd : ∀ n, MemLp (fun ω => X n ω - X' ω) 2 P := fun n => (hX n).sub hX'
  have hbound : ∀ n, ‖(∫ ω, X n ω ∂P) - ∫ ω, X' ω ∂P‖
      ≤ Real.sqrt (∫ ω, (X n ω - X' ω) ^ 2 ∂P) := by
    intro n
    have h := abs_integral_mul_le (hd n) (memLp_const (μ := P) (p := 2) (1 : ℝ))
    rw [Real.norm_eq_abs,
      ← integral_sub ((hX n).integrable one_le_two) (hX'.integrable one_le_two)]
    simpa using h
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun n => norm_nonneg _) hbound (tendsto_sqrt_integral_sub_sq hd hXc))
/-! ### The mean -/

/-- The compensated step integral of a simple mark profile has mean zero. -/
theorem SimpleProfile.integral_stepIntegral (N : PoissonRandomMeasure P ν)
    (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫ ω, G.stepIntegral N a b ω ∂P = 0 := by
  have hfin : ∀ k : Fin G.K, referenceIntensity ν (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := by
    intro k
    rw [referenceIntensity_Ioc_prod' _ ha]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k)
  have hint : ∀ k : Fin G.K,
      Integrable (fun ω => G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω) P :=
    fun k => ((G.memLp_compensated_step N ha b k).const_mul _).integrable one_le_two
  simp only [SimpleProfile.stepIntegral]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed N
    (measurableSet_Ioc.prod (G.B_measurable k)) (hfin k), mul_zero]
/-- The compensated integral of a square-integrable mark profile over a step has mean zero. -/
theorem integral_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProfile N f a b ω ∂P = 0 := by
  obtain ⟨G, hG⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  have h := tendsto_integral_of_tendsto_L2 (fun n => (G n).memLp_stepIntegral N ha b)
    (memLp_compensatedProfile N f a b)
    (tendsto_stepIntegral_compensatedProfile N hf ha hab G hG)
  exact tendsto_nhds_unique (h.congr fun n => (G n).integral_stepIntegral N ha b)
    tendsto_const_nhds
/-! ### The second moments -/

end LevyStochCalc.Poisson


