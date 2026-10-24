-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:29:51.474524+00:00
-- url     : https://prove2.me/theorems/a1d5efde-58bc-4dcc-b55c-d787eec5d0e0
-- title:
--   Tail, exponential, and polynomial moments of Borel log-concave laws
-- statement:
--   `BorelLogConcave.measure_norm_ge_le` bounds the mass of the set $\{v:kR\le\|v\|\}$ by $\operatorname{ofReal}(3^{(1-k)/2})$ when the open ball of radius R has mass at least $3/4$. From this, `integral_exp_norm_le_of_ball` gives integrability and the explicit bound $\int e^{(\log 3/(4R))\|v\|}\,d\nu\le 3^{3/4}/(1-3^{-1/4})$. The remaining declarations convert exponential bounds or a second-moment bound into all-order polynomial moment bounds, and `measure_ball_ge_of_integral_norm_sq_le` supplies the $3/4$ ball-mass hypothesis from $\int\|v\|^2\,d\nu\le R^2/4$.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Moments.lean#L24-L406 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Moments`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set Topology Filter
namespace FunctionalInequalities
section Moments
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
namespace KLS
namespace BorelLogConcave
omit [FiniteDimensional ℝ V] in
/-- Borell's tail lemma in the form needed here: once a ball of radius `R` carries mass at
least `3/4`, the mass outside radius `k R` decays geometrically in `k`. The bound is stated
for every `k`, the cases `k = 0, 1` being trivial. -/
theorem measure_norm_ge_le {ν : ProbabilityMeasure V} (hν : BorelLogConcave ν)
    {R : ℝ} (hball : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R)) (k : ℕ) :
    (ν : Measure V) {v | (k : ℝ) * R ≤ ‖v‖} ≤ ENNReal.ofReal ((3 : ℝ) ^ ((1 - (k : ℝ)) / 2)) := by
  by_cases hk : k < 2
  · have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    calc (ν : Measure V) {v | (k : ℝ) * R ≤ ‖v‖} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((1 - (k : ℝ)) / 2)) :=
        ENNReal.one_le_ofReal.mpr (Real.one_le_rpow (by norm_num) (by linarith))
  push Not at hk
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set t : ℝ := 2 / ((k : ℝ) + 1) with ht_def
  have hk1 : 0 < (k : ℝ) + 1 := by positivity
  have ht : 0 < t := by positivity
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one hk1]; linarith
  have ht_eq : t * ((k : ℝ) + 1) = 2 := by
    rw [ht_def]; field_simp
  set B₀ : Set V := {v | (k : ℝ) * R ≤ ‖v‖} with hB₀_def
  have hB₀ : MeasurableSet B₀ := (isClosed_le continuous_const continuous_norm).measurableSet
  have hB₁ : MeasurableSet (Metric.ball (0 : V) R) := measurableSet_ball
  have key := hν B₀ (Metric.ball 0 R) hB₀ hB₁ t ht ht1
  have hsub : {z | ∃ x ∈ B₀, ∃ y ∈ Metric.ball (0 : V) R, z = t • x + (1 - t) • y} ⊆
      (Metric.closedBall (0 : V) R)ᶜ := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hx' : (k : ℝ) * R ≤ ‖x‖ := hx
    have hy' : ‖y‖ < R := mem_ball_zero_iff.mp hy
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    have h1 := norm_le_add_norm_add (t • x) ((1 - t) • y)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht,
      abs_of_pos (sub_pos.mpr ht1)] at h1
    have h2 : t * ((k : ℝ) * R) ≤ t * ‖x‖ := mul_le_mul_of_nonneg_left hx' ht.le
    have h3 : (1 - t) * ‖y‖ < (1 - t) * R := mul_lt_mul_of_pos_left hy' (sub_pos.mpr ht1)
    have h4 : t * ((k : ℝ) * R) - (1 - t) * R = R := by linear_combination R * ht_eq
    linarith
  have hinner : innerMeasure (ν : Measure V)
      {z | ∃ x ∈ B₀, ∃ y ∈ Metric.ball (0 : V) R, z = t • x + (1 - t) • y} ≤
        (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ :=
    (innerMeasure_mono _ hsub).trans (innerMeasure_le _ _)
  have hcompl : (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ ≤ ENNReal.ofReal (1 / 4) := by
    calc (ν : Measure V) (Metric.closedBall (0 : V) R)ᶜ
        ≤ (ν : Measure V) (Metric.ball (0 : V) R)ᶜ :=
          measure_mono (Set.compl_subset_compl.mpr Metric.ball_subset_closedBall)
      _ = 1 - (ν : Measure V) (Metric.ball (0 : V) R) := prob_compl_eq_one_sub hB₁
      _ ≤ 1 - ENNReal.ofReal (3 / 4) := tsub_le_tsub_left hball 1
      _ = ENNReal.ofReal (1 / 4) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
  have h34 : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) := by
    calc ENNReal.ofReal (3 / 4) = ENNReal.ofReal (3 / 4) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ ≤ ENNReal.ofReal (3 / 4) ^ (1 - t) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr (by norm_num))
            (by linarith)
      _ ≤ (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) :=
          ENNReal.rpow_le_rpow hball (by linarith)
  have hmain : (ν : Measure V) B₀ ^ t * ENNReal.ofReal (3 / 4) ≤ ENNReal.ofReal (1 / 4) :=
    calc (ν : Measure V) B₀ ^ t * ENNReal.ofReal (3 / 4)
        ≤ (ν : Measure V) B₀ ^ t * (ν : Measure V) (Metric.ball (0 : V) R) ^ (1 - t) :=
          mul_le_mul' le_rfl h34
      _ ≤ _ := key
      _ ≤ _ := hinner
      _ ≤ _ := hcompl
  have hpow : (ν : Measure V) B₀ ^ t ≤ ENNReal.ofReal (1 / 3) := by
    have h34ne : ENNReal.ofReal (3 / 4) ≠ 0 := by simp
    have h34top : ENNReal.ofReal (3 / 4) ≠ ⊤ := ENNReal.ofReal_ne_top
    have := (ENNReal.le_div_iff_mul_le (Or.inl h34ne) (Or.inl h34top)).mpr hmain
    rwa [← ENNReal.ofReal_div_of_pos (by norm_num), show (1 / 4 : ℝ) / (3 / 4) = 1 / 3 by norm_num]
      at this
  have hroot : (ν : Measure V) B₀ ≤ ENNReal.ofReal (1 / 3) ^ (((k : ℝ) + 1) / 2) := by
    have h1t : 1 / t = ((k : ℝ) + 1) / 2 := by rw [ht_def, one_div_div]
    calc (ν : Measure V) B₀ = ((ν : Measure V) B₀ ^ t) ^ (1 / t) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel ht.ne', ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal (1 / 3) ^ (1 / t) := ENNReal.rpow_le_rpow hpow (by positivity)
      _ = _ := by rw [h1t]
  refine hroot.trans ?_
  rw [ENNReal.ofReal_rpow_of_pos (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : ((1 : ℝ) / 3) ^ (((k : ℝ) + 1) / 2) = (3 : ℝ) ^ (-(((k : ℝ) + 1) / 2)) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  rw [hexp]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
end BorelLogConcave
end KLS
namespace Probability
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- An exponential moment gives finite moments of every order. -/
theorem integrable_norm_pow_of_integrable_exp_norm {ν : Measure V} [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t) (hint : Integrable (fun v ↦ Real.exp (t * ‖v‖)) ν) (p : ℕ) :
    Integrable (fun v ↦ ‖v‖ ^ p) ν := by
  have hneg : Integrable (fun v ↦ Real.exp (-t * ‖v‖)) ν := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun v ↦ ?_)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg v])
  have := ProbabilityTheory.integrable_pow_abs_of_integrable_exp_mul ht.ne' hint hneg p
  simpa [abs_norm] using this
end Probability
namespace Probability
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Markov: `∫‖v‖² ≤ R²/4` gives mass at least `3/4` to the open ball of radius `R`. -/
theorem measure_ball_ge_of_integral_norm_sq_le {ν : ProbabilityMeasure V} {R : ℝ} (hR : 0 < R)
    (hint : Integrable (fun v : V => ‖v‖ ^ 2) (ν : Measure V))
    (hsecond : (∫ v, ‖v‖ ^ 2 ∂(ν : Measure V)) ≤ R ^ 2 / 4) :
    ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R) := by
  let A : Set V := {v | R ≤ ‖v‖}
  have hA : MeasurableSet A := (isClosed_le continuous_const continuous_norm).measurableSet
  have hsets : {v : V | R ^ 2 ≤ ‖v‖ ^ 2} = A := by
    ext v
    exact sq_le_sq₀ hR.le (norm_nonneg v)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := (ν : Measure V)) (ae_of_all _ fun v => sq_nonneg ‖v‖) hint (R ^ 2)
  rw [hsets] at hmarkov
  have hout : (ν : Measure V).real A ≤ 1 / 4 := by
    nlinarith [sq_pos_of_pos hR]
  have hcompl : (ν : Measure V).real Aᶜ = 1 - (ν : Measure V).real A :=
    probReal_compl_eq_one_sub hA
  have hballset : Aᶜ = Metric.ball (0 : V) R := by
    ext v
    simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Metric.mem_ball, dist_zero_right]
  rw [hballset] at hcompl
  have hreal : (3 / 4 : ℝ) ≤ (ν : Measure V).real (Metric.ball (0 : V) R) := by linarith
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).1
  simpa only [Measure.real, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 4)] using hreal
end Probability
namespace KLS
namespace BorelLogConcave
omit [FiniteDimensional ℝ V] in
/-- **Quantitative Borell exponential moment**: if a ball of radius `R` carries mass `≥ 3/4`, then
`∫ e^{q‖v‖} dν ≤ 3^{3/4}/(1 − 3^{−1/4})` with the explicit rate `q = log 3/(4R)`; constants do not
depend on the law (BKL Section 2, p. 5, uniform moments of the regular approximation). -/
theorem integral_exp_norm_le_of_ball {ν : ProbabilityMeasure V}
    (hν : KLS.BorelLogConcave ν) {R : ℝ} (hR : 0 < R)
    (hball : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R)) :
    Integrable (fun v : V => Real.exp ((Real.log 3 / (4 * R)) * ‖v‖)) (ν : Measure V) ∧
      (∫ v, Real.exp ((Real.log 3 / (4 * R)) * ‖v‖) ∂(ν : Measure V)) ≤
        (3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) := by

  have tail := hν.measure_norm_ge_le hball
  -- the rate and the dominating series
  set t₀ : ℝ := Real.log 3 / (4 * R) with ht₀_def
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ht₀ : 0 < t₀ := by positivity
  set c : ℕ → ℝ := fun k ↦ Real.exp (t₀ * ((k : ℝ) + 1) * R) with hc_def
  set b : ℕ → ℝ := fun k ↦ (3 : ℝ) ^ ((1 - (k : ℝ)) / 2) with hb_def
  set A : ℕ → Set V := fun k ↦ {v | (k : ℝ) * R ≤ ‖v‖} with hA_def
  have hA : ∀ k, MeasurableSet (A k) := fun k ↦
    (isClosed_le continuous_const continuous_norm).measurableSet
  set f : ℕ → V → ENNReal := fun k ↦ (A k).indicator fun _ ↦ ENNReal.ofReal (c k) with hf_def
  have hc_pos : ∀ k, 0 < c k := fun k ↦ Real.exp_pos _
  have hb_pos : ∀ k, 0 < b k := fun k ↦ Real.rpow_pos_of_pos (by norm_num) _
  -- pointwise domination
  have hpt : ∀ v : V, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ∑' k, f k v := by
    intro v
    set n := ⌊‖v‖ / R⌋₊ with hn_def
    have hn1 : (n : ℝ) ≤ ‖v‖ / R := Nat.floor_le (div_nonneg (norm_nonneg _) hR.le)
    have hn2 : ‖v‖ / R < n + 1 := Nat.lt_floor_add_one _
    have hmem : v ∈ A n := by
      show (n : ℝ) * R ≤ ‖v‖
      exact (le_div_iff₀ hR).mp hn1
    have hlt : ‖v‖ < ((n : ℝ) + 1) * R := (div_lt_iff₀ hR).mp hn2
    calc ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ≤ ENNReal.ofReal (c n) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hlt.le ht₀.le
      _ = f n v := by simp [hf_def, Set.indicator_of_mem hmem]
      _ ≤ ∑' k, f k v := ENNReal.le_tsum n
  -- the series
  have hcb : ∀ k, c k * b k = (3 : ℝ) ^ ((3 : ℝ) / 4) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    intro k
    have hc : c k = (3 : ℝ) ^ (((k : ℝ) + 1) / 4) := by
      rw [hc_def, Real.rpow_def_of_pos (by norm_num)]
      rw [ht₀_def]
      field_simp
    rw [hc, hb_def]
    simp only
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hq1 : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq0 : 0 ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable fun k ↦ c k * b k :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _).congr fun k ↦ (hcb k).symm
  -- the integral bound
  have hbound : ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V) ≤
      ENNReal.ofReal (∑' k, c k * b k) := by
    calc ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V)
        ≤ ∫⁻ v, ∑' k, f k v ∂(ν : Measure V) := lintegral_mono hpt
      _ = ∑' k, ∫⁻ v, f k v ∂(ν : Measure V) :=
          lintegral_tsum fun k ↦ (measurable_const.indicator (hA k)).aemeasurable
      _ = ∑' k, ENNReal.ofReal (c k) * (ν : Measure V) (A k) := by
          congr 1; ext k; exact lintegral_indicator_const (hA k) _
      _ ≤ ∑' k, ENNReal.ofReal (c k) * ENNReal.ofReal (b k) :=
          ENNReal.tsum_le_tsum fun k ↦ mul_le_mul' le_rfl (tail k)
      _ = ∑' k, ENNReal.ofReal (c k * b k) := by
          congr 1; ext k; rw [ENNReal.ofReal_mul (hc_pos k).le]
      _ = ENNReal.ofReal (∑' k, c k * b k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (mul_pos (hc_pos k) (hb_pos k)).le) hsum).symm
  have hfinite : ∫⁻ v, ENNReal.ofReal (Real.exp (t₀ * ‖v‖)) ∂(ν : Measure V) < ⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (fun v : V => Real.exp (t₀ * ‖v‖)) (ν : Measure V) := by
    refine ⟨((Real.continuous_exp.comp (continuous_const.mul continuous_norm)).measurable
      |>.aestronglyMeasurable), ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun v => (Real.exp_pos _).le)]
    exact hfinite
  have hreal : (∫ v, Real.exp (t₀ * ‖v‖) ∂(ν : Measure V)) ≤ ∑' k, c k * b k := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun v => (Real.exp_pos _).le)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg fun k => (mul_pos (hc_pos k) (hb_pos k)).le)).1 hbound
  have htsum : (∑' k, c k * b k) =
      (3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) := by
    simp_rw [hcb]
    rw [tsum_mul_left]
    rw [tsum_geometric_of_lt_one hq0 hq1]
    ring
  exact ⟨hint, by simpa only [ht₀_def, htsum] using hreal⟩
omit [FiniteDimensional ℝ V] in
/-- Explicit moment bound of every order `p` from the exponential bound: `∫‖v‖^p ≤ p!/q^p · C₀`. -/
theorem integral_norm_pow_le_of_ball {ν : ProbabilityMeasure V}
    (hν : KLS.BorelLogConcave ν) {R : ℝ} (hR : 0 < R)
    (hball : ENNReal.ofReal (3 / 4) ≤ (ν : Measure V) (Metric.ball (0 : V) R)) (p : ℕ) :
    Integrable (fun v : V => ‖v‖ ^ p) (ν : Measure V) ∧
      (∫ v, ‖v‖ ^ p ∂(ν : Measure V)) ≤
        (p.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ p *
          ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  let t : ℝ := Real.log 3 / (4 * R)
  have ht : 0 < t := div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) hR)
  obtain ⟨hint, hbound⟩ := integral_exp_norm_le_of_ball hν hR hball
  have hpint : Integrable (fun v : V => ‖v‖ ^ p) (ν : Measure V) :=
    Probability.integrable_norm_pow_of_integrable_exp_norm ht hint p
  have hfac : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have htPow : 0 < t ^ p := pow_pos ht p
  have hpt (v : V) : ‖v‖ ^ p ≤ ((p.factorial : ℝ) / t ^ p) * Real.exp (t * ‖v‖) := by
    have hex := Real.pow_div_factorial_le_exp (t * ‖v‖) (mul_nonneg ht.le (norm_nonneg v)) p
    rw [mul_pow] at hex
    have hmul := (div_le_iff₀ hfac).1 hex
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ htPow).2
    simpa only [mul_comm] using hmul
  have hc : 0 ≤ (p.factorial : ℝ) / t ^ p := div_nonneg hfac.le htPow.le
  refine ⟨hpint, ?_⟩
  calc
    (∫ v, ‖v‖ ^ p ∂(ν : Measure V)) ≤
        ∫ v, ((p.factorial : ℝ) / t ^ p) * Real.exp (t * ‖v‖) ∂(ν : Measure V) :=
      integral_mono hpint (hint.const_mul _) hpt
    _ = ((p.factorial : ℝ) / t ^ p) * (∫ v, Real.exp (t * ‖v‖) ∂(ν : Measure V)) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hc
omit [FiniteDimensional ℝ V] in
/-- All-order moment bounds from log-concavity and a second-moment radius `∫‖v‖² ≤ R²/4`. -/
theorem integral_norm_pow_le_of_second_moment {ν : ProbabilityMeasure V}
    (hν : KLS.BorelLogConcave ν) {R : ℝ} (hR : 0 < R)
    (hint : Integrable (fun v : V => ‖v‖ ^ 2) (ν : Measure V))
    (hsecond : (∫ v, ‖v‖ ^ 2 ∂(ν : Measure V)) ≤ R ^ 2 / 4) (p : ℕ) :
    Integrable (fun v : V => ‖v‖ ^ p) (ν : Measure V) ∧
      (∫ v, ‖v‖ ^ p ∂(ν : Measure V)) ≤
        (p.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ p *
          ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  exact integral_norm_pow_le_of_ball hν hR (Probability.measure_ball_ge_of_integral_norm_sq_le hR hint hsecond) p
omit [FiniteDimensional ℝ V] in
/-- All-order moment bounds from log-concavity and a second-moment bound `∫‖v‖² ≤ M`, with the
common radius `R = 2√(M+1)` and rate `log 3/(8√(M+1))`; uniform over all such laws. -/
theorem integral_norm_pow_le_of_second_bound {ν : ProbabilityMeasure V}
    (hν : KLS.BorelLogConcave ν)
    (hint : Integrable (fun v : V => ‖v‖ ^ 2) (ν : Measure V)) {M : ℝ}
    (hM : (∫ v, ‖v‖ ^ 2 ∂(ν : Measure V)) ≤ M) (p : ℕ) :
    let R : ℝ := 2 * Real.sqrt (M + 1)
    Integrable (fun v : V => ‖v‖ ^ p) (ν : Measure V) ∧
      (∫ v, ‖v‖ ^ p ∂(ν : Measure V)) ≤
        (p.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ p *
          ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  dsimp only
  have hM0 : 0 ≤ M := (integral_nonneg fun v : V => sq_nonneg ‖v‖).trans hM
  have hplus : 0 < M + 1 := by linarith
  have hR : 0 < 2 * Real.sqrt (M + 1) := mul_pos (by norm_num) (Real.sqrt_pos.2 hplus)
  have hR2 : (2 * Real.sqrt (M + 1)) ^ 2 = 4 * (M + 1) := by
    rw [mul_pow, Real.sq_sqrt hplus.le]
    norm_num
  have hs : (∫ v, ‖v‖ ^ 2 ∂(ν : Measure V)) ≤ (2 * Real.sqrt (M + 1)) ^ 2 / 4 := by
    rw [hR2]
    nlinarith
  exact integral_norm_pow_le_of_second_moment hν hR hint hs p
end BorelLogConcave
end KLS
end Moments
end FunctionalInequalities


