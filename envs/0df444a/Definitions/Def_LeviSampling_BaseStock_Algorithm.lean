-- Prove2me | Definitions.Def_LeviSampling_BaseStock_Algorithm
-- name    : LeviSampling_BaseStock_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:20.067171+00:00
-- url     : https://prove2.me/theorems/62faceec-bc65-4222-a494-fd8132ddaa87
-- title:
--   The sampling-based base-stock algorithm of §3.3 (p. 835)
-- statement:
--   The algorithm of §3.3 (p. 835) for constant costs $h, b > 0$, given an accuracy $\varepsilon$ and a confidence $\delta$. Stages are $0$-based: stage $t$ is the paper's stage $t+1$, so the paper's factor $T - t + 1$ is $T - t$ here.
--
--   - $\varepsilon_t = \varepsilon / 2T$, $\delta_t = \delta / T$, $\alpha_t = (\varepsilon_t/3)\min(b, h)$.
--   - $N_t = \big\lceil 2((b+h)(T-t))^2 (1/\alpha_t^2)\log(2/\delta_t)\big\rceil$ sample paths in stage $t$.
--   - The sample space holds, for each stage $t < T$, $N_t$ demand paths $(d_0, \dots, d_{T-1})$; under the algorithm's law every path of every stage is independent and distributed with independent coordinates of laws $\mu_0, \dots, \mu_{T-1}$. The samples of one stage are therefore independent of all other stages.
--   - Backward recursion: for $t = T-1, \dots, 0$, with $\tilde R_{t+1}, \dots, \tilde R_{T-1}$ already computed,
--   $$\tilde R_t = \inf\{\, y : \hat U^r_t(y) \ge \alpha_t / 2 \,\},$$
--   where $\hat U^r_t$ is the sample right-derivative estimator built from the $N_t$ stage-$t$ paths and the levels $\tilde R_{t+1}, \dots, \tilde R_{T-1}$.
--
--   **Formalization Note** The paper's $N_t$ is a real number; it is rounded up to an integer. Each stage-$t$ path also carries coordinates for periods before $t$, which the estimator never reads; this does not change the law of the computed levels. The infimum is a real `sInf`; for the parameters of the algorithm the set is nonempty and bounded below (the estimator equals $-b$ below all sample values and $h(T-t) \ge \alpha_t/2$ far above), so it is a true infimum. For $t \ge T$ the level is set to $0$ and never used.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 835, §3.3 (the algorithm)

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Estimator

open MeasureTheory

namespace LeviSampling.BaseStock

/-! The sampling-based algorithm of Levi, Roundy & Shmoys (2007), §3.3, p. 835, for constant
costs `h_t = h`, `b_t = b`. Periods (stages) are 0-based: stage `t` is the paper's stage `t + 1`,
so the paper's horizon factor `T - t + 1` is `T - t` here. -/

/-- The per-stage accuracy `ε_t = ε / 2T` (p. 835). -/
noncomputable def epsStage (T : ℕ) (ε : ℝ) : ℝ := ε / (2 * T)

/-- The per-stage confidence `δ_t = δ / T` (p. 835). -/
noncomputable def deltaStage (T : ℕ) (δ : ℝ) : ℝ := δ / T

/-- The per-stage first-order accuracy `α_t = (ε_t / 3) min(b, h)` (p. 835). -/
noncomputable def alphaStage (T : ℕ) (h b ε : ℝ) : ℝ := epsStage T ε / 3 * min b h

/-- The number of sample paths drawn in stage `t` (0-based),
`N_t = ⌈2 ((b + h)(T - t))² (1/α_t²) log(2/δ_t)⌉`, the paper's
`N_t = 2((b + h)(T - t + 1))² (1/α_t²) log(2/δ_t)` (p. 835) rounded up to an integer. -/
noncomputable def sampleSize (T : ℕ) (h b ε δ : ℝ) (t : ℕ) : ℕ :=
  ⌈2 * ((b + h) * ((T - t : ℕ) : ℝ)) ^ 2 * (1 / alphaStage T h b ε ^ 2) *
      Real.log (2 / deltaStage T δ)⌉₊

/-- The algorithm's sample space: for every stage `t < T`, `N_t` sample paths, each a full demand
vector `Fin T → ℝ`. -/
abbrev SampleSpace (T : ℕ) (h b ε δ : ℝ) : Type :=
  (t : Fin T) → Fin (sampleSize T h b ε δ t) → Fin T → ℝ

/-- The law of the algorithm's samples: all sample paths of all stages are independent, and each
is distributed as `(D_0, …, D_{T-1})` with independent coordinates of laws `μ 0, …, μ (T-1)`. In
particular the samples of stage `t` are independent of those of every other stage (p. 835). -/
noncomputable def algMeasure (T : ℕ) (μ : ℕ → Measure ℝ) (h b ε δ : ℝ) :
    Measure (SampleSpace T h b ε δ) :=
  Measure.pi fun _ => Measure.pi fun _ => pathLaw T μ

/-- The base-stock levels `R̃_0, …, R̃_{T-1}` computed by the algorithm of §3.3 (p. 835) on the
sample outcome `ω`, by backward recursion: in stage `t` (from `T-1` down to `0`), with the levels
`R̃_{t+1}, …, R̃_{T-1}` already computed, `R̃_t = inf {y : Û^r_t(y) ≥ α_t / 2}`, where `Û^r_t` is the
sample right-derivative estimator built from the `N_t` stage-`t` paths of `ω` and the levels
`R̃_{t+1}, …, R̃_{T-1}`. For `t ≥ T` the value is `0` (never used). -/
noncomputable def algLevel (T : ℕ) (h b ε δ : ℝ) (ω : SampleSpace T h b ε δ) (t : ℕ) : ℝ :=
  if ht : t < T then
    sInf {y : ℝ | alphaStage T h b ε / 2 ≤
      sampleRightDeriv T (fun _ => h) (fun _ => b)
        (fun k => if _hk : t < k then algLevel T h b ε δ ω k else 0) t (ω ⟨t, ht⟩) y}
  else 0
termination_by T - t

end LeviSampling.BaseStock


