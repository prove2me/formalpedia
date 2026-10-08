-- Prove2me | Definitions.Def_MatroidProphetKW_RankOne_Setting
-- name    : MatroidProphetKW_RankOne_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:09.410084+00:00
-- url     : https://prove2.me/theorems/c62107ee-3845-458c-8792-713df26afdaf
-- title:
--   §1 (1), §3.1 — the prophet's value max_i X_i, the threshold T = E[max_i X_i]/2, p = Pr[max_i X_i ≥ T], and the reward X_τ
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $n \ge 1$, and let $X_1,\dots,X_n$ be real random variables on $\Omega$, observed in the order $X_1, X_2, \dots, X_n$.
--
--   1. The **prophet's value** is the pointwise maximum
--   $$\max_i X_i(\omega) = \max\{X_1(\omega),\dots,X_n(\omega)\}.$$
--   2. For a real threshold $c$, the **single-threshold rule** stops at the first time $\tau$ with $X_\tau(\omega) \ge c$ and collects $X_\tau(\omega)$. If no $X_i(\omega)$ reaches $c$, the rule accepts nothing and collects $0$.
--   3. The threshold of §3.1 is
--   $$T = \tfrac12\,\mathbb E\big[\max_i X_i\big],$$
--   and $p = \Pr[\max_i X_i \ge T]$ is the probability that the rule with threshold $T$ accepts some element.
--   4. The **reward** $X_\tau$ is the amount collected by the single-threshold rule with threshold $T$: $X_\tau(\omega) = X_{\tau(\omega)}(\omega)$ when some $X_i(\omega) \ge T$, with $\tau(\omega)$ the least such index, and $X_\tau(\omega) = 0$ otherwise.
--
--   These are the objects of the rank-one analysis of Kleinberg and Weinberg (§3.1), which gives a proof of the Krengel–Sucheston–Garling prophet inequality $2\,\mathbb E[X_\tau] \ge \mathbb E[\max_i X_i]$ for this explicit rule.
--
--   **Formalization Note** The variables are `X : Fin n → Ω → ℝ` with `[NeZero n]`; the maximum is `Finset.sup'` over the nonempty index set, so it is never a junk value. $T$ is a Bochner integral divided by $2$; theorems assume $\max_i X_i$ integrable (the paper's $\mathbb E[\max_i X_i] < \infty$), so $T$ is the true half-mean. Probabilities are `Measure.real`, i.e. $\mathbb P(\cdot)$ as a real number. The stopping index is the least element (`Finset.min'`) of $\{i : T \le X_i(\omega)\}$; weak inequality, as in the paper. The rule is **not** forced to stop at $X_n$: when nothing reaches $T$ the reward is $0$.
-- source:
--   Kleinberg & Weinberg, Matroid Prophet Inequalities, arXiv:1201.4764v1, p. 1, §1 (1); p. 5, §3.1 (T = E[max_i X_i]/2, τ, p = Pr[max_i X_i ≥ T])

import Mathlib

namespace MatroidProphetKW.RankOne

open MeasureTheory

variable {Ω : Type*} {n : ℕ}

/-- The prophet's value `max_i X_i(ω)` of `n ≥ 1` real random variables `X_1, …, X_n`
(Kleinberg–Weinberg, *Matroid Prophet Inequalities*, arXiv:1201.4764v1, §1 (1), p. 1; §3.1, p. 5). -/
noncomputable def maxX [NeZero n] (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)

/-- The reward of the single-threshold rule with threshold `c`: the rule observes `X_1, X_2, …`
in order and stops at the first time `τ` with `X_τ(ω) ≥ c`, collecting `X_τ(ω)`. If no `X_i(ω)`
reaches `c` the rule accepts nothing and collects `0` (§3.1, p. 5). -/
noncomputable def thresholdReward (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) : ℝ := by
  classical
  exact if h : (Finset.univ.filter (fun i : Fin n => c ≤ X i ω)).Nonempty then
    X ((Finset.univ.filter (fun i : Fin n => c ≤ X i ω)).min' h) ω
  else 0

/-- The threshold of §3.1 (p. 5): `T = E[max_i X_i] / 2`. -/
noncomputable def thr [MeasurableSpace Ω] [NeZero n] (P : Measure Ω) (X : Fin n → Ω → ℝ) : ℝ :=
  (∫ ω, maxX X ω ∂P) / 2

/-- The paper's `p = Pr[max_i X_i ≥ T]` (§3.1, p. 5), the probability that the rule with
threshold `T` accepts some element. -/
noncomputable def stopProb [MeasurableSpace Ω] [NeZero n] (P : Measure Ω) (X : Fin n → Ω → ℝ) :
    ℝ :=
  P.real {ω | thr P X ≤ maxX X ω}

/-- The paper's `X_τ` (§3.1, p. 5): the reward of the rule that stops at the first time `τ` with
`X_τ ≥ T = E[max_i X_i]/2`, and `0` if there is no such time. -/
noncomputable def reward [MeasurableSpace Ω] [NeZero n] (P : Measure Ω) (X : Fin n → Ω → ℝ)
    (ω : Ω) : ℝ :=
  thresholdReward X (thr P X) ω

end MatroidProphetKW.RankOne


