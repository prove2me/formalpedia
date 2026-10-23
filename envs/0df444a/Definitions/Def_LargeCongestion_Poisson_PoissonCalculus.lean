-- Prove2me | Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
-- name    : LargeCongestion_Poisson_PoissonCalculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:52.097676+00:00
-- url     : https://prove2.me/theorems/371ceee8-3318-40bf-86d3-c68a9f698c71
-- title:
--   Appendix C, pp. 37–39 — Poisson probabilities, Poisson mixtures h̆, forward differences Δ^j h, and sums of independent Bernoulli variables
-- statement:
--   This file fixes the Poisson calculus of Appendix C of Cominetti, Scarsini, Schröder and Stier-Moses.
--
--   1. **Poisson probabilities.** For $x \ge 0$ and $X \sim \mathrm{Poisson}(x)$,
--   $$\mathsf P(X = k) = e^{-x}\frac{x^k}{k!}, \qquad k \in \mathbb N .$$
--   The probability is read off Mathlib's Poisson measure, so the same law is used in expectations and in total-variation statements.
--
--   2. **Poisson mixtures.** For $h : \mathbb N \to \mathbb R$,
--   $$\breve h(x) = \mathsf E[h(X)] = \sum_{k=0}^{\infty} h(k)\, e^{-x}\frac{x^k}{k!}.$$
--
--   3. **Forward differences.** $\Delta h(k) = h(k+1) - h(k)$, and $\Delta^j h$ is its $j$-th iterate. In particular $\Delta^2 h(k) = h(k+2) - 2h(k+1) + h(k)$, the second difference of condition (18); this identity is recorded as a structural lemma.
--
--   4. **Sums of independent Bernoulli variables.** For $p_1, \dots, p_n$, the outcome $\omega \in \{0,1\}^n$ has probability $\prod_i p_i^{\omega_i}(1-p_i)^{1-\omega_i}$, and $S(\omega) = \omega_1 + \dots + \omega_n$. The law $\mathcal L(S)$ on $\mathbb N$ (the Poisson-binomial law) and the finite expectation $\mathsf E[h(S)]$ are defined from these weights.
--
--   These objects are the vocabulary of (46), Propositions 5–6, Corollary 5 and Theorem 9, which control how well Poisson laws approximate loads made of many rare participations.
--
--   **Formalization Note** The Poisson parameter enters as `x.toNNReal`, so $x < 0$ behaves like $x = 0$; every theorem using these objects assumes $x \ge 0$. The mixture $\breve h$ is a `tsum`, which Lean sets to $0$ for a non-summable series; each theorem that reads it carries or proves the corresponding summability. The Bernoulli law is a finite sum of point masses with weights `ENNReal.ofReal`, a probability measure whenever $0 \le p_i \le 1$.
-- source:
--   Cominetti, Scarsini, Schröder & Stier-Moses, Approximation and Convergence of Large Atomic Congestion Games, arXiv:2001.02797v7, pp. 37–39, Appendix C (P(X = k) = e^{−x}x^k/k!, h̆, Δh), p. 18 after (18) (Δ²), p. 39 (S = X_1 + … + X_n)

import Mathlib

namespace LargeCongestion.Poisson

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The forward difference `Δh(k) = h(k + 1) − h(k)` of a function `h : ℕ → ℝ`
(Cominetti et al., Appendix C, p. 37). -/
def delta (h : ℕ → ℝ) : ℕ → ℝ := fun k => h (k + 1) - h k

/-- The `j`-th iterated forward difference `Δ^j h` (Appendix C, Propositions 5–6). -/
def deltaPow (j : ℕ) (h : ℕ → ℝ) : ℕ → ℝ := delta^[j] h

/-- `Δ²h(k) = h(k + 2) − 2h(k + 1) + h(k)`, the formula printed after (18), p. 18. -/
theorem deltaPow_two (h : ℕ → ℝ) (k : ℕ) :
    deltaPow 2 h k = h (k + 2) - 2 * h (k + 1) + h k := by
  simp only [deltaPow, Function.iterate_succ, Function.iterate_zero, Function.comp_apply,
    delta, id]
  ring_nf

/-- The Poisson probability `P(X = k)` for `X ∼ Poisson(x)`, read off Mathlib's
`poissonMeasure` (parameter `x.toNNReal`), so expectations and total-variation statements use
one and the same Poisson law. -/
noncomputable def poissonPmf (x : ℝ) (k : ℕ) : ℝ :=
  (poissonMeasure x.toNNReal).real {k}

/-- For `x ≥ 0`, `P(X = k) = e^{−x} x^k / k!` (Appendix C, p. 37). -/
theorem poissonPmf_eq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    poissonPmf x k = Real.exp (-x) * x ^ k / (k.factorial : ℝ) := by
  rw [poissonPmf, poissonMeasure_real_singleton, Real.coe_toNNReal x hx]

/-- The Poisson mixture `h̆(x) = E[h(X)] = ∑_{k ≥ 0} h(k) e^{−x} x^k / k!`, `X ∼ Poisson(x)`
(Appendix C, p. 37). The series is a `tsum`, which is a
genuine expectation only where it is summable. -/
noncomputable def poissonMean (h : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, h k * poissonPmf x k

/-- Probability of an outcome `ω ∈ {0,1}^n` of independent Bernoulli variables with
`P(X_i = 1) = p_i`. -/
def bernoulliWeight {n : ℕ} (p : Fin n → ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ i, if ω i then p i else 1 - p i

/-- The number of successes `S(ω) = X_1(ω) + ⋯ + X_n(ω)`. -/
def successCount {n : ℕ} (ω : Fin n → Bool) : ℕ :=
  ∑ i, if ω i then 1 else 0

/-- The law `L(S)` on `ℕ` of `S = X_1 + ⋯ + X_n`, a sum of independent Bernoulli variables
with `P(X_i = 1) = p_i` (the Poisson-binomial law; Appendix C, p. 39). -/
noncomputable def poissonBinomial {n : ℕ} (p : Fin n → ℝ) : Measure ℕ :=
  ∑ ω : Fin n → Bool, ENNReal.ofReal (bernoulliWeight p ω) • Measure.dirac (successCount ω)

/-- `E[h(S)]` for `S = X_1 + ⋯ + X_n` as above (a finite sum). -/
def bernoulliSumMean {n : ℕ} (p : Fin n → ℝ) (h : ℕ → ℝ) : ℝ :=
  ∑ ω : Fin n → Bool, bernoulliWeight p ω * h (successCount ω)

end LargeCongestion.Poisson


