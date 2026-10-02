-- Prove2me | Definitions.Def_NumStochOpt_LogConcave_chanceProb
-- name    : NumStochOpt_LogConcave_chanceProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T19:35:41.960743+00:00
-- url     : https://prove2.me/theorems/adc31478-c9bd-464d-beb0-a8d79cb9e972
-- title:
--   The probability function $h_0(x) = P(g_1(x,\xi) \ge 0, \dots, g_r(x,\xi) \ge 0)$
-- statement:
--   This file fixes the probability function of a joint probabilistic (chance) constraint, the central object of Prékopa's chapter.
--
--   Let $(\Omega, \mathcal F, P)$ be a probability space, let $\xi : \Omega \to \mathbb R^q$ be a random vector, and let $g_1, \dots, g_r : \mathbb R^n \times \mathbb R^q \to \mathbb R$ be the constraint functions of problem (5.1). For a decision $x \in \mathbb R^n$ the **probability function** is
--
--   $$
--   h_0(x) = P\bigl(g_1(x,\xi) \ge 0,\ \dots,\ g_r(x,\xi) \ge 0\bigr),
--   $$
--
--   the probability that all $r$ random constraints are satisfied simultaneously at $x$. The probabilistic constraint of (5.1) is $h_0(x) \ge p$ for a prescribed probability level $p$.
--
--   In the most important special case $g_i(x,y) = T_i x - y_i$ one gets $h_0(x) = P(Tx \ge \xi) = F(Tx)$, where $F$ is the joint distribution function of $\xi$ ((5.2)–(5.3)).
--
--   **Formalization Note** $\mathbb R^n$ and $\mathbb R^q$ are `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin q)`; the $r$ constraints are indexed by `Fin r` and each takes a pair $(x, y)$, so joint concavity in $(x,y)$ can be stated on the product space. The value is the real number `(P {ω | ∀ i, 0 ≤ g i (x, ξ ω)}).toReal`; for a probability measure $P$ this is the probability itself (it lies in $[0,1]$).
-- source:
--   A. Prékopa, "Numerical Solution of Probabilistic Constrained Programming Problems", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 5, p. 123, Eq. (5.1)

import Mathlib

open MeasureTheory

namespace NumStochOpt.LogConcave

/-- The probability function of the joint probabilistic constraint in problem (5.1) of
Prékopa, Ch. 5 of Ermoliev & Wets (1988), p. 123:
`h₀(x) = P(g₁(x, ξ) ≥ 0, …, g_r(x, ξ) ≥ 0)`, for a random vector `ξ : Ω → ℝ^q` on the
probability space `(Ω, P)` and constraint functions `gᵢ : ℝ^n × ℝ^q → ℝ`, `i = 1, …, r`
(indexed here by `Fin r`). -/
noncomputable def chanceProb {Ω : Type*} [MeasurableSpace Ω] {n q r : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin q))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (P {ω | ∀ i, 0 ≤ g i (x, ξ ω)}).toReal

end NumStochOpt.LogConcave


