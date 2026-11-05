-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_IcvLE
-- name    : BauerleRiederMDP_RegimeSwitching_IcvLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:56.649202+00:00
-- url     : https://prove2.me/theorems/401eeaa0-e552-4f1b-a967-c056a037dbb8
-- title:
--   Increasing concave order $X\le_{icv}Y$ (Definition B.3.9 c)
-- statement:
--   Let $X$ and $Y$ be real random variables with finite mean and laws $\mu$ and $\nu$. Then $X$ is **smaller than $Y$ in the increasing concave order**, $X\le_{icv}Y$, if
--
--   $$
--   \mathbb E f(X)\le\mathbb E f(Y)
--   $$
--
--   for all increasing, concave functions $f:\mathbb R\to\mathbb R$ for which the expectations exist. The order is also called second-order stochastic dominance; it ranks return distributions by size and by riskiness at once.
--
--   **Formalization Note** The order is stated for the laws $\mu,\nu$; "the expectations exist" is read as integrability of $f$ under both laws. For laws with finite mean this is the book's order: an increasing concave $f$ with infinite expectation is the decreasing limit of integrable increasing concave functions (equal to $f$ on $[-n,\infty)$, affine below), and the inequality passes to the limit.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition B.3.9 c), p.362 (PDF p.368)

import Mathlib
open MeasureTheory

namespace BauerleRiederMDP.RegimeSwitching

/-- The **increasing concave order** `X ≤_icv Y` (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition B.3.9 c), p.362, PDF p.368):
for random variables `X, Y` with finite mean, `X ≤_icv Y` if `𝔼 f(X) ≤ 𝔼 f(Y)` for all
increasing, concave functions `f` for which the expectations exist. Stated for the laws
`μ` of `X` and `ν` of `Y` on `ℝ`.

**Formalization Note.** "Increasing" is `Monotone` (nondecreasing), "concave" is concavity on all
of `ℝ`, and "the expectations exist" is read as integrability of `f` under both laws. For laws
with finite mean this is the book's order: an increasing concave `f` with `𝔼 f(X) = -∞` or
`𝔼 f(Y) = -∞` is the decreasing limit of the increasing concave functions that agree with `f`
on `[-n, ∞)` and are affine (tangent) below `-n`, which are integrable, so the inequality for
integrable `f` extends to it by monotone convergence. -/
def IcvLE (μ ν : Measure ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Monotone f → ConcaveOn ℝ Set.univ f → Integrable f μ → Integrable f ν →
    ∫ y, f y ∂μ ≤ ∫ y, f y ∂ν

end BauerleRiederMDP.RegimeSwitching


