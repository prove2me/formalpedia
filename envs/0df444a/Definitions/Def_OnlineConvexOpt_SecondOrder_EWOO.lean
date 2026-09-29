-- Prove2me | Definitions.Def_OnlineConvexOpt_SecondOrder_EWOO
-- name    : OnlineConvexOpt_SecondOrder_EWOO
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:30:50.824266+00:00
-- url     : https://prove2.me/theorems/7bdd65b7-709f-4c27-ad5c-3e26db86c568
-- title:
--   Algorithm 11 — the Exponentially Weighted Online Optimizer
-- statement:
--   The Exponentially Weighted Online Optimizer (EWOO, Algorithm 11) is a multiplicative-weights
--   algorithm for online convex optimization against exp-concave losses on a convex decision set
--   $K \subseteq \mathbb{R}^n$. Given a parameter $\alpha > 0$ and cost functions
--   $f_0, f_1, \dots$, define the un-normalized weight
--   $$
--   w_t(x) = \exp\Bigl(-\alpha \sum_{\tau < t} f_\tau(x)\Bigr) .
--   $$
--   At round $t$, EWOO plays the $w_t$-weighted centroid of $K$,
--   $$
--   x_t = \frac{\int_K x\, w_t(x)\, dx}{\int_K w_t(x)\, dx} .
--   $$
--   EWOO's regret guarantee (Theorem 4.4) needs no Lipschitz constant or diameter bound on $K$,
--   unlike online Newton step; its drawback is computational, since a naive implementation of
--   the integral takes exponential time in the dimension (a randomized polynomial-time variant
--   exists but is not formalized here).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 60, PDF p. 82, Algorithm 11

import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.SecondOrder

variable {n : ℕ}

/-- The un-normalized exponential weight `w_t(x) = exp(-α Σ_{τ=1}^{t-1} f_τ(x))` of Algorithm 11
(EWOO), for cost functions `f` (0-indexed: `t` here is the book's round `t + 1`, so `Finset.range
t` sums the book's rounds `1, ..., t`, exactly the exponent of `w_{t+1}` in the book's own
0-indexed-shifted convention). -/
noncomputable def ewooWeight (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-α * ∑ τ ∈ Finset.range t, f τ x)

/-- `x` is a run of the Exponentially Weighted Online Optimizer (Algorithm 11, book p. 60, PDF
p. 82) on cost functions `f` over the convex set `K`, with parameter `α > 0`: at every round `t`,
`x t` is the `w_t`-weighted centroid of `K`,
`x_t = (∫_K x w_t(x) dx) / (∫_K w_t(x) dx)`. -/
def IsEWOO (K : Set (EuclideanSpace ℝ (Fin n))) (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ t : ℕ, x t = (∫ y in K, ewooWeight α f t y ∂volume)⁻¹ •
    ∫ y in K, ewooWeight α f t y • y ∂volume

end OnlineConvexOpt.SecondOrder


