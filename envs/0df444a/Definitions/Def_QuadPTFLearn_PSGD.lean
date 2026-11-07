-- Prove2me | Definitions.Def_QuadPTFLearn_PSGD
-- name    : QuadPTFLearn_PSGD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:21:52.100272+00:00
-- url     : https://prove2.me/theorems/ce0d0a42-8814-4b12-a562-b3a51068a147
-- title:
--   Projected stochastic subgradient descent with step sizes $R/(M\sqrt t)$ and iterate averaging
-- statement:
--   The algorithm of Fact 8.5.
--
--   Let $\Pi_C$ be a Euclidean projection onto a set $C\subseteq\mathbb R^N$ (a nearest point map), $G(w,\xi)$ a stochastic oracle and $\xi_1,\xi_2,\dots$ its independent randomness. Starting from $w_1$, set
--   $$w_{t+1}=\Pi_C\big(w_t-\alpha_tG(w_t,\xi_t)\big),\qquad \alpha_t=\frac{R}{M\sqrt t},$$
--   and return after $T$ oracle calls the average $\hat w=\frac1T\sum_{t=1}^Tw_t$ of the points at which the oracle was queried.
--
--   **Formalization Note** This is the averaging convention of [Duc18]; the page says only "iterate averaging".
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Fact 8.5, p.78 (PDF p.80); citing [Duc18], Corollary 3.4.9

import Mathlib

open MeasureTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-!
# Projected stochastic subgradient descent with iterate averaging

I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Fact 8.5, p.78 (PDF p.80), citing [Duc18], Corollary 3.4.9.

**Formalization Note.**
* `proj` is a Euclidean projection onto the feasible set (a nearest point; for a nonempty closed
  convex set it is unique), `G` the stochastic oracle and `ξ = (ξ₀, ξ₁, …)` its fresh randomness.
* The iterates are `w₁` (given), and `w_{t+1} = proj(w_t − α_t G(w_t, ξ_{t−1}))` with step size
  `α_t = R/(M√t)`; `psgdIter … ξ t` is `w_{t+1}`.
* The output after `T` oracle calls is the plain average `ŵ = (1/T) Σ_{t=1}^{T} w_t` of the `T`
  points at which the oracle is queried ([Duc18]'s averaging convention).
-/

/-- The iterate `w_{t+1}` of projected stochastic subgradient descent (`psgdIter … ξ 0 = w₁`). -/
noncomputable def psgdIter {N : ℕ} {Ξ : Type*} (proj : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → Ξ → EuclideanSpace ℝ (Fin N)) (R M : ℝ)
    (w₁ : EuclideanSpace ℝ (Fin N)) (ξ : ℕ → Ξ) : ℕ → EuclideanSpace ℝ (Fin N)
  | 0 => w₁
  | t + 1 =>
    let w := psgdIter proj G R M w₁ ξ t
    proj (w - (R / (M * Real.sqrt ((t : ℝ) + 1))) • G w (ξ t))

/-- The averaged output `ŵ = (1/T) Σ_{t=1}^{T} w_t`. -/
noncomputable def psgdAvg {N : ℕ} {Ξ : Type*} (proj : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → Ξ → EuclideanSpace ℝ (Fin N)) (R M : ℝ)
    (w₁ : EuclideanSpace ℝ (Fin N)) (T : ℕ) (ξ : ℕ → Ξ) : EuclideanSpace ℝ (Fin N) :=
  (1 / (T : ℝ)) • ∑ t ∈ Finset.range T, psgdIter proj G R M w₁ ξ t

end QuadPTFLearn


