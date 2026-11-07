-- Prove2me | Definitions.Def_OnlineCAP_IsRounding
-- name    : OnlineCAP_IsRounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:39.491771+00:00
-- url     : https://prove2.me/theorems/8b314d54-99ea-45f9-8f38-437420af7240
-- title:
--   α(n)-rounding algorithm
-- statement:
--   Let $U$ be a finite universe and $\mathcal F$ a family of subsets of $U$. At time $t$ a **rounding algorithm** receives a request $R_t\in\mathcal F$ together with the current fractional hitting set $x^t$; the inputs $(R_1,x^1),\dots,(R_t,x^t)$ are **valid** when every $R_i\in\mathcal F$, every $x^i\ge0$, $\sum_{e\in R_i}x^i_e\ge1$, and $x^1\le x^2\le\cdots\le x^t$ coordinatewise (so $x^t$ covers every request so far).
--
--   A randomized online algorithm with purchased sets $H_t$ is an **$\alpha$-rounding algorithm** for $\mathcal F$ (Definition 4.11, with $\alpha=\alpha(n)$, $n=|U|$) if on every valid input
--
--   1. for every outcome of its coins, $H_t$ hits every request $R_1,\dots,R_t$;
--   2. for every element $e$,
--   $$\Pr[e\in H_t]\le\alpha\cdot x^t_e .$$
--
--   The input sequence is fixed before the coins are drawn: the requests and $x$ are independent of the algorithm's randomness.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Definitions 4.10–4.11, p.20

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg

namespace OnlineCAP

/-- **Valid input of a rounding algorithm.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definitions 4.10–4.11, p.20 (PDF p.20) and §2.2,
p.10: at time `t` the rounding algorithm receives the request `Rt ∈ F` and the current fractional
hitting set `x^t`, which is nonnegative, monotone (`x^{t−1} ≤ x^t`) and covers every request so
far (`∑_{e ∈ R_{t′}} x^t_e ≥ 1` for `t′ ≤ t`).

A list `[(R₁, x¹), …, (R_t, x^t)]` is valid when every `R_i ∈ F`, every `x^i ≥ 0`,
`∑_{e ∈ R_i} x^i_e ≥ 1`, and `x^1 ≤ x^2 ≤ ⋯ ≤ x^t` coordinatewise. By monotonicity this gives
`x^t(R_{t′}) ≥ 1` for every `t′ ≤ t`. -/
def RoundValid {U : Type} [Fintype U] (F : Set (Set U)) (s : List (Set U × (U → ℝ))) : Prop :=
  (∀ p ∈ s, p.1 ∈ F ∧ (∀ e, 0 ≤ p.2 e) ∧ 1 ≤ ∑ e, p.1.indicator p.2 e) ∧
  s.IsChain (fun p q => ∀ e, p.2 e ≤ q.2 e)

/-- **α(n)-rounding algorithm.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Definition 4.11, p.20 (PDF p.20): "Let U be a universe of n
elements and F be a family of subsets of U. An α(n)-rounding algorithm receives at time step t, the
request Rt ∈ F and the current fractional hitting set xt, and maintains an online hitting set H
such that Pr[e ∈ H] ≤ α(n) · xt_e for every time step t and every element e."

`IsRounding F A α`: on every valid input list `s = [(R₁, x¹), …, (R_t, x^t)]`,
1. for every outcome of the coins, the purchased set `H_t = A.buy ω s` hits every `R_i`;
2. for every element `e`, `Pr[e ∈ H_t] ≤ α · x^t_e`, where `x^t` is the last fractional vector.

**Formalization Note.** The value `α` is the number `α(n)` for the universe at hand (`n = |U|`).
The input list is quantified outside the probability: the requests and `x` are independent of
the algorithm's coins. -/
def IsRounding {U : Type} [Fintype U] (F : Set (Set U))
    (A : RandOnlineAlg U (Set U × (U → ℝ))) (α : ℝ) : Prop :=
  ∀ s, RoundValid F s →
    (∀ ω, ∀ p ∈ s, ∃ e ∈ A.buy ω s, e ∈ p.1) ∧
    ∀ (h : s ≠ []) (e : U), A.μ.real {ω | e ∈ A.buy ω s} ≤ α * (s.getLast h).2 e

end OnlineCAP


