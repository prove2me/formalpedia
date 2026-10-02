-- Prove2me | Definitions.Def_ServiceParts_UnitDecomp_Model
-- name    : ServiceParts_UnitDecomp_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T21:37:01.657011+00:00
-- url     : https://prove2.me/theorems/67b9c46a-09d9-4030-8cc3-8c423c5f67bc
-- title:
--   Single-location periodic-review model with Markov-modulated demand, lead time m − 1 and linear costs
-- statement:
--   A single item is stocked at a single location and reviewed periodically. The data of the model, with the standing assumptions of Section 2.2.1, are:
--
--   1. a finite set $\Sigma$ of states of an exogenous, time-homogeneous Markov chain $(s_n)$, with transition law $P(s,\cdot)$; $s_n$ is observed at the beginning of period $n$;
--   2. for every $s \in \Sigma$, the law $\kappa(s,\cdot)$ of the period demand $D_n \in \{0,1,2,\dots\}$ given $s_n = s$; given $s_n$, the demand $D_n$ and the next state $s_{n+1}$ are independent;
--   3. an integer $m \ge 1$: every unit is at one of the locations $0$ (used), $1$ (on hand), $2,\dots,m$ (in transit) or $m+1$ (at the supplier), and an order placed in period $n$ is on hand in period $n+m-1$;
--   4. a holding cost $h$ per unit on hand and a backorder cost $b$ per waiting customer, charged at the end of each period, with
--   $$0 < h < b;$$
--   5. a discount factor $\alpha \in (0,1]$ ($\alpha = 1$ is the undiscounted case).
--
--   The model also fixes the motion of one unit and one customer within a period. In event 2 of a period a unit at a location $z \in \{2,\dots,m\}$ moves to $z-1$, a unit at the supplier that is released moves to location $m$, and all other units stay. In event 3, if the demand of the period is $d$, a customer at distance $y \in \{2,\dots,d+1\}$ arrives and is then at distance $1$, a customer at distance $y \ge d+2$ moves to $y-d$, and customers at distance $0$ (served) or $1$ (waiting) stay.
--
--   Finally, for any system whose configuration moves by a rule $x \mapsto \mathrm{post}(x,a,d)$ under action $a$ and demand $d$, with end-of-period cost $c(\mathrm{post}(x,a,d))$, the expected discounted cost of a Markov policy $\pi$ over $k$ periods starting in period $n$ from $(s,x)$ is defined by the recursion
--   $$J_0 = 0,\qquad J_{k+1}(n,s,x) = \sum_{d\ge 0}\kappa(s,d)\Big(c(x') + \alpha\sum_{s'}P(s,s')\,J_k(n+1,s',x')\Big),\quad x' = \mathrm{post}(x,\pi(n,s,x),d).$$
--
--   This is the model of Section 2.2.1 on which the system $\mathcal S$, the subsystems $\mathcal S_w$ and every statement of the mission are built.
--
--   **Formalization Note** Costs are extended nonnegative reals, so every expectation is well defined (possibly $+\infty$). Three choices are not written in the book: $h > 0$ (with $h = 0$ an optimal policy with finite orders need not exist, so Theorem 5 fails); $m \ge 1$ (location $m$ must be a transit or on-hand location); and the conditional independence of $D_n$ and $s_{n+1}$ given $s_n$ (the book says only that $s_n$ governs demand and that the law of $D_n$ given $s_n$ is known). The chain's ergodicity (p. 23) is not used on a finite horizon and is omitted. Period $n$'s cost carries the factor $\alpha^{n-1}$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 23-25, Section 2.2.1 and Section 2.2.1.1 (model, locations and distances, sequence of events 1-5, b > h, performance measure)

import Mathlib

open scoped ENNReal NNReal

namespace ServiceParts.UnitDecomp

/-- The data of the single-item, single-location periodic-review system of Section 2.2.1
(Muckstadt, pp. 23–25), with the standing assumptions of the section as fields.

* `σ` is the finite state space of the exogenous Markov chain `sₙ`; `trans s` is the law of
  `sₙ₊₁` given `sₙ = s` (time-homogeneous), `demand s` the law of the period demand `Dₙ` given
  `sₙ = s`. `Dₙ` and `sₙ₊₁` are conditionally independent given `sₙ`.
* Units live at locations `0, 1, …, m + 1` (`0` used, `1` on hand, `2, …, m` in transit,
  `m + 1` at the supplier); an order placed in period `n` is on hand in period `n + m − 1`.
* `h` is the holding cost per unit on hand and `b` the backorder cost per waiting customer,
  charged at the end of each period; `α` is the discount factor (`α = 1`: undiscounted). -/
structure Model (σ : Type) [Fintype σ] where
  /-- transition law of the exogenous Markov chain -/
  trans : σ → PMF σ
  /-- law of the period demand given the current Markov state -/
  demand : σ → PMF ℕ
  /-- the supplier location is `m + 1`; the lead time is `m − 1` periods -/
  m : ℕ
  /-- holding cost per unit on hand at the end of a period -/
  h : ℝ≥0
  /-- backorder cost per waiting customer at the end of a period -/
  b : ℝ≥0
  /-- discount factor -/
  α : ℝ≥0
  one_le_m : 1 ≤ m
  h_pos : 0 < h
  h_lt_b : h < b
  α_pos : 0 < α
  α_le_one : α ≤ 1

/-- The two decisions available for a unit at the supplier (location `m + 1`). -/
inductive Decision
  | release
  | hold
  deriving DecidableEq

/-- Event 2 of the period for one unit: a unit at a location `2, …, m` moves one location
closer; a unit at the supplier location `m + 1` that is released moves to location `m`;
every other unit stays where it is. -/
def unitMove (m z : ℕ) (rel : Bool) : ℕ :=
  if 2 ≤ z ∧ z ≤ m then z - 1 else if z = m + 1 ∧ rel = true then m else z

/-- Event 3 of the period for one customer when the period demand is `d`: a customer at
distance `2, …, d + 1` arrives (distance `1`), a customer at distance `y ≥ d + 2` moves to
distance `y − d`, and customers at distance `0` (served) or `1` (waiting) stay. -/
def custMove (d y : ℕ) : ℕ :=
  if 2 ≤ y then (if y ≤ d + 1 then 1 else y - d) else y

variable {σ : Type} [Fintype σ]

/-- Expected (discounted) cost of a Markov policy `π` over `k` periods, starting in period `n`
with Markov state `s` and physical configuration `x`. In each period the policy picks an
action from `(n, s, x)`, the demand `d` is drawn from `demand s`, the configuration moves to
`post x a d` and the end-of-period cost `stage (post x a d)` is charged; the next Markov
state is drawn from `trans s`, and later periods are discounted by `α`. -/
noncomputable def Model.costToGo {X A : Type} (M : Model σ) (post : X → A → ℕ → X)
    (stage : X → ℝ≥0∞) (π : ℕ → σ → X → A) : ℕ → ℕ → σ → X → ℝ≥0∞
  | 0, _, _, _ => 0
  | k + 1, n, s, x =>
      ∑' d : ℕ, M.demand s d *
        (stage (post x (π n s x) d) +
          (M.α : ℝ≥0∞) * ∑ s' : σ, M.trans s s' *
            Model.costToGo M post stage π k (n + 1) s' (post x (π n s x) d))

end ServiceParts.UnitDecomp


