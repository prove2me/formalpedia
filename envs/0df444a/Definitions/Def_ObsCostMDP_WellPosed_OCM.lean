-- Prove2me | Definitions.Def_ObsCostMDP_WellPosed_OCM
-- name    : ObsCostMDP_WellPosed_OCM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:44.519548+00:00
-- url     : https://prove2.me/theorems/cb676c5d-2013-4512-ab42-bdaa56465e1e
-- title:
--   Proposition 2.7, (2.11) — the QVI of the discounted infinite-horizon observation cost model
-- statement:
--   Let $X$ be a finite state space, $A$ a finite nonempty action set, $\{P_a\}_{a\in A}$ stochastic matrices on $X$ (nonnegative entries, rows summing to $1$), $r:X\times A\to\mathbb R$ a reward with $(r_a)_x=r(x,a)$, $\gamma$ a discount factor and $c_{\mathrm{obs}}$ an observation cost. Write $P^n_a$ for the $n$-th power of $P_a$, the $n$-step transition matrix with constant action $a$, and $(\overline{\gamma v^1+r})_x=\max_{a\in A}(\gamma v^1_{a,x}+r_{a,x})$.
--
--   A function $v:\mathbb N\times X\times A\to\mathbb R$, $v^n_{a,x}$, **solves the QVI (2.11)** if for all $n\ge1$, $x\in X$ and $a\in A$,
--
--   $$\min\Big\{v^n_{a,x}-\gamma v^{n+1}_{a,x}-\big(P^n_a r_a\big)_x,\;v^n_{a,x}-\big(P^n_a\,\overline{\gamma v^1+r}\big)_x+c_{\mathrm{obs}}\Big\}=0.$$
--
--   By Proposition 2.7 the value function of the observation cost model, indexed by the time $n$ since the last observation, the last observed state $x$ and the current action $a$, satisfies this QVI. Corollary 3.4 asserts its solutions are unique.
--
--   **Formalization Note** $v$ is curried as `v n x a` $=v^n_{a,x}$; the time-$0$ slice is not constrained.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 12, Proposition 2.7, (2.11); p. 2 (P_a, r, c_obs > 0); p. 11 (γ ∈ (0, 1))

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI

namespace ObsCostMDP.WellPosed

/-- A **stochastic matrix**: nonnegative entries and every row sums to `1` (the transition
matrices `P_a` of the observation cost model, Reisinger–Tam, arXiv:2201.07908v3, p. 2). -/
def IsStochastic {X : Type*} [Fintype X] (P : Matrix X X ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- The left side of the QVI (2.11) of the discounted infinite-horizon observation cost model
(Proposition 2.7, p. 12), at `(n, x, a)`:
`min {v^n_{a,x} − γ v^{n+1}_{a,x} − (P^n_a r_a)_x, v^n_{a,x} − (P^n_a \overline{γv¹ + r})_x + c_obs}`,
where `P^n_a` is the `n`-th matrix power of `P_a` (the `n`-step transition matrix with constant
action `a`), `(r_a)_x = r(x, a)` and `(\overline{γv¹ + r})_y = max_{b∈A}(γ v¹_{b,y} + r_{b,y})`.
**Formalization Note**: `v n x a = v^n_{a,x}`, `P a = P_a`, `r x a = r(x, a)`. -/
def ocmResidual {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [Nonempty A]
    (P : A → Matrix X X ℝ) (r : X → A → ℝ) (γ cobs : ℝ) (v : ℕ → X → A → ℝ)
    (n : ℕ) (x : X) (a : A) : ℝ :=
  min (v n x a - γ * v (n + 1) x a - ∑ y, (P a ^ n) x y * r y a)
    (v n x a - ∑ y, (P a ^ n) x y * actMax (fun b => γ * v 1 y b + r y b) + cobs)

/-- `v` solves the QVI (2.11): the residual is `0` for all `n ≥ 1`, `x ∈ X`, `a ∈ A`. -/
def IsOCMSolution {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A] [Nonempty A]
    (P : A → Matrix X X ℝ) (r : X → A → ℝ) (γ cobs : ℝ) (v : ℕ → X → A → ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ x a, ocmResidual P r γ cobs v n x a = 0

end ObsCostMDP.WellPosed


