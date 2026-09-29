-- Prove2me | Definitions.Def_StochasticProg_ValueOfInfo_Instance
-- name    : StochasticProg_ValueOfInfo_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:49:53.992657+00:00
-- url     : https://prove2.me/theorems/c070aad9-2e02-418d-9f42-bff5fbb0ff85
-- title:
--   Two-stage recourse instance with K finite scenarios
-- statement:
--   This bundle formalizes a **two-stage stochastic program with fixed recourse and $K$ finite
--   scenarios**, as set up in Birge & Louveaux §4.1 (pp. 163-164).
--
--   An `Instance` consists of: a number $n_1$ of first-stage decision variables and a number
--   $d$ of coordinates describing a scenario; a first-stage feasible set $K_1 \subseteq
--   \mathbb R^{n_1}$; a *scenario cost* function $z(x,\xi)$, giving, for a first-stage decision
--   $x\in\mathbb R^{n_1}$ and a scenario $\xi\in\mathbb R^d$, the optimal value of
--   $$
--   c^Tx + \min\{q^Ty \mid Wy = h(\xi) - Tx,\ y \ge 0\},
--   $$
--   taking values in the extended reals $\overline{\mathbb R} = \mathbb R\cup\{-\infty,+\infty\}$
--   so that $z(x,\xi)=+\infty$ exactly when $x$ has no feasible second-stage recourse under
--   $\xi$, and $z(x,\xi)=-\infty$ when the second-stage program is unbounded below; $K$ scenarios
--   $\xi_1,\dots,\xi_K \in \mathbb R^d$; and probabilities $p_1,\dots,p_K\ge 0$ with
--   $\sum_k p_k = 1$.
--
--   Two derived quantities are defined on top of an instance: the **expected scenario-cost**
--   of a first-stage decision $x$,
--   $$
--   \mathrm{expect}(x) = \mathbb E_\xi\,z(x,\xi) = \sum_{k=1}^K p_k\, z(x,\xi_k),
--   $$
--   and the **mean scenario** $\bar\xi = \mathbb E(\xi) = \sum_{k=1}^K p_k\,\xi_k$.
--
--   This `Instance` and its two derived quantities are the shared foundation for every optimal
--   value (RP, WS, EV, EVPI, EEV, VSS, EVRS, SPEV, EPEV) defined in this mission's other items.
--
--   **Formalization Note** The scenario cost $z$ is taken as a primitive, extended-real-valued
--   function rather than unfolded into its underlying linear program's data $A,b,c,q,W,T,h$,
--   matching the level of abstraction Chapter 4 itself works at (that data is not needed to
--   state any result of this chapter).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 163-165, Chapter 4, Section 4.1-4.2 (eq. 1.1, 1.2, 2.1)

import Mathlib

namespace StochasticProg.ValueOfInfo

/-- A two-stage stochastic program with fixed recourse and `K` finite scenarios,
following Birge & Louveaux §4.1 (p. 163-164): `n1` first-stage decision variables,
scenarios `ξ` living in `ℝ^d`, first-stage feasible set `K1`, and `z x ξ` the
scenario-`ξ` objective value of first-stage decision `x` — the optimal value of
`c^T x + min {q^T y | W y = h(ξ) - T x, y ≥ 0}`, already carrying the book's own
convention that `z x ξ = +∞` when `x` is infeasible for scenario `ξ` and
`z x ξ = -∞` when the second-stage program is unbounded below. -/
structure Instance (n1 d K : ℕ) where
  K1 : Set (Fin n1 → ℝ)
  z : (Fin n1 → ℝ) → (Fin d → ℝ) → EReal
  xi : Fin K → (Fin d → ℝ)
  p : Fin K → ℝ
  p_nonneg : ∀ k, 0 ≤ p k
  p_sum : ∑ k, p k = 1

variable {n1 d K : ℕ}

/-- Extended-real addition with the book's convention (p. 164): `+∞` (infeasibility)
dominates, so `(+∞) + (−∞) = +∞`. Agrees with Mathlib's `EReal` addition whenever no
`+∞` is involved. -/
noncomputable def badd (a b : EReal) : EReal := if a = ⊤ ∨ b = ⊤ then ⊤ else a + b

/-- `a − b` under the same convention. -/
noncomputable def bsub (a b : EReal) : EReal := badd a (-b)

/-- A finite sum under the same convention: `+∞` if any term is `+∞`, else the ordinary sum.
Mathlib's `(0:EReal) * ⊤ = 0`, so a zero-probability scenario never contributes `+∞`. -/
noncomputable def bsum {ι : Type*} [Fintype ι] (f : ι → EReal) : EReal :=
  if ∃ i, f i = ⊤ then ⊤ else ∑ i, f i

/-- The expected scenario-cost of a first-stage decision `x`, under the book's `+∞`
convention (p. 164): `E_ξ z(x,ξ) = ∑_k p_k z(x,ξ_k)`. -/
noncomputable def expect (I : Instance n1 d K) (x : Fin n1 → ℝ) : EReal :=
  bsum (fun k => (I.p k : EReal) * I.z x (I.xi k))

/-- The mean scenario `ξ̄ = E(ξ)` (p. 165, eq. before (2.1)). -/
noncomputable def xiBar (I : Instance n1 d K) : Fin d → ℝ :=
  ∑ k, I.p k • I.xi k

/-- The reference scenario's probability `pᵣ = P(ξ = ξʳ)` (p. 172). -/
noncomputable def refProb (I : Instance n1 d K) (xir : Fin d → ℝ) : ℝ :=
  ∑ k, if I.xi k = xir then I.p k else 0

end StochasticProg.ValueOfInfo


