-- Prove2me | Definitions.Def_KellyStochasticNetworks_LossNetwork
-- name    : KellyStochasticNetworks_LossNetwork
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T15:41:29.516509+00:00
-- url     : https://prove2.me/theorems/cf40f906-7444-4de4-b2df-849a937b9a34
-- title:
--   Loss networks: feasible states, product-form weights, truncation, and the Erlang fixed point equations
-- statement:
--   The model of Chapter 3 of Kelly and Yudovina, *Stochastic Networks*: a **loss network with
--   fixed routing**, and the objects its analysis needs.
--
--   There are $J$ links, link $j$ carrying $C_j$ circuits, and $R$ routes. The **link-route
--   incidence matrix** $A$ records that a call on route $r$ requires $A_{jr}$ circuits from
--   link $j$; it is lost if any link has fewer free. Calls requesting route $r$ arrive as a
--   Poisson process of rate $\nu_r$, independently across routes, and hold their circuits for an
--   exponentially distributed time of unit mean. With $n_r$ the number of calls in progress on
--   route $r$, the feasible states are
--   $$S(C) = \{n \in \mathbb{Z}_+^{R} : An \le C\}.$$
--
--   Four further objects are introduced.
--
--   1. The **product-form weight** $\prod_r \nu_r^{n_r}/n_r!$ of equation (3.3), which becomes
--      the equilibrium distribution once multiplied by the normalizing constant $G(C)$.
--   2. **Truncation** of a Markov process to a subset of its state space: rates between states of
--      the subset are unchanged, and a transition leaving it is suppressed. Truncating the
--      uncapacitated network to $S(C)$ is what produces the loss network.
--   3. The objective of the **Dual problem** (3.5) of section 3.4,
--      $$\sum_r \nu_r e^{-\sum_j y_j A_{jr}} + \sum_j y_j C_j,$$
--      to be minimized over $y \ge 0$.
--   4. The **Erlang fixed point equations** (3.7),
--      $$E_j = E\!\left((1-E_j)^{-1}\sum_r A_{jr}\nu_r\prod_i (1-E_i)^{A_{ir}},\; C_j\right),
--        \qquad j = 1,\dots,J,$$
--      where $E(\nu,C)$ is Erlang's formula. The factor $(1-E_j)^{-1}$ removes link $j$'s own
--      thinning from the product, so that the argument is the **reduced load** offered to link
--      $j$: the traffic on the routes through $j$, thinned by the blocking probability of every
--      other link each route uses.
--
--   **Formalization Note** Links and routes are indexed by finite types and the incidence matrix
--   has natural-number entries, which is the general case of section 3.3 rather than only the
--   $0$–$1$ case of section 3.1. Truncation is the restriction of the rate matrix to the
--   subtype of feasible states, so a transition out of the set has no target rather than being
--   explicitly zeroed. Erlang's formula is the definition published in mission I of this series.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 3, pp. 49-67 (PDF pp. 57-75): the network model and the link-route incidence matrix pp. 49-50, truncation of a Markov process p. 52, the product form (3.3) p. 53, the Dual problem (3.5) p. 58, and the Erlang fixed point equations (3.7) p. 67. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration

namespace KellyStochasticNetworks

/-- The state space `S(C) = {n : A n ≤ C}` of a loss network with fixed routing: `n r` calls are
in progress on route `r`, route `r` requires `A j r` circuits from link `j`, and link `j` has
`C j` circuits.  Kelly–Yudovina, *Stochastic Networks*, pp. 50 and 53. -/
def lossStates {J R : ℕ} (A : Fin J → Fin R → ℕ) (C : Fin J → ℕ) : Set (Fin R → ℕ) :=
  {n | ∀ j, (∑ r, A j r * n r) ≤ C j}

/-- The unnormalized product-form weight `∏_r ν_r^{n_r} / n_r!` of equation (3.3). -/
noncomputable def lossWeight {R : ℕ} (ν : Fin R → ℝ) (n : Fin R → ℕ) : ℝ :=
  ∏ r, ν r ^ n r / (Nat.factorial (n r) : ℝ)

/-- A Markov process truncated to a subset `A` of its state space: the rates are unchanged
between states of `A`, and a transition leaving `A` is suppressed.  Kelly–Yudovina, p. 52. -/
def truncatedRates {S : Type*} (q : S → S → ℝ) (A : Set S) : A → A → ℝ :=
  fun j k => q (j : S) (k : S)

/-- The objective of the **Dual** problem (3.5) of section 3.4. -/
noncomputable def dualObjective {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (y : Fin J → ℝ) : ℝ :=
  (∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) + ∑ j, y j * (C j : ℝ)

/-- The **Erlang fixed point equations** (3.7):
`E_j = E((1 - E_j)⁻¹ ∑_r A_{jr} ν_r ∏_i (1 - E_i)^{A_{ir}}, C_j)` for every link `j`. -/
def ErlangFixedPoint {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℕ)
    (E : Fin J → ℝ) : Prop :=
  ∀ j, E j = erlang ((1 - E j)⁻¹ * ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r)) (C j)

end KellyStochasticNetworks


