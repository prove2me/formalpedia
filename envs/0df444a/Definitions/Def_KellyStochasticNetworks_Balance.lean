-- Prove2me | Definitions.Def_KellyStochasticNetworks_Balance
-- name    : KellyStochasticNetworks_Balance
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T05:45:15.117074+00:00
-- url     : https://prove2.me/theorems/3f987a4b-89fe-4973-8c4e-9e9ac0808fa4
-- title:
--   Detailed balance, full balance, and time-reversed rates
-- statement:
--   The reversibility apparatus of Chapter 1 of Kelly and Yudovina, *Stochastic Networks*.
--
--   Let $S$ be a state space, $q = (q(j,k))_{j,k \in S}$ a matrix of transition rates and
--   $\pi = (\pi(j))_{j \in S}$ a collection of real numbers. Three notions are introduced.
--
--   1. **Detailed balance.** $\pi$ and $q$ are in detailed balance when
--   $$\pi(j)\,q(j,k) = \pi(k)\,q(k,j) \qquad \text{for all } j,k \in S.$$
--   In equilibrium this says transitions from $j$ to $k$ occur as frequently as transitions from
--   $k$ to $j$. This is equation (1.4) of the book.
--
--   2. **Full balance (the equilibrium equations).** $\pi$ satisfies the equilibrium equations for
--   $q$ when
--   $$\pi(j)\sum_{k \in S} q(j,k) = \sum_{k \in S} \pi(k)\,q(k,j) \qquad \text{for all } j \in S.$$
--   This is equation (1.2). The sums range over the whole, possibly countably infinite, state
--   space.
--
--   3. **The time-reversed rates.** For $\pi$ strictly positive, the transition rates of the
--   reversed process $Y(t) = X(-t)$ computed in Proposition 1.1 are
--   $$q'(j,k) = \frac{\pi(k)\,q(k,j)}{\pi(j)}.$$
--
--   These three notions are the whole method of the book's first three chapters: an equilibrium
--   distribution is found by guessing that the process is reversible and solving the detailed
--   balance equations, which are a two-term recursion, in place of the equilibrium equations,
--   which are not.
--
--   **Formalization Note** The state space is an arbitrary type, so the same predicates serve
--   finite and countable chains. Full balance is written with Lean's unconditional sum `tsum`;
--   over a finite state space this is the ordinary finite sum, and over a countable one it is the
--   sum of the family whenever that family is summable.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, ch. 1, pp. 15-17 (PDF pp. 23-25); equilibrium equations (1.2), detailed balance equations (1.4), Proposition 1.1. sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib

namespace KellyStochasticNetworks

/-- **Detailed balance.** A collection of numbers `π` and a matrix of transition rates `q`
on a state space `S` satisfy detailed balance when `π j * q j k = π k * q k j` for all
states `j, k`.  This is equation (1.4) of Kelly–Yudovina, *Stochastic Networks*. -/
def DetailedBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  ∀ j k : S, π j * q j k = π k * q k j

/-- **The equilibrium (full balance) equations.** `π` satisfies the equilibrium equations for
the transition rates `q` when `π j * ∑ k, q j k = ∑ k, π k * q k j` for every state `j`.
This is equation (1.2) of Kelly–Yudovina, *Stochastic Networks*; the sums range over the whole
(countable) state space, so they are written as unconditional sums. -/
def FullBalance {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : Prop :=
  ∀ j : S, π j * (∑' k : S, q j k) = ∑' k : S, π k * q k j

/-- **The transition rates of the time-reversed process**, `q' j k = π k * q k j / π j`,
as computed in Proposition 1.1 of Kelly–Yudovina, *Stochastic Networks*. -/
noncomputable def reversedRates {S : Type*} (π : S → ℝ) (q : S → S → ℝ) : S → S → ℝ :=
  fun j k => π k * q k j / π j

end KellyStochasticNetworks


