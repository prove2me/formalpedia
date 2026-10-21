-- Prove2me | Definitions.Def_BlottoLP_Flow_ZeroSum
-- name    : BlottoLP_Flow_ZeroSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:28.909318+00:00
-- url     : https://prove2.me/theorems/0a620d41-2e43-4e36-90bb-308abec7af05
-- title:
--   Finite two-player zero-sum games: mixed strategies, expected payoff, Nash equilibria, maxmin and minmax strategies
-- statement:
--   Let $\alpha$ and $\beta$ be finite sets of pure strategies of a row player and a column player, and let $M:\alpha\times\beta\to\mathbb R$ be the row player's payoff; the game is zero-sum, so the column player receives $-M(a,b)$.
--
--   1. A **mixed strategy** on $\alpha$ is a weight function $\sigma:\alpha\to\mathbb R$ with $\sigma(a)\ge 0$ for all $a$ and $\sum_{a}\sigma(a)=1$. The point mass on a pure strategy $a$ is the mixed strategy $\delta_a$.
--   2. The row player's **expected payoff** under weight functions $\sigma,\tau$ is
--   $$
--   M(\sigma,\tau)=\sum_{a\in\alpha}\sum_{b\in\beta}\sigma(a)\,\tau(b)\,M(a,b).
--   $$
--   3. $(\sigma,\tau)$ is a **Nash equilibrium** if both are mixed strategies, $M(\sigma',\tau)\le M(\sigma,\tau)$ for every mixed $\sigma'$, and $M(\sigma,\tau)\le M(\sigma,\tau')$ for every mixed $\tau'$. The set $R$ of the row player's **equilibrium strategies** consists of the $\sigma$ for which some $\tau$ makes $(\sigma,\tau)$ a Nash equilibrium.
--   4. $\sigma$ is a **maxmin strategy** if it is mixed and there is a level $v$ such that $M(\sigma,\tau)\ge v$ for every mixed $\tau$, while for every mixed $\sigma'$ some mixed $\tau$ gives $M(\sigma',\tau)\le v$; that is, $\sigma$ guarantees $v$ and no mixed strategy guarantees more.
--   5. Symmetrically, $\tau$ is a **minmax strategy** if it is mixed and for some $v$, $M(\sigma,\tau)\le v$ for every mixed $\sigma$, while against every mixed $\tau'$ some mixed $\sigma$ gives $M(\sigma,\tau')\ge v$.
--
--   These are the standard notions the paper uses for Colonel Blotto (§2 and §3); they are stated here for an arbitrary finite zero-sum game so that the Blotto model can instantiate them.
--
--   **Formalization Note** Mixed strategies are real weight functions rather than probability measures, and expected payoffs are finite double sums. The maxmin and minmax notions are written with an explicit level $v$ instead of an infimum or supremum, so no junk value of `sSup`/`sInf` enters.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), pp. 4–5, §2 (mixed strategies, Nash equilibria) and §3 (maxmin and minmax strategies)

import Mathlib

namespace BlottoLP.Flow

open Finset

/-- A mixed strategy on a finite set of pure strategies `α`: a weight function that is
non-negative and sums to `1`. -/
def IsMixed {α : Type*} [Fintype α] (σ : α → ℝ) : Prop :=
  (∀ a, 0 ≤ σ a) ∧ ∑ a, σ a = 1

/-- The mixed strategy that plays the pure strategy `a` with probability `1`. -/
def pureMixed {α : Type*} [DecidableEq α] (a : α) : α → ℝ :=
  fun a' => if a' = a then 1 else 0

/-- Expected payoff of the row player in the finite two-player zero-sum game with payoff
`M a b` (row player's payoff when she plays `a` and the column player plays `b`; the column
player receives `- M a b`), when the players use the weight functions `σ` and `τ`. -/
def expPay {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) : ℝ :=
  ∑ a, ∑ b, σ a * τ b * M a b

/-- `(σ, τ)` is a (mixed) Nash equilibrium of the zero-sum game `M`: both are mixed strategies,
the row player cannot raise her expected payoff by deviating, and the column player cannot raise
his (which is `- expPay M σ τ`) by deviating. -/
def IsNashEq {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) (σ : α → ℝ) (τ : β → ℝ) :
    Prop :=
  IsMixed σ ∧ IsMixed τ ∧
    (∀ σ' : α → ℝ, IsMixed σ' → expPay M σ' τ ≤ expPay M σ τ) ∧
    (∀ τ' : β → ℝ, IsMixed τ' → expPay M σ τ ≤ expPay M σ τ')

/-- The row player's strategies that occur in some Nash equilibrium of `M`. -/
def nashRow {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) : Set (α → ℝ) :=
  {σ | ∃ τ, IsNashEq M σ τ}

/-- `σ` is a maxmin strategy of the row player: for some level `v`, `σ` guarantees at least `v`
against every mixed strategy of the column player, and no mixed strategy `σ'` of the row player
guarantees more than `v` (against every `σ'` some mixed `τ` holds the row player to at most `v`). -/
def IsMaxmin {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) (σ : α → ℝ) : Prop :=
  IsMixed σ ∧ ∃ v : ℝ,
    (∀ τ : β → ℝ, IsMixed τ → v ≤ expPay M σ τ) ∧
    (∀ σ' : α → ℝ, IsMixed σ' → ∃ τ : β → ℝ, IsMixed τ ∧ expPay M σ' τ ≤ v)

/-- `τ` is a minmax strategy of the column player: for some level `v`, `τ` holds the row player
to at most `v` against every mixed strategy of hers, and no mixed strategy `τ'` of the column
player holds her below `v`. -/
def IsMinmax {α β : Type*} [Fintype α] [Fintype β] (M : α → β → ℝ) (τ : β → ℝ) : Prop :=
  IsMixed τ ∧ ∃ v : ℝ,
    (∀ σ : α → ℝ, IsMixed σ → expPay M σ τ ≤ v) ∧
    (∀ τ' : β → ℝ, IsMixed τ' → ∃ σ : α → ℝ, IsMixed σ ∧ v ≤ expPay M σ τ')

end BlottoLP.Flow


