-- Prove2me | Definitions.Def_HarmonicGames_GenericPure_Games
-- name    : HarmonicGames_GenericPure_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:59.970124+00:00
-- url     : https://prove2.me/theorems/e357fa2c-0c29-4fe1-bb7a-be230364d83f
-- title:
--   Harmonic games: the subspaces $\mathcal P,\mathcal H,\mathcal N$ of (28), the space $\mathcal H\oplus\mathcal N$ of harmonic games, and payoffs
-- statement:
--   Fix a finite set of players $\mathcal M$ and, for each player $m$, a finite strategy set $E^m$. Strategy profiles are $p = (p^m)_m \in E = \prod_m E^m$. A **game** is a collection of utilities $u = (u^m)_{m \in \mathcal M}$ with $u^m \in C_0 = \{E \to \mathbb R\}$, i.e. an element of $C_0^M$, which carries the inner product $\langle u, v\rangle = \sum_m \langle u^m, v^m\rangle_0$. With the operators $D_m$, $D$, $\Pi_m = D_m^\dagger D_m$, $\Pi = \operatorname{diag}(\Pi_1,\dots,\Pi_M)$ and the gradient $\delta_0$ of the game graph (eqs. (9), (20), (21), §4.1):
--
--   1. The **payoff** of player $m$ at the profile $p$ is $u^m(p)$.
--   2. **Definition 4.2** (28): the potential, harmonic and nonstrategic subspaces
--   $$
--   \mathcal P = \{u \mid u = \Pi u,\ Du \in \operatorname{im}\delta_0\},\quad
--   \mathcal H = \{u \mid u = \Pi u,\ Du \in \ker\delta_0^*\},\quad
--   \mathcal N = \{u \mid u \in \ker D\}.
--   $$
--   3. A game is a **harmonic game** if it lies in $\mathcal H \oplus \mathcal N$ (p. 23). The space of harmonic games is the subspace $\mathcal H + \mathcal N$ of $C_0^M$.
--
--   These objects are the vocabulary of the paper's Section 5.2: Lemma 5.1 and Proposition 5.1 are statements about harmonic games, and Proposition 4.1 computes the dimensions of $\mathcal P$, $\mathcal H$, $\mathcal N$.
--
--   **Formalization Note** This module builds on `HarmonicGames.Decomposition.Games`: `potentialSubspace` and `harmonicSubspace` here are abbreviations of the subspaces $\mathcal P$, $\mathcal H$ defined there by (28), and $\mathcal N$ is that module's `nonstrategicSubspace`, so every mission states its results about the same subspaces, the same operator $D$ and the same pseudoinverses (taken for the $C_1$ inner product with the factor $\tfrac12$ and the unweighted sum inner product on $C_0^M$). `payoff E u m p` is $u^m(p)$, the game seen as a plain function `ι → (∀ k, E k) → ℝ`. $\mathcal H \oplus \mathcal N$ is the submodule sum `H ⊔ N`; that the sum is direct is part of the paper's Theorem 4.1 and is not needed by the definition.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 17 (Definition 4.2, (28)), p. 23 (Section 5.2, harmonic games)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Games

/-!
Harmonic games (Section 5.2 of Candogan, Menache, Ozdaglar, Parrilo), built on the operator
layer of `HarmonicGames.Decomposition`: the payoff functions of a game, local names for the
potential and harmonic subspaces `P`, `H` of Definition 4.2, (28) (abbreviations of the subspaces
of `HarmonicGames.Decomposition`, whose nonstrategic subspace `N` is used directly), and the
space `H ⊕ N` of harmonic games (p. 23).
-/

noncomputable section

namespace HarmonicGames.GenericPure

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

/-- The utility functions of a game `u ∈ C0^M` as plain functions:
`payoff u m p = u^m(p)`, the payoff of player `m` at the strategy profile `p`. -/
def payoff (u : HarmonicGames.Decomposition.Games E) : ι → (∀ k, E k) → ℝ := fun m p => u m p

/-- The **potential subspace** `P = {u ∈ C0^M | u = Π u and D u ∈ im δ0}` of (28). -/
abbrev potentialSubspace : Submodule ℝ (HarmonicGames.Decomposition.Games E) :=
  HarmonicGames.Decomposition.potentialSubspace E

/-- The **harmonic subspace** `H = {u ∈ C0^M | u = Π u and D u ∈ ker δ0*}` of (28). -/
abbrev harmonicSubspace : Submodule ℝ (HarmonicGames.Decomposition.Games E) :=
  HarmonicGames.Decomposition.harmonicSubspace E

/-- The space of **harmonic games** `H ⊕ N` (Section 5.2, p. 23): a game is harmonic if it lies
in the sum of the harmonic and the nonstrategic subspaces. -/
def harmonicGames : Submodule ℝ (HarmonicGames.Decomposition.Games E) :=
  harmonicSubspace E ⊔ HarmonicGames.Decomposition.nonstrategicSubspace E

/-- A game `u` is a **harmonic game** if `u ∈ H ⊕ N` (Section 5.2, p. 23). -/
def IsHarmonicGame (u : HarmonicGames.Decomposition.Games E) : Prop := u ∈ harmonicGames E

end HarmonicGames.GenericPure

end


