-- Prove2me | Definitions.Def_LeiBR_Sync_NashGame
-- name    : LeiBR_Sync_NashGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:46.816373+00:00
-- url     : https://prove2.me/theorems/9e21e0ea-74f2-4e66-9e19-089a506fe324
-- title:
--   N-player game: strategy spaces $\mathbb R^{n_i}$, profiles, Nash equilibrium, and the Euclidean norm of the vector of block distances
-- statement:
--   There are $N$ players indexed by $i\in\mathcal N=\{1,\dots,N\}$. Player $i$ chooses a strategy $x_i\in\mathbb R^{n_i}$ (with the Euclidean norm) from a strategy set $X_i\subseteq\mathbb R^{n_i}$. A **strategy profile** is $x=(x_1,\dots,x_N)$, and the joint strategy set is $X=\prod_{i}X_i$. For a profile $y$ and a strategy $z\in\mathbb R^{n_i}$, $(z,y_{-i})$ denotes the profile obtained from $y$ by replacing its $i$-th block with $z$.
--
--   Given payoff (cost) functions $f_i$ of the whole profile, each player $i$ minimizes $f_i(x_i,x_{-i})$ over $x_i\in X_i$. A profile $x^*$ is a **Nash equilibrium** if $x^*\in X$ and, for every player $i$,
--   $$f_i(x^*)\le f_i(z,x^*_{-i})\qquad\text{for all } z\in X_i,$$
--   that is, $x^*_i$ solves player $i$'s problem given the rivals' strategies $x^*_{-i}$.
--
--   The distance between two profiles used throughout the paper is the Euclidean norm of the vector of block distances,
--   $$\left\|\begin{pmatrix}\|x_1-y_1\|\\ \vdots\\ \|x_N-y_N\|\end{pmatrix}\right\|=\Big(\sum_{i=1}^N\|x_i-y_i\|^2\Big)^{1/2}.$$
--
--   These are the basic objects of a Nash equilibrium problem with continuous strategy sets; every statement of the mission is phrased in them.
--
--   **Formalization Note** Players are indexed by `Fin N` (0-based). Player $i$'s space is `EuclideanSpace ℝ (Fin (n i))` and a profile is a dependent function; $(z,y_{-i})$ is `Function.update y i z`. Mathlib's own norm on profiles is the sup norm, so the Euclidean norm of the vector of block distances is written out as `blockDist`.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 4, §2.1 (SNash_i) and the definition of an NE; p. 7, (9); p. 11, (26)

import Mathlib

namespace LeiBR.Sync

/-- Player `i`'s strategy space `ℝ^{n_i}`, with the Euclidean norm. -/
abbrev Strat {N : ℕ} (n : Fin N → ℕ) (i : Fin N) : Type := EuclideanSpace ℝ (Fin (n i))

/-- A strategy profile `x = (x_1, …, x_N)`, one strategy per player. -/
abbrev Profile {N : ℕ} (n : Fin N → ℕ) : Type := ∀ i : Fin N, Strat n i

/-- The joint strategy set `X = ∏_i X_i`. -/
def stratSet {N : ℕ} {n : Fin N → ℕ} (X : ∀ i : Fin N, Set (Strat n i)) : Set (Profile n) :=
  Set.univ.pi X

/-- `xs` is a Nash equilibrium of the game in which player `i` minimizes `f i` over `X i`:
`xs ∈ X` and, for every player `i`, `xs i` minimizes `z ↦ f_i(z, xs_{-i})` over `X i`.
The profile `(z, xs_{-i})` is `Function.update xs i z`. -/
def IsNashEq {N : ℕ} {n : Fin N → ℕ} (X : ∀ i : Fin N, Set (Strat n i))
    (f : Fin N → Profile n → ℝ) (xs : Profile n) : Prop :=
  xs ∈ stratSet X ∧ ∀ i : Fin N, ∀ z ∈ X i, f i xs ≤ f i (Function.update xs i z)

/-- The Euclidean norm of the vector of block distances,
`‖(‖x_1 - y_1‖, …, ‖x_N - y_N‖)‖ = √(∑_i ‖x_i - y_i‖²)`. (Mathlib's norm on `Profile n` is the
sup norm, so this is written out.) -/
noncomputable def blockDist {N : ℕ} {n : Fin N → ℕ} (x y : Profile n) : ℝ :=
  Real.sqrt (∑ i : Fin N, ‖x i - y i‖ ^ 2)

end LeiBR.Sync


