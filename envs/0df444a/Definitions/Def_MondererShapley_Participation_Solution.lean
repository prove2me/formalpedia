-- Prove2me | Definitions.Def_MondererShapley_Participation_Solution
-- name    : MondererShapley_Participation_Solution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:57.886433+00:00
-- url     : https://prove2.me/theorems/a3529222-c92b-44be-bcc6-0d4bfc94e5e1
-- title:
--   Solutions on TU games and efficiency (Monderer–Shapley, p. 136)
-- statement:
--   Let $N = \{1, \dots, n\}$ be the set of players. For a nonempty coalition $S \subseteq N$, $G(S)$ is the space of cooperative games with transferable utility on the player set $S$: real-valued functions $v$ on the subsets of $S$ with $v(\emptyset) = 0$.
--
--   A **solution** $\psi$ assigns to every coalition $S$ and every game $v \in G(S)$ a payoff vector $\psi(v) \in \mathbb R^S$. A solution is **efficient** if
--
--   $$\sum_{i \in S} \psi(v)(i) = v(S) \qquad \text{for every } S \in 2^N \text{ and every } v \in G(S).$$
--
--   These are the objects of Section 6: Theorems 6.1 and 6.2 characterise, among efficient solutions, the Shapley value.
--
--   **Formalization Note** A solution is a function `ψ : Finset ι → (Finset ι → ℝ) → ι → ℝ`: `ψ S w` is the payoff vector for the game `w` on the player set `S`, and only its coordinates $i \in S$ are meaningful. A game on $S$ is represented by any `w : Finset ι → ℝ` with `w ∅ = 0`, of which only the values on subsets of $S$ are meant; in particular the restriction $v_S$ of $v \in G(N)$ is passed as `ψ S v`. This lets `ψ S` depend on values of `w` outside $2^S$, so the Lean class of solutions is larger than the paper's (every solution of the paper is one, via `ψ S w := ψ(w|_{2^S})`). Efficiency is required for every coalition `S` and every `w` with `w ∅ = 0`; for `S = ∅` it reads `0 = w ∅`, which holds.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 136 (PDF p. 13), Section 6, definition of G(S), solution, efficient

import Mathlib

namespace MondererShapley.Participation

/-- A solution (Monderer--Shapley, p. 136): `ψ S w` is the payoff vector the solution assigns to
the TU game `w` on the player set `S`. A game on `S` is a function `w : Finset ι → ℝ` with
`w ∅ = 0`, of which only the values on subsets of `S` are meant; only the coordinates `i ∈ S`
of `ψ S w` are meaningful. -/
abbrev Solution (ι : Type*) := Finset ι → (Finset ι → ℝ) → ι → ℝ

/-- Efficiency (p. 136): `∑_{i ∈ S} ψ(w)(i) = w(S)` for every coalition `S` and every game `w`
on `S` (`w ∅ = 0`). -/
def IsEfficient {ι : Type*} (ψ : Solution ι) : Prop :=
  ∀ (S : Finset ι) (w : Finset ι → ℝ), w ∅ = 0 → ∑ i ∈ S, ψ S w i = w S

end MondererShapley.Participation


