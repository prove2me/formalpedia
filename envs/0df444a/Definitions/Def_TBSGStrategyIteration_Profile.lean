-- Prove2me | Definitions.Def_TBSGStrategyIteration_Profile
-- name    : TBSGStrategyIteration_Profile
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:02:37.960105+00:00
-- url     : https://prove2.me/theorems/902e65be-a289-4471-b657-aab99c76c7e0
-- title:
--   Positional strategies, strategy profiles, $P_\pi$ and $c_\pi$ (Definition 2.4)
-- statement:
--   A (positional) **strategy** $\pi_1 \in \Pi_1$ of player 1 chooses an action $\pi_1(i) \in A_i$ for every state $i \in S_1$; a strategy $\pi_2 \in \Pi_2$ of player 2 chooses $\pi_2(i) \in A_i$ for every $i \in S_2$. A **strategy profile** is a pair $\pi = (\pi_1, \pi_2) \in \Pi = \Pi_1 \times \Pi_2$; it is also viewed as the map $\pi : S \to A$ with $\pi(i) = \pi_1(i)$ on $S_1$ and $\pi(i) = \pi_2(i)$ on $S_2$.
--
--   For a profile $\pi$, $P_\pi \in \mathbb{R}^{n \times n}$ is the matrix of the rows of $P$ selected by $\pi$, and $c_\pi \in \mathbb{R}^n$ the vector of the costs of the actions of $\pi$:
--   $$(P_\pi)_{i,j} = P_{\pi(i), j}, \qquad (c_\pi)_i = c(\pi(i)).$$
--
--   **Formalization Note.** `Strat1 G` and `Strat2 G` are functions on the subtypes $\{i \in S_1\}$ and $\{i \notin S_1\}$ with a proof that $s(\pi_j(i)) = i$; `Profile G` is the product `Strat1 G × Strat2 G`; `Profile.act`, `Profile.transMat`, `Profile.costVec` are $\pi(\cdot)$, $P_\pi$ and $c_\pi$. Only positional (deterministic, memoryless) strategies occur, as in the paper.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 3, Definition 2.4 and the paragraph after it

import Mathlib
import Definitions.Def_TBSGStrategyIteration_Game

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S]

/-- A positional strategy `π₁ ∈ Π₁` of player 1 (Def. 2.4): a choice of an action
`π₁(i) ∈ A_i` for every state `i ∈ S₁`. -/
structure Strat1 (G : Game S A) where
  act : {i : S // i ∈ G.S1} → A
  act_mem : ∀ i, G.src (act i) = i

/-- A positional strategy `π₂ ∈ Π₂` of player 2 (Def. 2.4): a choice of an action
`π₂(i) ∈ A_i` for every state `i ∈ S₂ = S \ S₁`. -/
structure Strat2 (G : Game S A) where
  act : {i : S // i ∉ G.S1} → A
  act_mem : ∀ i, G.src (act i) = i

/-- A strategy profile `π = (π₁, π₂) ∈ Π = Π₁ × Π₂` (Def. 2.4). -/
abbrev Profile (G : Game S A) := Strat1 G × Strat2 G

/-- A profile viewed as a map `π : S → A` (p. 3): `π(i) = π₁(i)` for `i ∈ S₁`, `π(i) = π₂(i)`
for `i ∈ S₂`. -/
def Profile.act {G : Game S A} (π : Profile G) (i : S) : A :=
  if h : i ∈ G.S1 then π.1.act ⟨i, h⟩ else π.2.act ⟨i, h⟩

/-- `P_π ∈ ℝ^{n×n}`: the rows of the probability matrix `P` selected by the actions of `π`
(p. 3), `(P_π)_{i,j} = P_{π(i),j}`. -/
def Profile.transMat {G : Game S A} (π : Profile G) : Matrix S S ℝ :=
  fun i j => G.P (π.act i) j

/-- `c_π ∈ ℝ^n`: the costs of the actions of `π` (p. 3), `(c_π)_i = c(π(i))`. -/
def Profile.costVec {G : Game S A} (π : Profile G) : S → ℝ :=
  fun i => G.c (π.act i)

end TBSGStrategyIteration


