-- Prove2me | Definitions.Def_TBSGStrategyIteration_valueIterOp
-- name    : TBSGStrategyIteration_valueIterOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T00:25:21.525356+00:00
-- url     : https://prove2.me/theorems/5f72288f-ed52-4705-99bc-fd14b51d51b8
-- title:
--   Value iteration operator $\mathcal T$ (Definition 4.1)
-- statement:
--   For $v \in \mathbb{R}^n$ write $(c + \gamma P v)_a = c(a) + \gamma \sum_j P_{a,j} v_j$ for every action $a$. The **value iteration operator** $\mathcal T : \mathbb{R}^n \to \mathbb{R}^n$ is
--   $$(\mathcal T v)_i = \begin{cases} \min_{a \in A_i} (c + \gamma P v)_a, & i \in S_1,\\ \max_{a \in A_i} (c + \gamma P v)_a, & i \in S_2.\end{cases}$$
--   The minimum and maximum are over the finite nonempty set $A_i$.
--
--   **Formalization Note.** `actionSet G i` is $A_i$, `qValue G v a` is $(c + \gamma P v)_a$, and the min/max are `Finset.inf'`/`Finset.sup'` with the nonemptiness proof `actionSet_nonempty` (a structural lemma), so no junk value of an empty infimum can occur.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 6, Definition 4.1

import Mathlib
import Definitions.Def_TBSGStrategyIteration_Game

namespace TBSGStrategyIteration

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- `A_i = {a ∈ A | s(a) = i}`, the actions playable from state `i` (Def. 2.2). -/
def actionSet (G : Game S A) (i : S) : Finset A :=
  Finset.univ.filter fun a => G.src a = i

/-- Structural: `A_i ≠ ∅` (the standing assumption of Def. 2.2). -/
theorem actionSet_nonempty (G : Game S A) (i : S) : (actionSet G i).Nonempty := by
  obtain ⟨a, ha⟩ := G.actions_nonempty i
  exact ⟨a, by simp [actionSet, ha]⟩

/-- The vector `c + γ P v ∈ ℝ^m` at the action `a`: `c(a) + γ ∑_j P_{a,j} v_j`. -/
def qValue (G : Game S A) (v : S → ℝ) (a : A) : ℝ :=
  G.c a + G.γ * ∑ j, G.P a j * v j

/-- Def. 4.1: the value iteration operator `𝒯 : ℝ^n → ℝ^n`,
`(𝒯v)_i = min_{A_i} (c + γPv)` for `i ∈ S₁` and `(𝒯v)_i = max_{A_i} (c + γPv)` for `i ∈ S₂`
(the minimum and maximum of a finite nonempty set). -/
def valueIterOp (G : Game S A) (v : S → ℝ) : S → ℝ :=
  fun i => if i ∈ G.S1 then (actionSet G i).inf' (actionSet_nonempty G i) (qValue G v)
    else (actionSet G i).sup' (actionSet_nonempty G i) (qValue G v)

end TBSGStrategyIteration


