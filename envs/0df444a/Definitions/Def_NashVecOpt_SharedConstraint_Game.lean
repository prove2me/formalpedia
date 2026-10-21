-- Prove2me | Definitions.Def_NashVecOpt_SharedConstraint_Game
-- name    : NashVecOpt_SharedConstraint_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:14.722988+00:00
-- url     : https://prove2.me/theorems/b956512d-2c00-46cc-89f8-f789cd4c13aa
-- title:
--   Shared-constraint Nash equilibria (Definition 2.2)
-- statement:
--   Consider finitely many players $i$ with real linear strategy spaces $\mathcal X_i$, arbitrary real-valued cost functions $f_i$ on joint strategies, and an arbitrary shared feasible set $\mathbb X\subseteq\prod_i\mathcal X_i$. A feasible joint strategy $x^*$ is a Nash equilibrium when no player can lower her cost by a feasible unilateral change:
--
--   $$\mathrm{NE}(f,\mathbb X)=\{x^*\in\mathbb X:\forall i,\forall x_i\in\mathcal X_i,\ (x_i,x^*_{-i})\in\mathbb X\Rightarrow f_i(x^*)\le f_i(x_i,x^*_{-i})\}.$$
--
--   This definition provides the game-side solution set used in the main equality. Feasibility is tested on the entire changed strategy, so it retains the shared constraint's coupling between players.
--
--   **Formalization Note** `Function.update` constructs $(x_i,x^*_{-i})$. The definition allows any finite player type; the paper's standing assumption of at least two players is placed on each theorem that uses it.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, p. 4, problem (1) and Definition 2.2

import Mathlib

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Definition 2.2, p. 4: feasible unilateral cost minimization in a shared-constraint game. -/
def NE (f : ι → (∀ j, E j) → ℝ) (X : Set (∀ j, E j)) : Set (∀ j, E j) :=
  {xs | xs ∈ X ∧ ∀ (i : ι) (xi : E i), Function.update xs i xi ∈ X →
      f i xs ≤ f i (Function.update xs i xi)}

end NashVecOpt.SharedConstraint


