-- Prove2me | Definitions.Def_Supermodularity_Cooperative_Core
-- name    : Supermodularity_Cooperative_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:32:21.211715+00:00
-- url     : https://prove2.me/theorems/f20f42d6-2329-4f84-a200-630166676831
-- title:
--   Section 5.1 - the core of a cooperative game (and of a subgame)
-- statement:
--   For a set of players $N$ (modeled as `Fin n`), a coalition $U \subseteq N$, and a
--   characteristic function $f : 2^N \to \mathbb{R}$ (`f : Finset (Fin n) → ℝ`), `Core U f` is the
--   core of the subgame $(U, f\restriction_{2^U})$ (p. 208-209):
--   $$\mathrm{Core}(U, f) = \Big\{ y \in \mathbb{R}^N \ \Big|\ \sum_{i \in U} y_i = f(U) \text{ and }
--   f(S) \le \sum_{i \in S} y_i \text{ for every } S \subseteq U \Big\}.$$
--   `Core Finset.univ f` is the core of the whole game $(N,f)$; `Core U f` for a proper subset $U$
--   is the core of the subgame $(U, f)$ used by Theorem 5.2.6.
--
--   **Formalization note.** A payoff vector `y : Fin n → ℝ` is total on all of `N` even when
--   describing a payoff to the subgame on `U`; only the equality (feasibility on `U`) and the
--   inequalities (acceptability on subsets of `U`) constrain the coordinates indexed by `U`, matching
--   how the book reuses the ambient payoff-vector space $\mathbb{R}^N$ for every subgame.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 208-209, Section 5.1

import Mathlib

namespace Supermodularity.Cooperative

/-- `Core U f` is the core of the cooperative game with characteristic function `f`
restricted to the coalition `U ⊆ Fin n` (Topkis p. 209): the payoff vectors `y` that
are feasible on `U` (`∑_{i∈U} y i = f U`) and acceptable on `U`
(`f S ≤ ∑_{i∈S} y i` for every `S ⊆ U`). `Core Finset.univ f` is the core of the
whole game; `Core U f` for `U ⊊ Finset.univ` is the core of the subgame `(U, f)`. -/
def Core {n : ℕ} (U : Finset (Fin n)) (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ | (∑ i ∈ U, y i) = f U ∧ ∀ S ⊆ U, f S ≤ ∑ i ∈ S, y i}

end Supermodularity.Cooperative


