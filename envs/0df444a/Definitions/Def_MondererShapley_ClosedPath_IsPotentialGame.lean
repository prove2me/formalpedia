-- Prove2me | Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
-- name    : MondererShapley_ClosedPath_IsPotentialGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:40.428436+00:00
-- url     : https://prove2.me/theorems/e6ce686e-9d18-40a4-befa-937f9f30ae69
-- title:
--   Exact potential game
-- statement:
--   A strategic-form game $\Gamma$ is an **exact potential game** if it admits a function $P:Y\to\mathbb R$ whose difference across each unilateral deviation equals the deviating player's payoff difference:
--
--   $$\exists P:Y\to\mathbb R\quad\forall i,y^{-i},x,z,\quad u^i(y^{-i},x)-u^i(y^{-i},z)=P(y^{-i},x)-P(y^{-i},z).$$
--
--   This is condition (1) in Theorem 2.8 and the paper's unqualified meaning of “potential game.”
--
--   **Formalization Note** Player types are finite; strategy sets may be infinite or empty, as the section does not impose finiteness or nonemptiness on them.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 128 (PDF p. 5), exact-potential-game definition; https://doi.org/10.1006/game.1996.0044

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- A game admits an exact potential. -/
def IsPotentialGame (u : ι → (∀ i, Y i) → ℝ) : Prop := ∃ P, IsPotential u P

end MondererShapley.ClosedPath


