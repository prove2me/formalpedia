-- Prove2me | Definitions.Def_MondererShapley_ClosedPath_IsStep
-- name    : MondererShapley_ClosedPath_IsStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:57.991192+00:00
-- url     : https://prove2.me/theorems/17fed501-1e4b-48ed-b2c7-8dab458403b2
-- title:
--   Genuine unilateral step of a path
-- statement:
--   Profiles $a,b\in Y$ form a **path step** by player $i$ when player $i$ changes strategy and every other player's strategy stays fixed:
--
--   $$b^i\ne a^i,\qquad b^j=a^j\quad(j\ne i).$$
--
--   Thus a step has exactly one deviator. This is the adjacency condition used by every path and by the local exchange in Appendix A.
--
--   **Formalization Note** The player index is supplied explicitly. Its uniqueness follows from the two displayed conditions; null steps are excluded.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 128 (PDF p. 5), definition of a path; https://doi.org/10.1006/game.1996.0044

import Mathlib

namespace MondererShapley.ClosedPath

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- A genuine unilateral deviation by player `i`. -/
def IsStep (a b : ∀ i, Y i) (i : ι) : Prop := b i ≠ a i ∧ ∀ j, j ≠ i → b j = a j

end MondererShapley.ClosedPath


