-- Prove2me | Definitions.Def_MondererShapley_Improvement_G1
-- name    : MondererShapley_Improvement_G1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:16.02348+00:00
-- url     : https://prove2.me/theorems/d174d408-1199-4cc2-887c-c0f6d5041f80
-- title:
--   The two-player game G₁
-- statement:
--   The paper's game $G_1$ has two players and two strategies each. Player 0 chooses row $a$ or $b$; player 1 chooses column $c$ or $d$. The ordered payoff pairs are
--
--   $$
--   G_1=\begin{pmatrix}(1,0)&(2,0)\\(2,0)&(0,1)\end{pmatrix}.
--   $$
--
--   It provides the counterexample showing that the FIP need not yield an ordinal potential, even though Lemma 2.5 gives a generalized ordinal potential.
--
--   **Formalization Note** Each player's strategies are `Fin 2`; index 0 is $a$ or $c$, and index 1 is $b$ or $d$.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 129 (PDF p. 6), displayed game G₁

import Mathlib

namespace MondererShapley.Improvement

/-- The two-player game G₁ displayed on p. 129. Player 0 chooses the row. -/
def G1 : Fin 2 → (Fin 2 → Fin 2) → ℝ := fun i y =>
  ![![![1, 0], ![2, 0]], ![![2, 0], ![0, 1]]] (y 0) (y 1) i

end MondererShapley.Improvement


