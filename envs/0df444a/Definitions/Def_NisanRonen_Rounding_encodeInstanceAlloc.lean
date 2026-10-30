-- Prove2me | Definitions.Def_NisanRonen_Rounding_encodeInstanceAlloc
-- name    : NisanRonen_Rounding_encodeInstanceAlloc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:23:03.776085+00:00
-- url     : https://prove2.me/theorems/3f22d62d-6570-46d2-86f6-f298b4296127
-- title:
--   Binary encoding of a rounded instance with an allocation
-- statement:
--   A pair consisting of a rounded instance in $\delta$-units and an allocation (a list of agents, one per task) is written as the binary encoding of the instance followed by the list of agents, each agent a single letter of the finite alphabet $\{1, \dots, n\}$ (finite because $n$ is fixed).
--
--   This is the input encoding in which "polynomial time" is measured for the bonus computation.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, Definition 34 and Theorem 5.9, p. 193 (PDF p. 28)

import Mathlib
import Definitions.Def_NisanRonen_Rounding_encodeInstance

namespace NisanRonen.Rounding

/-- **Encoding of an instance together with an allocation** (cost model for the bonus
computation, Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), Definition 34 and Theorem 5.9, p. 193). The δ-unit instance is
encoded by `encodeInstance` (letters `Sum.inl`), followed by the allocation as a list of agents
(letters `Sum.inr`, alphabet `Fin n`, finite because `n` is fixed). -/
def encodeInstanceAlloc {n : ℕ} (p : List (Fin n → ℕ) × List (Fin n)) :
    List (Computability.Γ' ⊕ Fin n) :=
  (encodeInstance p.1).map Sum.inl ++ p.2.map Sum.inr

end NisanRonen.Rounding


