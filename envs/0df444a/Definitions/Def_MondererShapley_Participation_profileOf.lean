-- Prove2me | Definitions.Def_MondererShapley_Participation_profileOf
-- name    : MondererShapley_Participation_profileOf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:07.479511+00:00
-- url     : https://prove2.me/theorems/68767269-c16d-49ea-b200-dcb06d06a7b1
-- title:
--   The profile ε_S of a coalition S (Monderer–Shapley, p. 137)
-- statement:
--   For a coalition $S \subseteq N$, $\varepsilon_S \in Y = \{0,1\}^N$ is the profile in which exactly the members of $S$ participate:
--
--   $$\varepsilon_S^i = \begin{cases} 1 & \text{if } i \in S,\\ 0 & \text{if } i \notin S. \end{cases}$$
--
--   It is introduced in the proof of Theorem 6.1 to write the potential of a participation game as a function of coalitions.
--
--   **Formalization Note** $\{0, 1\}$ is `Bool` (`true` = 1).
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), proof of Theorem 6.1, definition of ε_S

import Mathlib

namespace MondererShapley.Participation

variable {ι : Type*} [DecidableEq ι]

/-- The profile `ε_S` (p. 137): `εⁱ_S = 1` (`true`) if `i ∈ S` and `0` (`false`) otherwise. -/
def profileOf (S : Finset ι) : ι → Bool := fun i => decide (i ∈ S)

end MondererShapley.Participation


