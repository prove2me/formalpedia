-- Prove2me | Definitions.Def_MondererShapley_Participation_joiners
-- name    : MondererShapley_Participation_joiners
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:14.157008+00:00
-- url     : https://prove2.me/theorems/ce7d02c6-94d1-4400-88dd-41d81683ecde
-- title:
--   The set S(ε) of participating players (Monderer–Shapley, p. 137)
-- statement:
--   For a profile $\varepsilon \in Y = \{0, 1\}^N$ of the participation game, the set of participating players is
--
--   $$S(\varepsilon) = \{ i \in N : \varepsilon^i = 1 \}.$$
--
--   **Formalization Note** The strategy set $\{0, 1\}$ is `Bool`, with `false` for 0 (not joining) and `true` for 1 (joining); the player type `ι` is finite.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 137 (PDF p. 14), definition of S(ε)

import Mathlib

namespace MondererShapley.Participation

variable {ι : Type*} [Fintype ι]

/-- `S(ε) = {i ∈ N : εⁱ = 1}` (p. 137), the players choosing to participate; strategy `1` is
`true`, strategy `0` is `false`. -/
def joiners (ε : ι → Bool) : Finset ι := Finset.univ.filter (fun i => ε i = true)

end MondererShapley.Participation


