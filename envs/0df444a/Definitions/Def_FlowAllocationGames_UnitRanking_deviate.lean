-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_deviate
-- name    : FlowAllocationGames_UnitRanking_deviate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:14.296573+00:00
-- url     : https://prove2.me/theorems/382be792-6db2-4fa4-8047-9fa9473ffb11
-- title:
--   Joint deviation $(a'_C, a_{-C})$ of a coalition
-- statement:
--   For a profile $a$, a coalition $C \subseteq V$ and a profile $a'$, the profile $(a'_C, a_{-C})$ lets every player $v \in C$ play its strategy in $a'$ and every other player its strategy in $a$. Since the strategy of $v$ is the family $(a_e)_{e\in E^+(v)}$, edge $e$ follows $a'_e$ when its tail lies in $C$ and $a_e$ otherwise.
--
--   This is the profile against which profitable deviations of coalitions are measured.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.3, p. 15

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile

namespace FlowAllocationGames.UnitRanking

/-- **Joint deviation of a coalition.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.3, p. 15:
"upon joint deviation of C to a′C, the resulting utility in the new profile (a′C, a−C) …
Here a−C denotes the reduced profile composed of all entries of a except the ones for players
v ∈ C."

`deviate Γ a C a'` is the profile `(a′C, a−C)`: every edge whose tail lies in `C` follows `a'`,
every other edge follows `a`.

**Formalization Note.** A strategy of a player is the family of functions on its outgoing edges,
so replacing the strategies of the players in `C` replaces exactly the functions of the edges with
tail in `C`. -/
def deviate {n m : ℕ} (Γ : Game n m) (a : Profile m) (C : Finset (Fin n)) (a' : Profile m) :
    Profile m :=
  fun e => if Γ.tail e ∈ C then a' e else a e

end FlowAllocationGames.UnitRanking


