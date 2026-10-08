-- Prove2me | Definitions.Def_RubinsteinBargaining_PEP_PerfectEquilibrium
-- name    : RubinsteinBargaining_PEP_PerfectEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:28:38.430587+00:00
-- url     : https://prove2.me/theorems/f3a89e2f-67f4-4c1b-8fe8-bbaccbfa5d8b
-- title:
--   Perfect equilibrium in either opening order
-- statement:
--   A strategy pair is a perfect equilibrium when, after every rejected history, the player who responds to its last offer and proposes next has no profitable alternative continuation strategy. If that player plans to accept the last offer, no alternative continuation is preferred to accepting it immediately; if the player plans to reject it, the planned continuation is weakly preferred to immediate acceptance.
--
--   These are conditions (P-1)–(P-6) in a common form for either opening player. They make every possible history relevant, including the empty history, and compare subgame outcomes using time measured from that subgame.
--
--   **Formalization Note** The strategy arguments are the opening and responding roles. At odd-length histories their roles swap in the continuation game. At the empty history the no-profitable-deviation clause applies, while acceptance clauses have no last offer to compare.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 102, Definition (P-1)–(P-6), https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_Game

namespace RubinsteinBargaining.PEP

/-- The player who answers the last offer and, after rejection, proposes next. -/
def actingPlayer (opener : Player) (h : List Partition) : Player :=
  if Even h.length then opener else other opener

def plannedAnswer (f g : Strategy) (h : List Partition) : Bool :=
  if Even h.length then f.answer h else g.answer h

/-- Play from the subgame after all offers in `h` have been rejected.
The new game's time counter starts at period 1. -/
noncomputable def continuation (f g : Strategy) (h : List Partition) : Outcome :=
  if Even h.length then
    play (restrictStrategy f h) (restrictStrategy g h)
  else
    play (restrictStrategy g h) (restrictStrategy f h)

/-- Replace the next proposer/responder's entire continuation strategy. -/
noncomputable def deviation (f g : Strategy) (h : List Partition)
    (d : Strategy) : Outcome :=
  if Even h.length then
    play d (restrictStrategy g h)
  else
    play d (restrictStrategy f h)

/-- Conditions (P-1)–(P-6), including the empty history in (P-4).
`f` is the opening player's strategy and `g` the other player's strategy. -/
noncomputable def IsPE (opener : Player) (p : Preferences)
    (f g : Strategy) : Prop :=
  ∀ h : List Partition,
    (∀ d : Strategy,
      ¬ strict p (actingPlayer opener h) (deviation f g h d)
          (continuation f g h)) ∧
    (∀ s : Partition, h.getLast? = some s →
      if plannedAnswer f g h then
        ∀ d : Strategy,
          ¬ strict p (actingPlayer opener h) (deviation f g h d)
              (agreement s 0)
      else
        weak p (actingPlayer opener h) (continuation f g h)
            (agreement s 0))

end RubinsteinBargaining.PEP


