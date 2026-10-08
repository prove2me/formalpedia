-- Prove2me | Definitions.Def_RubinsteinBargaining_PEP_Game
-- name    : RubinsteinBargaining_PEP_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:12:34.245982+00:00
-- url     : https://prove2.me/theorems/375617bc-9a9c-4062-8ed1-72042db6b1e4
-- title:
--   Alternating-offer strategies, histories, and play
-- statement:
--   A strategy specifies an offer after every history of rejected offers and an accept-or-reject response after every history containing a current offer. Starting with an opening strategy $f$ and a responding strategy $g$, the players alternate offers. The first accepted offer $s$ in period $t$ yields $(s,t)$; an endless sequence of rejections yields perpetual disagreement.
--
--   The sequence of offers, first acceptance time, agreement time $T$, and final partition $D$ are defined from these strategies. Restricting a strategy to a rejected history appends each future history to it. These objects permit the paper's equilibrium conditions to be stated at every possible subgame.
--
--   **Formalization Note** Periods are numbered from 1 in play, while comparison outcomes may use period 0. $D$ and $T$ are optional, with no default partition at perpetual disagreement.
-- source:
--   Rubinstein, Perfect Equilibrium in a Bargaining Model, Econometrica 50 (1982), p. 100, Section 2; p. 102, Section 3, https://doi.org/10.2307/1912531

import Definitions.Def_RubinsteinBargaining_PEP_Core

namespace RubinsteinBargaining.PEP

/-- A history-dependent strategy. `offer` is used after rejected offers; `answer`
is used on a history including the current offer. Unused parities have no effect. -/
structure Strategy where
  offer : List Partition → Partition
  answer : List Partition → Bool

def restrictStrategy (f : Strategy) (h : List Partition) : Strategy where
  offer := fun future => f.offer (h ++ future)
  answer := fun future => f.answer (h ++ future)

/-- `f` opens the game and `g` answers the first offer. -/
def nextOffer (f g : Strategy) (h : List Partition) : Partition :=
  if Even h.length then f.offer h else g.offer h

/-- The first `n` offers, computed without stopping at acceptance. -/
def offers (f g : Strategy) : ℕ → List Partition
  | 0 => []
  | n + 1 =>
      let h := offers f g n
      h ++ [nextOffer f g h]

/-- Whether the offer in period `n+1` is accepted. -/
def acceptedAt (f g : Strategy) (n : ℕ) : Prop :=
  let h := offers f g (n + 1)
  if Even n then g.answer h = true else f.answer h = true

/-- The period of the first acceptance, if any. -/
noncomputable def firstAcceptance (f g : Strategy) : Option ℕ :=
  by
    classical
    exact if h : ∃ n, acceptedAt f g n then some (Nat.find h) else none

/-- The play outcome; the first offer accepted in index `n` is agreed in period `n+1`. -/
noncomputable def play (f g : Strategy) : Outcome :=
  match firstAcceptance f g with
  | none => none
  | some n => agreement (nextOffer f g (offers f g n)) (n + 1)

/-- The agreement period, or `none` for perpetual disagreement. -/
noncomputable def T (f g : Strategy) : Option ℕ :=
  (play f g).map Prod.snd

/-- The final partition, or `none` for perpetual disagreement. -/
noncomputable def D (f g : Strategy) : Option Partition :=
  (play f g).map Prod.fst

end RubinsteinBargaining.PEP


