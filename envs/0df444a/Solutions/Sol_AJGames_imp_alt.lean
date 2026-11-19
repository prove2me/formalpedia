-- Prove2me | solution 1 for AJGames.imp_alt
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:36:20.961541+00:00
-- url     : https://prove2.me/submissions/5bd079b4-7d46-406f-87b0-624f3a64a08b

import Mathlib
import Definitions.Def_AJGames_Game
import Definitions.Def_AJGames_Tensor

open AJGames in
theorem solution (A B : Game) {s : List (Game.imp A B).M} (h : s ∈ (Game.imp A B).pos) :
    Alt (Game.imp A B).lab s :=
  (Game.imp A B).alt s h
