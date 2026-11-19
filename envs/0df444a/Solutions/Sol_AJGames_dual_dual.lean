-- Prove2me | solution 1 for AJGames.dual_dual
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:33:49.429091+00:00
-- url     : https://prove2.me/submissions/e3a7e175-42c1-42e4-8dac-f592e4b63da5

import Mathlib
import Definitions.Def_AJGames_Game

theorem solution (A : AJGames.Game) : A.dual.dual = A := by
  cases A
  simp only [AJGames.Game.dual, AJGames.Pl.flip_flip]
