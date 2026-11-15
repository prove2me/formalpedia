-- Prove2me | Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
-- name    : Kyprianou_Ch03_EntryAndHittingTimes
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T13:27:32.887203+00:00
-- url     : https://prove2.me/theorems/9cc185b1-ba0e-4e12-85ec-10c0a8f77b03
-- title:
--   Extended first entrance and first hitting times
-- statement:
--   Two extended first passage times of a real process: entrance uses times t>=0 and hitting uses times t>0. Both use the infimum in WithTop NNReal and equal infinity when their time set is empty.
-- source:
--   Kyprianou (2006), Chapter 3, unnumbered definitions, printed p. 70.

import Mathlib
set_option autoImplicit false

namespace Kyprianou.Ch03

/-- First entrance, with t >= 0 and an infinite value when there is no entrance. -/
noncomputable def firstEntranceTime
    {Omega : Type} (X : NNReal -> Omega -> Real)
    (B : Set Real) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | X t omega ∈ B})

/-- First hitting, with t > 0 and an infinite value when there is no hit. -/
noncomputable def firstHittingTime
    {Omega : Type} (X : NNReal -> Omega -> Real)
    (B : Set Real) (omega : Omega) : WithTop NNReal :=
  sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
    {t : NNReal | 0 < t ∧ X t omega ∈ B})

end Kyprianou.Ch03


