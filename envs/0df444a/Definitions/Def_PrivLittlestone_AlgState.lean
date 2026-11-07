-- Prove2me | Definitions.Def_PrivLittlestone_AlgState
-- name    : PrivLittlestone_AlgState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:06.902747+00:00
-- url     : https://prove2.me/theorems/f531ea7b-4e80-4cea-a08b-c926967ea8d2
-- title:
--   Internal state of Algorithm 1
-- statement:
--   The **internal state of Algorithm 1** between rounds consists of the phase index $j$, the round at which the current phase started, the retained sequence $S$, the phase counter $c$, the currently released classifier $g$ (the phase aggregate, or $g_{\mathrm{fb}}$ after the cap), and whether the public fallback is active. None of it except the released classifier is published.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, p.7

import Mathlib

namespace PrivLittlestone

/-- The **internal state of Algorithm 1** between rounds (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Algorithm 1, p.7): the 0-based phase index `j`, the round at which the current phase started,
the retained sequence `S`, the phase counter `c`, the current classifier `g` (the phase aggregate,
or `g_fb` after the phase cap) and whether the public fallback is active. -/
structure AlgState (X Z : Type*) where
  /-- the 0-based phase index -/
  phase : ℕ
  /-- the 0-based round at which the current phase started -/
  start : ℕ
  /-- the retained sequence `S` -/
  retained : List Z
  /-- the phase counter `c` -/
  counter : ℕ
  /-- the classifier released while this state is current -/
  current : X → Bool
  /-- whether the public fallback after the phase cap is active -/
  fallback : Bool

end PrivLittlestone


