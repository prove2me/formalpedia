-- Prove2me | Definitions.Def_NashOrTriangle_inputH
-- name    : NashOrTriangle_inputH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:37.972205+00:00
-- url     : https://prove2.me/theorems/0a5e38af-b9e3-4637-9187-fa61e8f74578
-- title:
--   Input of the algorithm $A_h$
-- statement:
--   The input of the algorithm of Lemma C.1 run with accuracy $h$: memory cell $0$ holds $h$, all other cells hold $0$.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Lemma C.1, p.24 (PDF p.25)

import Mathlib

namespace NashOrTriangle

/-- The input memory of the algorithm of Lemma C.1 run with accuracy `h`: cell `0` holds `h`,
all other cells `0`.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Lemma C.1, printed p. 24 (PDF p. 25). -/
noncomputable def inputH (h : ℝ) : ℤ → ℝ :=
  fun i => if i = 0 then h else 0

end NashOrTriangle


