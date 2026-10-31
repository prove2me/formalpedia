-- Prove2me | Definitions.Def_GeomRescale_Mode
-- name    : GeomRescale_Mode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:11.973326+00:00
-- url     : https://prove2.me/theorems/f3bdd5ee-e71e-416a-a43f-10927835ed98
-- title:
--   The control point of Algorithm 2
-- statement:
--   The control point of Rescaling-SFM is one of: before lines 2–3; the head of the `for` loop (line 4); inside the call of line 5; line 6; or finished with a returned set $W$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10

import Mathlib

namespace GeomRescale

/-- The control point of Algorithm Rescaling-SFM (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 2, p.10): `start` is before
lines 2–3, `head` is at line 4, `inner` is inside the call of line 5, `afterCall` is at line 6, and
`done W` means that `W` was returned. -/
inductive Mode (n : ℕ) where
  | start
  | head
  | inner
  | afterCall
  | done (W : Finset (Fin n))

end GeomRescale


