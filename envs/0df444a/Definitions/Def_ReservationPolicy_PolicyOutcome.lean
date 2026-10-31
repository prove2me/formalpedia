-- Prove2me | Definitions.Def_ReservationPolicy_PolicyOutcome
-- name    : ReservationPolicy_PolicyOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:19.822508+00:00
-- url     : https://prove2.me/theorems/f6d6a4a8-361f-47ed-b78c-4a5331e3c674
-- title:
--   Outcome under a seat transfer
-- statement:
--   Under a seat transfer the two types face different cutoffs. An outcome records the efforts $e_{x,s},e_{y,s}$, the cutoffs $d_x,d_y$ and the rewards $r_{x,s},r_{y,s}$.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), §4, pp.18–20

import Mathlib

namespace ReservationPolicy

/-- An outcome of the game under a seat transfer: the efforts `ex`, `ey`, the group cutoffs `dx`, `dy`
and the rewards `rx`, `ry`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), §4, pp.18–20
(PDF 18–20). -/
@[ext] structure PolicyOutcome where
  ex : ℝ
  ey : ℝ
  dx : ℝ
  dy : ℝ
  rx : ℝ
  ry : ℝ

end ReservationPolicy


