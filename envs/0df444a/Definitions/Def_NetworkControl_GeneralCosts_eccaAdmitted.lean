-- Prove2me | Definitions.Def_NetworkControl_GeneralCosts_eccaAdmitted
-- name    : NetworkControl_GeneralCosts_eccaAdmitted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:24:44.463986+00:00
-- url     : https://prove2.me/theorems/681e2486-bcaa-4352-a0fd-35abadc24bd0
-- title:
--   ECCA Flow Control rule, p. 114-115
-- statement:
--   The ECCA Flow Control rule (p. 114-115): "we allow the full set of new arrivals $A_i(t)$ into
--   the queue whenever $U_i(t)\le V$. Else, we drop all new arrivals for queue $i$ entering on
--   that timeslot." This is the minimizer of $[U(t)-V]\cdot R(t)$ subject to $0\le R(t)\le A(t)$,
--   stated directly as the book's own if-then rule rather than as an unresolved `argmin`.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, FnT Networking 2006, p. 114-115, ECCA Flow Control

import Mathlib

namespace NetworkControl.GeneralCosts

/-- The ECCA Flow Control rule, p. 114-115: "we allow the full set of new arrivals `A_i(t)` into
the queue whenever `U_i(t) ≤ V`. Else, we drop all new arrivals for queue `i` entering on that
timeslot." This is the minimizer of `[U(t)-V]·R(t)` subject to `0 ≤ R(t) ≤ A(t)`, stated directly
as the book's own if-then rule rather than as an unresolved `argmin`. -/
noncomputable def eccaAdmitted (U V A : ℝ) : ℝ :=
  if U ≤ V then A else 0

end NetworkControl.GeneralCosts


