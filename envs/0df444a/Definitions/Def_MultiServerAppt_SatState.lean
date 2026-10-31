-- Prove2me | Definitions.Def_MultiServerAppt_SatState
-- name    : MultiServerAppt_SatState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:58.571802+00:00
-- url     : https://prove2.me/theorems/26c90e0e-3abe-4f71-b2dc-f7124dd8725f
-- title:
--   Saturated states of the system
-- statement:
--   A saturated state after client $s+i$ is a pair $(q,m)$ with $q\in\{0,\dots,i-1\}$ and $m:\{1,\dots,s\}\to\iota$. It stands for $j=s+1+q$ clients in the system, so that $q+1\ge 1$ wait, with the $s$ busy servers in phases $m$. These are the blocks $j=s+i,\dots,s+1$ of Eqs. (12), (13) and (16).
--
--   **Formalization Note** The index $q$ replaces $j$, so the type has exactly the $i$ blocks of $S_i^{\mathrm{wait}}$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11, and Eq. (16), p.14

import Mathlib

namespace MultiServerAppt

/-- The saturated states of the system after `s + i` clients have arrived: `(q, m)` means
`j = s + 1 + q` clients are in the system, so `q + 1 ≥ 1` of them wait, and the `s` busy servers are
in the phases `m`. These are the blocks `j = s + i, …, s + 1` of Eqs. (12), (13), (16). Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, p.11 and Eq. (16), p.14.

**Formalization Note** `q : Fin i` replaces `j`, so the type has exactly the `i` blocks of `S_i^wait`
and no truncated subtraction. -/
abbrev SatState (ι : Type*) (s i : ℕ) : Type _ := Fin i × (Fin s → ι)

end MultiServerAppt


