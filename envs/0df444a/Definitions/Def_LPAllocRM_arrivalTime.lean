-- Prove2me | Definitions.Def_LPAllocRM_arrivalTime
-- name    : LPAllocRM_arrivalTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:07.497982+00:00
-- url     : https://prove2.me/theorems/5e310863-a1c0-4114-a607-cfc44d727cbf
-- title:
--   Arrival time of the $i$-th class-$j$ request
-- statement:
--   For an arrival path $d$, a class $j$ and $i\ge 1$, the time of the $i$-th class-$j$ arrival is
--
--   $$T_{j,i}(d)=\inf\{t\in\mathbb R : d_j(t)\ge i\}.$$
--
--   It is an auxiliary notion used to evaluate the integral (2) on counting paths.
--
--   **Formalization Note** For $1\le i\le d_j(\tau)$ on an arrival path the set is nonempty and bounded below and the infimum is attained (right-continuity). Outside that range Lean's real infimum returns the default value $0$; the count of accepted customers only evaluates it for $1\le i\le d_j(\tau)$.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, §2, eq. (2), p.722 (auxiliary)

import Mathlib

namespace LPAllocRM

/-- The time of the `i`-th class-`j` arrival on the counting path `d`:
`arrivalTime d j i = inf {t : i ≤ d t j}`.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
§2, p.722 (PDF p.3), auxiliary to the integral (2).

**Formalization Note** For an arrival path (`IsArrivalPath`) and `1 ≤ i ≤ d τ j` the set is
nonempty (it contains `τ`) and bounded below (by `0`), and the infimum is attained by
right-continuity, so this is the `i`-th arrival time. Outside that range Lean's real `sInf` returns
`0` (empty set when `i > d τ j`, unbounded set when `i = 0`); `accepted` only evaluates it for
`1 ≤ i ≤ d τ j`. -/
noncomputable def arrivalTime {n : ℕ} (d : ℝ → Fin n → ℕ) (j : Fin n) (i : ℕ) : ℝ :=
  sInf {t : ℝ | i ≤ d t j}

end LPAllocRM


