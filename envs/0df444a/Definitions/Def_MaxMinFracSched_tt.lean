-- Prove2me | Definitions.Def_MaxMinFracSched_tt
-- name    : MaxMinFracSched_tt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:12.750205+00:00
-- url     : https://prove2.me/theorems/eaf937ae-7c9b-48f9-b14c-8a967ac74387
-- title:
--   Hard family: interval boundaries $t_i$
-- statement:
--   For $k\ge1$ and $0<x<1$, the boundaries of the hard family are
--   $$t_0=0,\qquad t_i=x^{k-i}\quad(1\le i\le k),$$
--   so that $t_k=1$.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31)

import Mathlib

namespace MaxMinFracSched

/-- **The interval boundaries `tᵢ` of the hard family.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 6.1, p.29 (PDF p.31): "Let
t0 := 0, and for 0 < i ≤ k we define ti := x^{k−i}."

`tt x k i = 0` for `i = 0` and `x^{k−i}` otherwise (only used for `i ≤ k`). -/
noncomputable def tt (x : ℝ) (k i : ℕ) : ℝ :=
  if i = 0 then 0 else x ^ (k - i)

end MaxMinFracSched


