-- Prove2me | Definitions.Def_TIESharp_slotStart
-- name    : TIESharp_slotStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:59.522756+00:00
-- url     : https://prove2.me/theorems/70779526-2242-4d9d-9126-19ba7d18bdfc
-- title:
--   Start of a job's interval in a machine's slot list
-- statement:
--   At machine $i$, the jobs with $q_{ij}>0$ are sorted by decreasing $t_{ij}$, ties broken by job index, and intervals of lengths $q_{ij}$ are laid end to end in that order. Job $j$ occupies $[c_{ij},c_{ij}+q_{ij})$ where
--   $$c_{ij}=\sum_{j':\,q_{ij'}>0,\ (t_{ij'}>t_{ij})\text{ or }(t_{ij'}=t_{ij},\ j'<j)}q_{ij'} .$$
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10

import Mathlib
import Definitions.Def_TIESharp_bsProb

set_option autoImplicit false

namespace TIESharp

/-- The **left end of job `j`'s interval on machine `i`** in the slot construction (Li, *Sharp
Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10): "At machine i, sort
jobs with q_ij > 0 by decreasing t_ij, breaking ties by job index. Lay intervals of lengths q_ij end
to end in that order". Job `j` occupies `[c, c + q_ij)` where `c` is the total length of the jobs
`j'` with `q_ij' > 0` placed before it, i.e. with `t_ij' > t_ij`, or `t_ij' = t_ij` and `j' < j`.

**Formalization Note.** `q` is the Bounded-Square probability `bsProb`; the tie-break is by the
0-based job index. -/
noncomputable def slotStart {n m : ℕ} (t : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  ∑ j' ∈ Finset.univ.filter
      (fun j' => 0 < bsProb t i j' ∧ (t i j < t i j' ∨ (t i j' = t i j ∧ j' < j))),
    bsProb t i j'

end TIESharp


