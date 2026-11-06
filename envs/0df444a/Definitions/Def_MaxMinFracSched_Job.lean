-- Prove2me | Definitions.Def_MaxMinFracSched_Job
-- name    : MaxMinFracSched_Job
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:11.395022+00:00
-- url     : https://prove2.me/theorems/999b9d72-77ed-4363-a8c7-2d20e36ad55d
-- title:
--   A job $(a_i,d_i,w_i)$ with a label
-- statement:
--   A **job** is a record $(\mathrm{id}, a, d, w)$: a natural-number label, an arrival time $a\in\mathbb R$, a deadline $d\in\mathbb R$ and a work requirement $w\in\mathbb R$ (the processing time needed to complete it).
--
--   Jobs are the input of max-min fractional scheduling: job $i$ is unknown until its arrival time $a_i$, must be processed on a single processor, and only work done before its deadline $d_i$ counts.
--
--   **Formalization Note** The label lets two different jobs share the same $(a,d,w)$, and lets the prefix instances of the hard family be literal subsets of one another. Validity ($a<d$, $w>0$) is imposed separately by `ValidInstance`.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, Main problem definition, p.1 (PDF p.3)

import Mathlib

namespace MaxMinFracSched

/-- **A job** of max-min fractional scheduling. Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, "Main problem definition",
p.1 (PDF p.3): "Each job i has an arrival time ai, a deadline di, and a work requirement wi needed
to complete the job."

A job is a record `⟨id, a, d, w⟩`: a natural-number label `id`, the arrival time `a`, the deadline
`d` and the work requirement `w`.

**Formalization Note.** The label lets two different jobs share the same `(a, d, w)` and lets the
prefix instances of the hard family (Section 6.1) be literal subsets of one another. Times are
arbitrary reals; the paper starts the clock at `0`, and the model is translation invariant. The
validity conditions `a < d`, `0 < w` are imposed by `ValidInstance`, not here. Equality of jobs is
decided classically. -/
structure Job where
  /-- the label of the job -/
  id : ℕ
  /-- the arrival time `aᵢ` -/
  a : ℝ
  /-- the deadline `dᵢ` -/
  d : ℝ
  /-- the work requirement `wᵢ` -/
  w : ℝ

noncomputable instance : DecidableEq Job := Classical.decEq _

end MaxMinFracSched


