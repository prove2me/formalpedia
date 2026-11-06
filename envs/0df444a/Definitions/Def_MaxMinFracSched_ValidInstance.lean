-- Prove2me | Definitions.Def_MaxMinFracSched_ValidInstance
-- name    : MaxMinFracSched_ValidInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:58.777022+00:00
-- url     : https://prove2.me/theorems/9e2f5190-b0de-4505-9f19-4109779fcd79
-- title:
--   Valid instance: nonempty, $a_i<d_i$ and $w_i>0$
-- statement:
--   An **instance** $J$ is a finite set of jobs. It is **valid** when $J\neq\emptyset$ and every job $i\in J$ satisfies
--   $$a_i<d_i\qquad\text{and}\qquad w_i>0 .$$
--
--   These are the paper's standing assumptions on jobs ("We assume throughout that $w_i>0$ and $a_i<d_i$ for every job", Section 8.1). They make the offline optimum positive and the fractional completions well defined.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3) and Section 8.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job

namespace MaxMinFracSched

/-- **A valid instance.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1, p.1 (PDF p.3): "The input is a set J of n jobs", and
Section 8.1, p.40 (PDF p.42): "We assume throughout that wi > 0 and ai < di for every job".

An instance is a finite set of jobs; it is valid when it is nonempty and every job `j` has
`j.a < j.d` and `0 < j.w`.

**Formalization Note.** Nonemptiness makes the minimum fractional completion `minFrac` a genuine
minimum (an `iInf` over an empty index is `0` in `ℝ`); `a < d` and `0 < w` make the offline
optimum positive and the fractional completion well defined. -/
def ValidInstance (J : Finset Job) : Prop :=
  J.Nonempty ∧ ∀ j ∈ J, j.a < j.d ∧ 0 < j.w

end MaxMinFracSched


