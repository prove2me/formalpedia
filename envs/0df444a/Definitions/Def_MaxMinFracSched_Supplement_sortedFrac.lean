-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_sortedFrac
-- name    : MaxMinFracSched_Supplement_sortedFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:12:21.109185+00:00
-- url     : https://prove2.me/theorems/10102929-704e-4c82-ae62-6943b353fecd
-- title:
--   Sorted fraction vector $f^{\uparrow}_J$
-- statement:
--   For a schedule $r$ of an instance $J$ with $|J|=n$, the **sorted fraction vector** $f^{\uparrow}_J$ is the list $(f_{(1)},\dots,f_{(n)})$ of the fractional completions $f_j=\min(w_j,c_j)/w_j$, $j\in J$, sorted in nondecreasing order. A value shared by several jobs appears once for each of them.
--
--   The lexicographic objective (Section 7) compares schedules through this vector.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 7, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_work
import Definitions.Def_MaxMinFracSched_frac

namespace MaxMinFracSched

namespace Supplement

/-- **The sorted fraction vector `f↑_J`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 7, p.33 (PDF p.35): "consider an instance J with |J| = n jobs. For any scheduler, let
f↑J := (f1, f2, . . . , fn) denote its fractional completions, sorted in nondecreasing order."

`sortedFrac J r` is the list of the fractional completions `frac r j`, `j ∈ J`, sorted in
nondecreasing order; it has length `|J|` (a value shared by several jobs appears with its
multiplicity). -/
noncomputable def sortedFrac (J : Finset Job) (r : Job → ℝ → ℝ) : List ℝ :=
  (J.val.map (frac r)).sort (· ≤ ·)

end Supplement

end MaxMinFracSched


