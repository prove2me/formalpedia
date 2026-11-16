-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_contract
-- name    : MaxMinFracSched_Supplement_contract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:17:03.489195+00:00
-- url     : https://prove2.me/theorems/67ffb40b-9aca-4848-b019-4afbf2b9d45e
-- title:
--   Contracted instance $J-I^{\star}$
-- statement:
--   The **contracted instance** $J-I^{\star}$ is obtained from $J$ by deleting the jobs of $S_J(I^{\star})$, which lie inside densest intervals, and replacing every other job by its corresponding job $(\mathrm{id},\tau(a_j),\tau(d_j),w_j)$, where $\tau$ contracts all densest intervals.
--
--   The recursion behind the lexicographic optimum works on this instance (Theorem 7.3).
--
--   **Formalization Note** The map keeps the label, so on an instance whose jobs have pairwise distinct labels no two surviving jobs become the same element of the set.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 7.2, p.33 (PDF p.35); Theorem 7.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_Supplement_densestCovered
import Definitions.Def_MaxMinFracSched_Supplement_contractMap

namespace MaxMinFracSched

namespace Supplement

/-- **The contracted instance `J − I⋆`.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 7.2, p.33 (PDF p.35): "First, delete every job of J with L ≤ ai ≤ di ≤ R. …
Second, delete I from the time axis"; Theorem 7.3, p.34 (PDF p.36).

Delete the jobs of `S_J(I⋆)` (`densestCovered J`) and map every other job to its corresponding job
`contractMap J j`.

**Formalization Note.** The map keeps the job label, so it is injective on jobs with pairwise
distinct labels (the paper's job indices), the hypothesis under which Theorem 7.3 is stated; then
no two surviving jobs merge into one element of the finite set. -/
noncomputable def contract (J : Finset Job) : Finset Job :=
  (J.filter (fun j => j ∉ densestCovered J)).image (contractMap J)

end Supplement

end MaxMinFracSched


