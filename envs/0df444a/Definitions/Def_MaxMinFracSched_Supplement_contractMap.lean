-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_contractMap
-- name    : MaxMinFracSched_Supplement_contractMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:16:16.467199+00:00
-- url     : https://prove2.me/theorems/5325f22a-45b6-4b64-9ad2-cb9d22586ee0
-- title:
--   Corresponding job in the contracted instance
-- statement:
--   The job corresponding to $j=(\mathrm{id},a_j,d_j,w_j)$ in the contracted instance is
--   $$
--   \bigl(\mathrm{id},\ \tau(a_j),\ \tau(d_j),\ w_j\bigr),
--   $$
--   with the same label and work, and its arrival time and deadline mapped by the contraction $\tau$ of all densest intervals.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Definition 7.2, p.33 (PDF p.35); Theorem 7.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_Supplement_contractTime

namespace MaxMinFracSched

namespace Supplement

/-- **The corresponding job in the contracted instance.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Definition 7.2, p.33 (PDF p.35): "each surviving job i becomes the job (τI(ai), τI(di), wi)";
Theorem 7.3, p.34 (PDF p.36): "the corresponding job in the contracted instance J−I⋆".

The job with the same label and work, whose arrival time and deadline are mapped by
`contractTime J`. -/
noncomputable def contractMap (J : Finset Job) (j : Job) : Job :=
  ⟨j.id, contractTime J j.a, contractTime J j.d, j.w⟩

end Supplement

end MaxMinFracSched


