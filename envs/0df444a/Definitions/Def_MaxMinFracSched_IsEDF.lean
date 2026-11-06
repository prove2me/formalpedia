-- Prove2me | Definitions.Def_MaxMinFracSched_IsEDF
-- name    : MaxMinFracSched_IsEDF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:12.018644+00:00
-- url     : https://prove2.me/theorems/ae740621-bb2c-4a57-8610-e88ecfc0c8aa
-- title:
--   EDF run
-- statement:
--   An **EDF run** on the instance $J$ is a threshold-EDF run with thresholds $\theta_j(t)=w_j$: at almost every time it works on an incomplete, released, unexpired job of earliest deadline (ties broken arbitrarily), and idles if there is none.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 1.2, p.2 (PDF p.4); Lemma 3.3, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_IsThresholdEDF

namespace MaxMinFracSched

/-- **An EDF run.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 1.2, p.2 (PDF p.4): "earliest deadline first (EDF) where the
processor simply works on the incomplete job with earliest deadline", used in Lemma 3.3, p.12.

A threshold-EDF run with threshold `w_j`: at almost every time it serves an incomplete,
released, unexpired job of earliest deadline (ties broken arbitrarily), and idles if there is
none. -/
def IsEDF (J : Finset Job) (r : Job → ℝ → ℝ) : Prop :=
  IsThresholdEDF J (fun j _ => j.w) r

end MaxMinFracSched


