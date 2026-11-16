-- Prove2me | Definitions.Def_DRSub4633_Supplement_lmoCount
-- name    : DRSub4633_Supplement_lmoCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:29:04.920103+00:00
-- url     : https://prove2.me/theorems/43ff1f61-b06f-4809-b089-d97673fc59a8
-- title:
--   Number of LMO calls in a transcript
-- statement:
--   The number of linear maximization oracle queries in a transcript. The paper counts constraint-oracle calls separately from objective queries (p.7).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, p.7, and Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Query

namespace DRSub4633.Supplement

/-- **Number of LMO calls in a transcript.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, p.7: "Constraint-oracle calls
are counted separately from objective queries". -/
def lmoCount {n : ℕ} (h : List (Query n × (ℝ × EuclideanSpace ℝ (Fin n)))) : ℕ :=
  h.countP (fun p => match p.1 with
    | .lmo _ => true
    | _ => false)

end DRSub4633.Supplement


