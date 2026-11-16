-- Prove2me | Definitions.Def_DRSub4633_Supplement_projCount
-- name    : DRSub4633_Supplement_projCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:29:28.848545+00:00
-- url     : https://prove2.me/theorems/f81f5635-c3a5-4f54-81ed-7e8c2def8a50
-- title:
--   Number of projection calls in a transcript
-- statement:
--   The number of projection-oracle queries in a transcript. The paper counts constraint-oracle calls separately from objective queries (p.7).
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, p.7, and Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Query

namespace DRSub4633.Supplement

/-- **Number of projection-oracle calls in a transcript.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, p.7, and
Theorem 6.3, p.37 ("`O(n³ε⁻⁴)` projections"). -/
def projCount {n : ℕ} (h : List (Query n × (ℝ × EuclideanSpace ℝ (Fin n)))) : ℕ :=
  h.countP (fun p => match p.1 with
    | .proj _ => true
    | _ => false)

end DRSub4633.Supplement


