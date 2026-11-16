-- Prove2me | Definitions.Def_DRSub4633_Supplement_objCount
-- name    : DRSub4633_Supplement_objCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:29:50.973223+00:00
-- url     : https://prove2.me/theorems/5d3b9736-365b-4c36-ba91-3f155fbfd554
-- title:
--   Number of objective queries in a transcript
-- statement:
--   The number of objective queries in a transcript, that is, the number of value queries plus the number of gradient queries.
--
--   **Formalization Note** Value and gradient queries are counted together. A bound $O(\cdot)$ on their sum is equivalent to the same bound on each of them separately.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Theorem 6.3, p.37

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Query

namespace DRSub4633.Supplement

/-- **Number of objective queries (values and gradients) in a transcript.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Theorem 6.3,
p.37: "exact cube value and gradient queries", "objective queries".

**Formalization Note.** Value and gradient queries are counted together; a bound on the sum is
the same `O(·)` statement as bounds on each. -/
def objCount {n : ℕ} (h : List (Query n × (ℝ × EuclideanSpace ℝ (Fin n)))) : ℕ :=
  h.countP (fun p => match p.1 with
    | .value _ => true
    | .grad _ => true
    | _ => false)

end DRSub4633.Supplement


