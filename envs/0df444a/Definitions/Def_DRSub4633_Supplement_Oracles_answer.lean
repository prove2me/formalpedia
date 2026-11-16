-- Prove2me | Definitions.Def_DRSub4633_Supplement_Oracles_answer
-- name    : DRSub4633_Supplement_Oracles_answer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:26:37.845121+00:00
-- url     : https://prove2.me/theorems/82070350-8253-4863-95e6-45c00a801ccd
-- title:
--   The answer to one oracle query
-- statement:
--   For an oracle bundle $O$ and a query $q$, the answer is a pair (scalar, vector): $(f(y),0)$ for a value query at $y$, $(0,\nabla f(y))$ for a gradient query at $y$, $(0,z(c))$ for an LMO query in direction $c$, and $(0,\Pi_{K_W}(v))$ for a projection query at $v$.
--
--   **Formalization Note** A single answer type serves all four kinds of query; the unused component is $0$ and carries no information.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 3.1, pp.7–8

import Mathlib
import Definitions.Def_DRSub4633_Supplement_Query
import Definitions.Def_DRSub4633_Supplement_Oracles

namespace DRSub4633.Supplement

/-- **The answer to one query.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 3.1, pp.7–8.

`O.answer q` is the pair `(scalar, vector)` returned for the query `q`: `(f(y), 0)` for a value
query, `(0, ∇f(y))` for a gradient query, `(0, z)` for an LMO or projection query with `z` the
oracle's selection.

**Formalization Note.** One answer type for all queries; the unused component is `0` and carries
no information. -/
def Oracles.answer {n : ℕ} (O : Oracles n) : Query n → ℝ × EuclideanSpace ℝ (Fin n)
  | .value y => (O.val y, 0)
  | .grad y => (0, O.grad y)
  | .lmo c => (0, O.lmo c)
  | .proj v => (0, O.proj v)

end DRSub4633.Supplement


