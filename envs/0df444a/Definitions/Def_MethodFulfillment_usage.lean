-- Prove2me | Definitions.Def_MethodFulfillment_usage
-- name    : MethodFulfillment_usage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:49.830001+00:00
-- url     : https://prove2.me/theorems/22c565af-c49d-4636-a8ef-8f3d010ac53a
-- title:
--   Units $W^t_{ik}$ of a pair consumed before period $t$
-- statement:
--   For a run $r$, a period $t$ and a pair $(i,k)$, the **usage** $W^t_{ik}$ is the number of periods $s<t$ in which the pair $(i,k)$ was used, i.e. belonged to $m_s\cap A_s$. It is the number of units of item $i$ at facility $k$ consumed before period $t$.
--
--   **Formalization Note** The period $t$ is a natural number, so $t=T$ (the whole horizon) is allowed. With 0-based time, the Lean value at $t$ is the paper's $W^{t+1}_{ik}$.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Appendix D, pp.57–58

import Mathlib
import Definitions.Def_MethodFulfillment_Run

namespace MethodFulfillment

/-- The number of units of inventory `(i, k)` consumed before Lean time `t` in the run `r`
(Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, Appendix D, pp.57–58, "W^t_ik denote
the number of consumed inventory (i,k) … prior to period t"): the number of periods `s < t` whose
used pairs `m ∩ A` contain `(i, k)`.

**Formalization Note.** `t : ℕ`, so `t = T` (the whole horizon) is allowed. With 0-based time,
`usage r t i k` is the paper's `W^{t+1}_{ik}`. -/
def usage {I K Q : Type} [DecidableEq I] [DecidableEq K] {T : ℕ} (r : Run I K Q T) (t : ℕ)
    (i : I) (k : K) : ℕ :=
  (Finset.univ.filter fun s : Fin T => (s : ℕ) < t ∧ (i, k) ∈ (r s).2.1 ∩ (r s).2.2).card

end MethodFulfillment


