-- Prove2me | Definitions.Def_MethodFulfillment_pa
-- name    : MethodFulfillment_pa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:51.348196+00:00
-- url     : https://prove2.me/theorems/47631e3a-af5c-48ed-9271-01c55f5d0bdd
-- title:
--   Aggregate arrival probability $p_a(q)=\sum_t p_t(q)$
-- statement:
--   For an order type $q$, the **aggregate arrival probability** is
--   $$p_a(q)=\sum_{t\in[T]}p_t(q),$$
--   the expected number of arrivals of type $q$ over the horizon. It is the right-hand side of constraint (7) of the expected LP and the normalizer in the aggregation (10).
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), below (9), p.11

import Mathlib
import Definitions.Def_MethodFulfillment_Instance

namespace MethodFulfillment

/-- The aggregate arrival probability `pa(q) = ∑_{t ∈ [T]} p_t(q)` (Amil, Makhdoumi & Wei,
manuscript, PDF sha256 197c13b9…, below (9), p.11). -/
def pa {I K Q : Type} {T : ℕ} (P : Instance I K Q T) (q : Q) : ℝ :=
  ∑ t, P.p t q

end MethodFulfillment


