-- Prove2me | Definitions.Def_TransitoryQueue_load
-- name    : TransitoryQueue_load
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:09.527606+00:00
-- url     : https://prove2.me/theorems/68dfc34c-e6e0-4eea-b107-4dc8d3aeb242
-- title:
--   The cumulative offered load $W_n(t)=\sum_{i=1}^{A_n(t)}V_i$
-- statement:
--   With service requirements $V_1,\dots,V_n$ ($V_i$ belongs to the $i$-th customer to turn up), the **cumulative offered load** (4) is
--
--   $$W_n(t)=\sum_{i=1}^{A_n(t)}V_i,$$
--
--   the total work brought to the server by time $t$.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eq. (4), p.6

import Mathlib
import Definitions.Def_TransitoryQueue_arrivals

namespace TransitoryQueue

/-- The cumulative offered load (4): `W_n(t) = Σ_{i=1}^{A_n(t)} V_i`, the total service
requirement of the customers who have turned up by time `t`; `V_i` is the requirement of the
`i`-th customer to turn up. Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eq. (4), p.6.

**Formalization Note** `Σ_{i=1}^{m}` is the sum over `i : Fin n` with `i.val < m`. -/
noncomputable def load {n : ℕ} (T : Fin n → ℝ) (ζ : Fin n → ℕ) (V : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin n with i.val < arrivals T ζ t, V i

end TransitoryQueue


