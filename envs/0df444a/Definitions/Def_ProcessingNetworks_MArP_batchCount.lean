-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_batchCount
-- name    : ProcessingNetworks_MArP_batchCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:25.932548+00:00
-- url     : https://prove2.me/theorems/c91a4d22-3b32-4a3c-8eea-ddbc27ff1106
-- title:
--   The total batch count $A_k(t)$ (eq. (E.1))
-- statement:
--   The total number of batch arrivals with configuration $\delta^k$ up to time $t$ is
--   $$
--   A_k(t)=\sum_{s\in\mathcal S}\xi^k\big(\beta_k(s)T(s,t)\big)+\sum_{s,\tilde s\in\mathcal S}J_k(s,\tilde s,t),
--   $$
--   the first sum counting spontaneous arrivals and the second triggered arrivals.
--
--   **Formalization Note** This is (E.1) as printed, with the same process $\xi^k$ in every term of the first sum.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), eq. (E.1), p.305 (PDF p.321)

import Mathlib
import Definitions.Def_ProcessingNetworks_MArP_occupationTime
import Definitions.Def_ProcessingNetworks_MArP_triggeredCount

open MeasureTheory

namespace ProcessingNetworks.MArP

/-- The total number of batch arrivals with configuration `δᵏ` up to time `t`, eq. (E.1) (Dai &
Harrison, Processing Networks, pre-publication draft 2020-4-2, p.305, PDF p.321):
`A_k(t) = ∑_{s} ξᵏ(β_k(s) T(s, t)) + ∑_{s, s̃} J_k(s, s̃, t)`.

**Formalization Note.** This is (E.1) as printed: the same process `ξᵏ` appears in every term of the
first sum. -/
noncomputable def batchCount {I d r : ℕ} {D : MArPData I d r} {Ω : Type*} [MeasureSpace Ω]
    (P : MArPPrimitives D Ω) (k : Fin r) (t : ℝ) (ω : Ω) : ℕ :=
  ∑ s, P.ξ k (D.β k s * occupationTime P.Y s t ω) ω + ∑ s, ∑ s', triggeredCount P k s s' t ω

end ProcessingNetworks.MArP


