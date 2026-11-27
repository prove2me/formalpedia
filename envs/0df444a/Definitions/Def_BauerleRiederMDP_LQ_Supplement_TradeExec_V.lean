-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_V
-- name    : BauerleRiederMDP_LQ_Supplement_TradeExec_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:40:55.300934+00:00
-- url     : https://prove2.me/theorems/fda99284-c530-4a1c-b5c6-ec5192afcd34
-- title:
--   The value function of the trade execution problem
-- statement:
--   **The value function of the trade execution problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.4, p.294, PDF 304): $V(t, x) := \inf _\pi  V_\pi (t, x)$, $(t, x) \in  [0, T] \times  \mathbb N _0 =: E$, the infimum over all admissible (predictable) control processes.
--
--   **Formalization Note.** An infimum in $[0, \infty ]$ over `TradeStrategy`; it is not defined as the value of the discrete-time model.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.4, p.294, PDF 304

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_TradeExec_Vstrat

namespace BauerleRiederMDP.LQ.Supplement

/-- **The value function of the trade execution problem** (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §9.4, p.294, PDF 304):
`V(t, x) := inf_π V_π(t, x)`, `(t, x) ∈ [0, T] × ℕ_0 =: E`, the infimum over all admissible
(predictable) control processes.

**Formalization Note.** An infimum in `[0, ∞]` over `TradeStrategy`; it is not defined as the value
of the discrete-time model. -/
noncomputable def TradeExec.V (P : TradeExec) (p : ℝ × ℕ) : ENNReal :=
  ⨅ g : TradeStrategy, P.Vstrat g p

end BauerleRiederMDP.LQ.Supplement


