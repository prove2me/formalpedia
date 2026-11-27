-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_V
-- name    : BauerleRiederMDP_LQ_Supplement_JumpMarket_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:18:43.224004+00:00
-- url     : https://prove2.me/theorems/120b7e65-6aad-458e-9136-bf24e8997f87
-- title:
--   The value function of the terminal wealth problem in the pure jump market
-- statement:
--   **The value function of the terminal wealth problem in the pure jump market** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.11), p.281, PDF 291): $V(t, x) := \sup _\pi  V_\pi (t, x)$, the supremum over all predictable portfolio strategies with values in $U$.
--
--   **Formalization Note.** A supremum in `EReal` over `JMStrategy` (all predictable strategies, not only Markov ones).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), eq. (9.11), p.281, PDF 291

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JMStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_JumpMarket_Vstrat

namespace BauerleRiederMDP.LQ.Supplement

/-- **The value function of the terminal wealth problem in the pure jump market** (Bäuerle &
Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (9.11), p.281, PDF 291):
`V(t, x) := sup_π V_π(t, x)`, the supremum over all predictable portfolio strategies with values in
`U`.

**Formalization Note.** A supremum in `EReal` over `JMStrategy` (all predictable strategies, not
only Markov ones). -/
noncomputable def JumpMarket.V {d : ℕ} (Mk : JumpMarket d) (U : ℝ → ℝ) (p : ℝ × ℝ) : EReal :=
  ⨆ R : JMStrategy d, Mk.Vstrat U R p

end BauerleRiederMDP.LQ.Supplement


