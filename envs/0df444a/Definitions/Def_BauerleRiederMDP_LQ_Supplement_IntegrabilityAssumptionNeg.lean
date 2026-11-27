-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_IntegrabilityAssumptionNeg
-- name    : BauerleRiederMDP_LQ_Supplement_IntegrabilityAssumptionNeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:09:36.75444+00:00
-- url     : https://prove2.me/theorems/ca05985c-15d5-5196-811e-3b24e0e1c4dc
-- title:
--   The Integrability Assumption (A) of §7.4 (positive models)
-- statement:
--   **The Integrability Assumption (A) of §7.4 (positive models)** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §7.4, p.208, PDF 219): $\varepsilon (x) = \sup _\pi  \mathbb E ^\pi _x [\sum _{k=0}^\infty  \beta ^k r^-(X_k, f_k(X_k))] < \infty $ for all $x \in  E$.
--
--   **Formalization Note.** $\varepsilon $ is `epsNeg`; the strict inequality is in `EReal`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.4, p.208, PDF 219

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_epsNeg

open MDPFinance.Contracting

namespace BauerleRiederMDP.LQ.Supplement

/-- **The Integrability Assumption (A) of §7.4 (positive models)** (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §7.4, p.208, PDF 219):
`ε(x) = sup_π 𝔼^π_x [∑_{k=0}^∞ β^k r^−(X_k, f_k(X_k))] < ∞` for all `x ∈ E`.

**Formalization Note.** `ε` is `epsNeg`; the strict inequality is in `EReal`. -/
def IntegrabilityAssumptionNeg {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) : Prop :=
  ∀ x, epsNeg M x < ⊤

end BauerleRiederMDP.LQ.Supplement


