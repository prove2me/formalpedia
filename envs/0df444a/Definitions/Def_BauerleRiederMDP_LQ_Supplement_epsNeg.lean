-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_epsNeg
-- name    : BauerleRiederMDP_LQ_Supplement_epsNeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:09:02.2138+00:00
-- url     : https://prove2.me/theorems/e9e232d0-0c12-545c-9c14-a45a03005910
-- title:
--   The bound $\varepsilon $ of the Integrability Assumption (A) for positive models
-- statement:
--   **The bound $\varepsilon $ of the Integrability Assumption (A) for positive models** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §7.4, p.208, PDF 219): $\varepsilon (x) := \sup _\pi  \mathbb E ^\pi _x [\sum _{k=0}^\infty  \beta ^k r^-(X_k, f_k(X_k))]$, the supremum over all Markov policies $\pi  = (f_0, f_1, \dots ) \in  F^\infty $.
--
--   **Formalization Note.** The model is the published infinite-horizon `MDPFinance.Contracting` model. For a policy $\pi $ the expectation of the discounted sum of the negative parts $r^- = \max (-r, 0) \ge  0$ is the published `Jinfpi M r⁻ π x`, the limit of the $n$-stage expectations (an increasing sequence of $[0, \infty ]$-values, so the limit exists and equals the expectation of the infinite sum by monotone convergence). The value lies in $[0, \infty ]$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.4, p.208, PDF 219

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value

open MeasureTheory ProbabilityTheory Filter
open MDPFinance.Contracting

namespace BauerleRiederMDP.LQ.Supplement

/-- **The bound `ε` of the Integrability Assumption (A) for positive models** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), §7.4, p.208, PDF 219):
`ε(x) := sup_π 𝔼^π_x [∑_{k=0}^∞ β^k r^−(X_k, f_k(X_k))]`, the supremum over all Markov policies
`π = (f_0, f_1, …) ∈ F^∞`.

**Formalization Note.** The model is the published infinite-horizon `MDPFinance.Contracting`
model. For a policy `π` the expectation of the discounted sum of the negative parts
`r^− = max(−r, 0) ≥ 0` is the published `Jinfpi M r⁻ π x`, the limit of the `n`-stage expectations
(an increasing sequence of `[0, ∞]`-values, so the limit exists and equals the expectation of the
infinite sum by monotone convergence). The value lies in `[0, ∞]`. -/
noncomputable def epsNeg {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicyOf M π}, Jinfpi M (fun p => max (-M.r p) 0) π x

end BauerleRiederMDP.LQ.Supplement


