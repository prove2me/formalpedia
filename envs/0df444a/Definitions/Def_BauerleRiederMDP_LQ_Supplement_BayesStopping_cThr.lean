-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_cThr
-- name    : BauerleRiederMDP_LQ_Supplement_BayesStopping_cThr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:01:15.639325+00:00
-- url     : https://prove2.me/theorems/53fc1c30-8a51-4c2f-8dda-f85529738a50
-- title:
--   The threshold $c_n(i)$ of the Bayesian stopping problem
-- statement:
--   **The threshold $c_n(i)$ of the Bayesian stopping problem** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §10.3.4, p.324, PDF 332): $c_n(i) := -c + \int \int  J_{n-1}(z, \hat{\Phi}(i, z)) Q(dz|\theta ) \hat{\mu}(d\theta |i)$, $i \in  I$, for $n \ge  1$.
--
--   **Formalization Note.** The double integral is the integral against the predictive law $\hat{Q}^Z(\cdot |i) = \int  Q(\cdot |\theta ) \hat{\mu}(d\theta |i)$ (`Qk ∘ₖ muhat`), taken as the published `erealIntegral` ($\int  v^+ - \int  v^-$, two Lebesgue integrals). Only $n \ge  1$ is meaningful.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §10.3.4, p.324, PDF 332

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesStopping_J

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

/-- **The threshold `c_n(i)` of the Bayesian stopping problem** (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §10.3.4, p.324, PDF 332):
`c_n(i) := −c + ∫∫ J_{n−1}(z, Φ̂(i, z)) Q(dz|θ) μ̂(dθ|i)`, `i ∈ I`, for `n ≥ 1`.

**Formalization Note.** The double integral is the integral against the predictive law
`Q̂^Z(·|i) = ∫ Q(·|θ) μ̂(dθ|i)` (`Qk ∘ₖ muhat`), taken as the published `erealIntegral`
(`∫ v⁺ − ∫ v⁻`, two Lebesgue integrals). Only `n ≥ 1` is meaningful. -/
noncomputable def BayesStopping.cThr {SΘ : Set ℝ} {I : Type} [MeasurableSpace I]
    (P : BayesStopping SΘ I) (n : ℕ) (i : I) : EReal :=
  ((-P.c : ℝ) : EReal) + erealIntegral ((P.Qk ∘ₖ P.muhat) i) fun z => P.J (n - 1) z (P.Phihat (i, z))

end BauerleRiederMDP.LQ.Supplement


