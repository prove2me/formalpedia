-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_rhat
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_rhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:24:10.344824+00:00
-- url     : https://prove2.me/theorems/5ca3cc47-4abc-51c2-a8b1-d09ddfecb7a9
-- title:
--   Formalization Note.
-- statement:
--   The one-stage reward of the information-based model $\hat{r}(x, i, a) := \int  r(x, \theta , a) \hat{\mu}(d\theta |i)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.6, p.162, PDF 175), "whenever the integral exists".
--
--   **Formalization Note.** `erealIntegral` ($\int  r^+ - \int  r^-$, Lebesgue integrals), so the value is in $[-\infty , \infty ]$ and no Bochner junk value enters.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The one-stage reward of the information-based model `r̂(x, i, a) := ∫ r(x, θ, a) μ̂(dθ|i)`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition
5.4.6, p.162, PDF 175), "whenever the integral exists".

**Formalization Note.** `erealIntegral` (`∫ r⁺ − ∫ r⁻`, Lebesgue integrals), so the value is in
`[−∞, ∞]` and no Bochner junk value enters. -/
noncomputable def SeqSuffStat.rhat (S : SeqSuffStat M I) (x : EX) (i : I) (a : A) : EReal :=
  erealIntegral (S.muhat i) fun θ => ((M.r (x, θ, a) : ℝ) : EReal)

end BauerleRiederMDP.LQ.Supplement


