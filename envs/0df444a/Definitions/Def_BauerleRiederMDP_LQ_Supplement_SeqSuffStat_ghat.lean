-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_ghat
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_ghat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:28:02.72942+00:00
-- url     : https://prove2.me/theorems/0d18c30d-0869-51d8-a86c-17f4bf07a235
-- title:
--   Formalization Note.
-- statement:
--   The terminal reward of the information-based model $ĝ(x, i) := \int  g(x, \theta ) \hat{\mu}(d\theta |i)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.6, p.163, PDF 176), "provided the integral exists".
--
--   **Formalization Note.** `erealIntegral`, values in $[-\infty , \infty ]$.
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

/-- The terminal reward of the information-based model `ĝ(x, i) := ∫ g(x, θ) μ̂(dθ|i)`
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition
5.4.6, p.163, PDF 176), "provided the integral exists".

**Formalization Note.** `erealIntegral`, values in `[−∞, ∞]`. -/
noncomputable def SeqSuffStat.ghat (S : SeqSuffStat M I) (x : EX) (i : I) : EReal :=
  erealIntegral (S.muhat i) fun θ => ((M.g (x, θ) : ℝ) : EReal)

end BauerleRiederMDP.LQ.Supplement


