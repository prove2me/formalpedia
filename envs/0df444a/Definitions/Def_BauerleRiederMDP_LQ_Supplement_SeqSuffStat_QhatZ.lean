-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_QhatZ
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_QhatZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:24:37.954048+00:00
-- url     : https://prove2.me/theorems/f0412026-0e94-5c5e-9333-e4f5f214c8ac
-- title:
--   The disturbance law of the information-based model
--   $\hat{Q}^Z(B|x, i, a) := \int  Q^Z(B|x, \theta , a) \hat{\mu}(d\theta |i)$ (Bäuerle & Rieder, *Markov Decision Processes with
--   Applications to Fi
-- statement:
--   The disturbance law of the information-based model $\hat{Q}^Z(B|x, i, a) := \int  Q^Z(B|x, \theta , a) \hat{\mu}(d\theta |i)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.6, p.162, PDF 175).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 5.4.6, p.162, PDF 175

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

/-- The disturbance law of the information-based model
`Q̂^Z(B|x, i, a) := ∫ Q^Z(B|x, θ, a) μ̂(dθ|i)` (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Definition 5.4.6, p.162, PDF 175). -/
noncomputable def SeqSuffStat.QhatZ (S : SeqSuffStat M I) (x : EX) (i : I) (a : A) : Measure Z :=
  (S.muhat i).bind fun θ => M.QZ (x, θ, a)

end BauerleRiederMDP.LQ.Supplement


