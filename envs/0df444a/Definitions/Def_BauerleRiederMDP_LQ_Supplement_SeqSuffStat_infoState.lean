-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoState
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:28:24.94369+00:00
-- url     : https://prove2.me/theorems/ccb5de02-e258-5591-8619-d2decf2ca005
-- title:
--   The information state $i_k$ along a history (Bäuerle & Rieder, *Markov Decision Processes with
--   Applications to Finance* (2011), Definition 5
-- statement:
--   The information state $i_k$ along a history (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.6, p.162, PDF 175): from $i_0 = i$, $i_{k+1} = \hat{\Phi}(x_k, i_k, a_k, z_{k+1})$. With $i = t_0(x_0)$ this is $t_k(\tilde{h}_k)$ (Definition 5.4.5).
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

/-- The information state `i_k` along a history (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Definition 5.4.6, p.162, PDF 175): from `i_0 = i`,
`i_{k+1} = Φ̂(x_k, i_k, a_k, z_{k+1})`. With `i = t_0(x_0)` this is `t_k(h̃_k)` (Definition 5.4.5). -/
def SeqSuffStat.infoState (S : SeqSuffStat M I) (i : I) : (k : ℕ) → Htil EX A Z k → I
  | 0, _ => i
  | k + 1, (h, a, z, _) => S.Phihat (Htil.state k h, SeqSuffStat.infoState S i k h, a, z)

end BauerleRiederMDP.LQ.Supplement


