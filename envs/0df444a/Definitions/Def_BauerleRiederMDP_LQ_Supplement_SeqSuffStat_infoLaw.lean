-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoLaw
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:28:51.382868+00:00
-- url     : https://prove2.me/theorems/85a1c7e7-36f6-564c-b84f-1168cf745059
-- title:
--   Formalization Note.
-- statement:
--   The law of the history and of the accumulated reward of the information-based Markov Decision Model under a policy $\pi  \in  \tilde{\Pi}_N$ from $(x_0, i_0) = (x, i)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.6 and the values $\hat J _{n\pi }$, p.163, PDF 176): the action is $a_k = \pi _k(\tilde{h}_k)$, $z_{k+1} ~ \hat{Q}^Z(\cdot |x_k, i_k, a_k)$, $x_{k+1} = T_X(x_k, a_k, z_{k+1})$, $i_{k+1} = \hat{\Phi}(x_k, i_k, a_k, z_{k+1})$; the second coordinate is $\sum _{j<k} \beta ^j \hat{r}(x_j, i_j, a_j)$.
--
--   **Formalization Note.** Built forwards by `Measure.bind`; the information state is recomputed from the history (`infoState`).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 5.4.6 and the values `Ĵ_{nπ}`, p.163, PDF 176

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_rhat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_QhatZ
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoState

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The law of the history and of the accumulated reward of the information-based Markov Decision
Model under a policy `π ∈ Π̃_N` from `(x_0, i_0) = (x, i)` (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), Definition 5.4.6 and the values `Ĵ_{nπ}`, p.163,
PDF 176): the action is `a_k = π_k(h̃_k)`, `z_{k+1} ~ Q̂^Z(·|x_k, i_k, a_k)`, `x_{k+1} = T_X(x_k, a_k, z_{k+1})`,
`i_{k+1} = Φ̂(x_k, i_k, a_k, z_{k+1})`; the second coordinate is `∑_{j<k} β^j r̂(x_j, i_j, a_j)`.

**Formalization Note.** Built forwards by `Measure.bind`; the information state is recomputed
from the history (`infoState`). -/
noncomputable def SeqSuffStat.infoLaw (S : SeqSuffStat M I) (π : (k : ℕ) → Htil EX A Z k → A)
    (x : EX) (i : I) : (k : ℕ) → Measure (Htil EX A Z k × EReal)
  | 0 => Measure.dirac (x, 0)
  | k + 1 => (SeqSuffStat.infoLaw S π x i k).bind fun p =>
      (S.QhatZ (Htil.state k p.1) (S.infoState i k p.1) (π k p.1)).map fun z =>
        ((p.1, π k p.1, z, M.TX (Htil.state k p.1, π k p.1, z)),
          p.2 + ((M.β ^ k : ℝ) : EReal) * S.rhat (Htil.state k p.1) (S.infoState i k p.1) (π k p.1))

end BauerleRiederMDP.LQ.Supplement


