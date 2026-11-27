-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhatpi
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhatpi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:29:58.126291+00:00
-- url     : https://prove2.me/theorems/3e716bea-dcd1-4755-9935-caa83e182c6c
-- title:
--   Formalization Note.
-- statement:
--   The value $\hat J _{n\pi }(x, i)$ of a policy $\pi  \in  \tilde{\Pi}_n$ in the information-based Markov Decision Model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.163, PDF 176): $\mathbb E ^\pi _{x i}[\sum _{k=0}^{n-1} \beta ^k \hat{r}(X_k, I_k, A_k) + \beta ^n ĝ(X_n, I_n)]$.
--
--   **Formalization Note.** `erealIntegral` under `infoLaw`; the horizon $n$ is a parameter.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.163, PDF 176

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_ghat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoState
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_infoLaw

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The value `Ĵ_{nπ}(x, i)` of a policy `π ∈ Π̃_n` in the information-based Markov Decision Model
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.163, PDF 176):
`𝔼^π_{x i}[∑_{k=0}^{n−1} β^k r̂(X_k, I_k, A_k) + β^n ĝ(X_n, I_n)]`.

**Formalization Note.** `erealIntegral` under `infoLaw`; the horizon `n` is a parameter. -/
noncomputable def SeqSuffStat.Jhatpi (S : SeqSuffStat M I) (n : ℕ)
    (π : (k : ℕ) → Htil EX A Z k → A) (x : EX) (i : I) : EReal :=
  erealIntegral (S.infoLaw π x i n) fun p =>
    p.2 + ((M.β ^ n : ℝ) : EReal) * S.ghat (Htil.state n p.1) (S.infoState i n p.1)

end BauerleRiederMDP.LQ.Supplement


