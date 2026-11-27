-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_That
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_That
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:26:43.890084+00:00
-- url     : https://prove2.me/theorems/9a8ebe09-6fa4-4bfb-ae24-b719b44c3089
-- title:
--   Formalization Note.
-- statement:
--   The maximal reward operator of the information-based model $\hat{T}v(x, i) := \sup _{a \in  D(x)} \hat{L}v(x, i, a)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Theorem 5.4.8 a), p.163, PDF 176; $D(x, i) := D(x)$ by Definition 5.4.6).
--
--   **Formalization Note.** The supremum is in `EReal`, so an action outside $D(x)$ contributes $\bot $.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 5.4.8 a), p.163, PDF 176; `D(x, i) := D(x)` by Definition 5.4.6

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Lhat

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The maximal reward operator of the information-based model
`T̂v(x, i) := sup_{a ∈ D(x)} L̂v(x, i, a)` (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 5.4.8 a), p.163, PDF 176; `D(x, i) := D(x)` by Definition
5.4.6).

**Formalization Note.** The supremum is in `EReal`, so an action outside `D(x)` contributes `⊥`. -/
noncomputable def SeqSuffStat.That (S : SeqSuffStat M I) (v : EX × I → EReal) (p : EX × I) :
    EReal :=
  ⨆ a ∈ {a : A | (p.1, a) ∈ M.D}, S.Lhat v p.1 p.2 a

end BauerleRiederMDP.LQ.Supplement


