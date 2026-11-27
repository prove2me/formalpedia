-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhat
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:31:20.373106+00:00
-- url     : https://prove2.me/theorems/de661d22-8633-4cc1-84f3-4ab621b307c9
-- title:
--   Formalization Note.
-- statement:
--   The value function $\hat J _n(x, i) := \sup _{\pi  \in  \tilde{\Pi}_n} \hat J _{n\pi }(x, i)$ of the information-based Markov Decision Model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.163, PDF 176), the supremum over all history-dependent policies with measurable decision rules $f_k : \tilde{H}_k \to  A$, $f_k(\tilde{h}_k) \in  D(x_k)$.
--
--   **Formalization Note.** A supremum in `EReal` over $\tilde{\Pi}_n$ (`BayesModel.IsPolicy`), not over Markov policies and not the Bellman recursion.
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
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Jhatpi

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The value function `Ĵ_n(x, i) := sup_{π ∈ Π̃_n} Ĵ_{nπ}(x, i)` of the information-based Markov
Decision Model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011),
p.163, PDF 176), the supremum over all history-dependent policies with measurable decision rules
`f_k : H̃_k → A`, `f_k(h̃_k) ∈ D(x_k)`.

**Formalization Note.** A supremum in `EReal` over `Π̃_n` (`BayesModel.IsPolicy`), not over Markov
policies and not the Bellman recursion. -/
noncomputable def SeqSuffStat.Jhat (S : SeqSuffStat M I) (n : ℕ) (x : EX) (i : I) : EReal :=
  ⨆ π ∈ {π : (k : ℕ) → Htil EX A Z k → A | M.IsPolicy n π}, S.Jhatpi n π x i

end BauerleRiederMDP.LQ.Supplement


