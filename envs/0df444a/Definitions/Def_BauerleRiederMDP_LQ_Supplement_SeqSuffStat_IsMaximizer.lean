-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_IsMaximizer
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_IsMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:27:38.329052+00:00
-- url     : https://prove2.me/theorems/3e28ea54-61df-4a00-a53f-49467ce516ce
-- title:
--   A maximizer of $v$ in the information-based model (Bäuerle & Rieder, *Markov Decision Processes
--   with Applications to Finance* (2011), Definition 2
-- statement:
--   A maximizer of $v$ in the information-based model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 2.3.6, p.21, PDF 36, as used in Theorem 5.4.8 b)): a decision rule $f : E_X \times  I \to  A$ (measurable, $f(x, i) \in  D(x)$) with $\hat{L}v(x, i, f(x, i)) = \hat{T}v(x, i)$ for all $(x, i)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.3.6, p.21, PDF 36, as used in Theorem 5.4.8 b)

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
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_That

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- A maximizer of `v` in the information-based model (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Definition 2.3.6, p.21, PDF 36, as used in Theorem 5.4.8 b)):
a decision rule `f : E_X × I → A` (measurable, `f(x, i) ∈ D(x)`) with `L̂v(x, i, f(x, i)) = T̂v(x, i)`
for all `(x, i)`. -/
def SeqSuffStat.IsMaximizer (S : SeqSuffStat M I) (v : EX × I → EReal) (f : EX × I → A) : Prop :=
  Measurable f ∧ ∀ p : EX × I, (p.1, f p) ∈ M.D ∧ S.Lhat v p.1 p.2 (f p) = S.That v p

end BauerleRiederMDP.LQ.Supplement


