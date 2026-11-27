-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Lhat
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_Lhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:25:48.362209+00:00
-- url     : https://prove2.me/theorems/a39f992f-aad2-4a82-869f-6e9cf6fee6a9
-- title:
--   Formalization Note.
-- statement:
--   The operator $\hat{L}$ of the information-based model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 5.4.6, pp.162–163, PDF 175–176, with Definition 2.3.1, p.19, PDF 34): for $v : E_X \times  I \to  [-\infty , \infty )$, $\hat{L}v(x, i, a) := \hat{r}(x, i, a) + \beta  \int  v(\hat{T}(x, i, a, z)) \hat{Q}^Z(dz|x, i, a)$, where $\hat{T}(x, i, a, z) = (T_X(x, a, z), \hat{\Phi}(x, i, a, z))$. By Definition 5.4.6 the integral is $\int  \int  v(T_X(x, a, z), \hat{\Phi}(x, i, a, z)) Q^Z(dz|x, \theta , a) \hat{\mu}(d\theta |i)$, the form of Theorem 5.4.8 a).
--
--   **Formalization Note.** `erealIntegral` against the disturbance law $\hat{Q}^Z$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 5.4.6, pp.162–163, PDF 175–176, with Definition 2.3.1, p.19, PDF 34

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

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The operator `L̂` of the information-based model (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Definition 5.4.6, pp.162–163, PDF 175–176, with Definition
2.3.1, p.19, PDF 34): for `v : E_X × I → [−∞, ∞)`,
`L̂v(x, i, a) := r̂(x, i, a) + β ∫ v(T̂(x, i, a, z)) Q̂^Z(dz|x, i, a)`, where
`T̂(x, i, a, z) = (T_X(x, a, z), Φ̂(x, i, a, z))`. By Definition 5.4.6 the integral is
`∫ ∫ v(T_X(x, a, z), Φ̂(x, i, a, z)) Q^Z(dz|x, θ, a) μ̂(dθ|i)`, the form of Theorem 5.4.8 a).

**Formalization Note.** `erealIntegral` against the disturbance law `Q̂^Z`. -/
noncomputable def SeqSuffStat.Lhat (S : SeqSuffStat M I) (v : EX × I → EReal) (x : EX) (i : I)
    (a : A) : EReal :=
  S.rhat x i a + (M.β : EReal) *
    erealIntegral (S.QhatZ x i a) fun z => v (M.TX (x, a, z), S.Phihat (x, i, a, z))

end BauerleRiederMDP.LQ.Supplement


