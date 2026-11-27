-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IntegrabilityAssumption
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel_IntegrabilityAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:57:49.536951+00:00
-- url     : https://prove2.me/theorems/4d71610d-f7b4-533a-870c-6aaf81136098
-- title:
--   The Integrability Assumption of Chapter 5
-- statement:
--   **The Integrability Assumption of Chapter 5** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.151, PDF 164), for the Bayesian Model: for all $x \in  E_X$, $\sup _\pi  \int  \mathbb E ^\pi _{x\theta }[\sum _{n=0}^{N-1} \beta ^n r^+(X_n, \theta , A_n) + \beta ^N g^+(X_N, \theta )] Q_0(d\theta ) < \infty $.
--
--   **Formalization Note.** The expectation is computed with the published path construction `BayesModel.law` of the model whose rewards are replaced by their positive parts (the law of the history does not depend on the rewards); it is a Lebesgue integral of a nonnegative function, and the supremum is over $\tilde{\Pi}_N$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_law

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The Integrability Assumption of Chapter 5** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), p.151, PDF 164), for the Bayesian Model: for all `x ∈ E_X`,
`sup_π ∫ 𝔼^π_{xθ}[∑_{n=0}^{N−1} β^n r⁺(X_n, θ, A_n) + β^N g⁺(X_N, θ)] Q_0(dθ) < ∞`.

**Formalization Note.** The expectation is computed with the published path construction
`BayesModel.law` of the model whose rewards are replaced by their positive parts (the law of the
history does not depend on the rewards); it is a Lebesgue integral of a nonnegative function, and
the supremum is over `Π̃_N`. -/
def BayesModel.IntegrabilityAssumption {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX]
    [MeasurableSpace A] [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ)
    (N : ℕ) : Prop :=
  ∀ x : EX, (⨆ π ∈ {π : (k : ℕ) → Htil EX A Z k → A | M.IsPolicy N π},
    ∫⁻ p, ENNReal.ofReal (p.2.2 + M.β ^ N * max (M.g (Htil.state N p.2.1, p.1)) 0)
      ∂(BayesModel.law
        { M with r := (fun q => max (M.r q) 0), r_meas := (M.r_meas.max measurable_const) } π x N)) < ⊤

end BauerleRiederMDP.LQ.Supplement


