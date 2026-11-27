-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_Jpi
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel_Jpi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:58:20.976129+00:00
-- url     : https://prove2.me/theorems/14a48ed5-e3c2-5b95-9ba5-16fa25cf118d
-- title:
--   The expected total reward of a policy in the Bayesian problem
-- statement:
--   **The expected total reward of a policy in the Bayesian problem** $J_{N\pi }(x) := \int  \mathbb E ^\pi _{x\theta }[\sum _{n=0}^{N-1} \beta ^n r(X_n, \theta , A_n) + \beta ^N g(X_N, \theta )] Q_0(d\theta )$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.150, PDF 163, for the Bayesian Model of Example 5.2.4, with $\pi  \in  \tilde{\Pi}_N$ as in Theorem 5.4.7, p.163, PDF 176).
--
--   **Formalization Note.** The expectation is `erealIntegral` ($\int  Y^+ - \int  Y^-$, Lebesgue integrals) under the joint law `BayesModel.law` of $(\vartheta , \tilde{h}_N, \sum  \beta ^n r)$; the Integrability Assumption of p.151 makes the positive part finite.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.150, PDF 163, for the Bayesian Model of Example 5.2.4, with `π ∈ Π̃_N` as in Theorem 5.4.7, p.163, PDF 176

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_law

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The expected total reward of a policy in the Bayesian problem**
`J_{Nπ}(x) := ∫ 𝔼^π_{xθ}[∑_{n=0}^{N−1} β^n r(X_n, θ, A_n) + β^N g(X_N, θ)] Q_0(dθ)` (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), p.150, PDF 163, for the Bayesian
Model of Example 5.2.4, with `π ∈ Π̃_N` as in Theorem 5.4.7, p.163, PDF 176).

**Formalization Note.** The expectation is `erealIntegral` (`∫ Y⁺ − ∫ Y⁻`, Lebesgue integrals)
under the joint law `BayesModel.law` of `(ϑ, h̃_N, ∑ β^n r)`; the Integrability Assumption of p.151
makes the positive part finite. -/
noncomputable def BayesModel.Jpi {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ) (N : ℕ)
    (π : (k : ℕ) → Htil EX A Z k → A) (x : EX) : EReal :=
  erealIntegral (M.law π x N) fun p =>
    ((p.2.2 + M.β ^ N * M.g (Htil.state N p.2.1, p.1) : ℝ) : EReal)

end BauerleRiederMDP.LQ.Supplement


