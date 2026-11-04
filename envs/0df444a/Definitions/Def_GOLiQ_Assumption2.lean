-- Prove2me | Definitions.Def_GOLiQ_Assumption2
-- name    : GOLiQ_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:05.641243+00:00
-- url     : https://prove2.me/theorems/15edda8c-bffd-44dc-a9be-9963028eb57c
-- title:
--   Assumption 2: light-tailed service and interarrival times with constants $\eta,\theta,a,\gamma$
-- statement:
--   Assumption 2 with constants $\eta,\theta,a,\gamma$ holds if $\eta>0$ and the moment-generating functions are finite,
--   $$\mathbb E[e^{\eta V_n}]<\infty,\qquad \mathbb E[e^{\eta U_n}]<\infty,$$
--   and $0<\theta<\eta/(2\bar\mu)$, $0<a<(\underline\mu-\lambda(\underline p))/(\underline\mu+\lambda(\underline p))$, $\gamma>0$ satisfy
--   $$\phi_U(-\theta)<-(1-a)\theta-\gamma,\qquad \phi_V(\theta)<(1+a)\theta-\gamma,\tag{3}$$
--   where $\phi_U$, $\phi_V$ are the cumulant generating functions of $U_n$ and $V_n$.
--
--   The constants $\gamma$ and $\theta$ give the exponential rate of forgetting of the initial state (Lemma 2), and $\min(\gamma,\eta)$ sets the cycle lengths of the algorithm.
--
--   **Formalization Note** "$\eta/2\bar\mu$" is read as $\eta/(2\bar\mu)$. The words "a sufficiently small constant $\eta$" are not part of this predicate: statements that need $\eta$ small quantify over all $\eta$ below a model-dependent threshold.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Assumption 2, p.11, (3)

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives

open MeasureTheory ProbabilityTheory

namespace GOLiQ

/-- **Assumption 2 (light-tailed service and interarrival times)** with constants `η, θ, a, γ`
(Chen, Liu, Hong, arXiv:2009.02911v3, p.11):

`η > 0` with `E[exp(ηVₙ)] < ∞` and `E[exp(ηUₙ)] < ∞`, and `0 < θ < η/(2µ̄)`,
`0 < a < (µ̲ − λ(p̲))/(µ̲ + λ(p̲))`, `γ > 0` such that

`φ_U(−θ) < −(1 − a)θ − γ` and `φ_V(θ) < (1 + a)θ − γ`    (3)

where `φ_U`, `φ_V` are the cumulant generating functions of `U` and `V`.

**Formalization Note.** `η/2µ̄` is read as `η/(2µ̄)`. The cumulant generating function is Mathlib's
`cgf` (logarithm of the moment generating function); both are evaluated at points where the
moment generating function is finite (`θ < η` and `Uₙ ≥ 0`). The words "a sufficiently small
constant `η`" are not part of this predicate: statements that need `η` small say so by quantifying
over all `η` below a model-dependent threshold. -/
def Assumption2 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (η θ a γ : ℝ) : Prop :=
  0 < η ∧
  Integrable (fun ω => Real.exp (η * Pr.V 1 ω)) Pr.P ∧
  Integrable (fun ω => Real.exp (η * Pr.U 1 ω)) Pr.P ∧
  0 < θ ∧ θ < η / (2 * M.muHi) ∧
  0 < a ∧ a < (M.muLo - M.lam M.pLo) / (M.muLo + M.lam M.pLo) ∧
  0 < γ ∧
  cgf (Pr.U 1) Pr.P (-θ) < -(1 - a) * θ - γ ∧
  cgf (Pr.V 1) Pr.P θ < (1 + a) * θ - γ

end GOLiQ


