-- Prove2me | Definitions.Def_StochSQP_Vanishing_Supplement_Stochastic
-- name    : StochSQP_Vanishing_Supplement_Stochastic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:16:02.656796+00:00
-- url     : https://prove2.me/theorems/9fc739ff-9268-46fb-8939-8f8465095f40
-- title:
--   Algorithm paths, signature events, and Assumption 6
-- statement:
--   On an arbitrary probability space $(\Omega,\mathcal F,\mu)$, a process is a family of published algorithm runs. Each gradient is measurable; the iterate, normal step and Hessian are measurable functions of the preceding gradient history, and the remaining iteration outputs are measurable functions of the history including the current gradient. Initial data and the supplied sequence $\{\beta_k\}$ are fixed. Every realization satisfies Algorithm 1, Assumption 1 and the pathwise part of Assumption 3 (symmetry, the norm bound $\kappa_H$ and curvature $\zeta$ on $\operatorname{Null}(J_k)$). Assumption 3's clause that $H_k$ is chosen independently from $g_k$ is not imposed; the source means it conditionally on reaching $x_k$, and none of Lemmas 22–24 or Theorem 5 uses it. Assumption 2 is written as conditional mean and second-moment identities over all measurable events determined by $X_k$, with explicit integrability.
--
--   Let $E=\{\omega:T_k^{\mathrm{trial,true}}(\omega)\ge t\text{ for all }k\}$ for $t>0$. Define $Q_k=I[T_k^{\mathrm{trial,true}}<T_{k-1}]$, $W_k=\sum_{i<k}I[T_i<T_{i-1}]$, and signature nodes by matching all $Q_i,W_i$ up to the current depth. Assumption 6 requires the bound in every realization, time-constant $\chi,\zeta,\xi$, and one $p_\tau\in(0,1]$ such that
--   $$\mu(T_k<T_{k-1}\mid E,\text{signature through }k,T_k^{\mathrm{trial,true}}<T_{k-1})\ge p_\tau$$
--   on every reachable conditioning event, uniformly over every $k$. Null nodes impose no conditional-probability requirement. The all-realizations lower bound makes $E$ certain, so no extra positive-probability hypothesis is needed.
--
--   The reduction threshold is the printed integer $s_{\max}=\lceil\log(t/\tau_{-1})/\log(1-\epsilon_\tau)\rceil\in\mathbb Z$. It is negative only when $t>\tau_{-1}/(1-\epsilon_\tau)$; then no true-trial value can fall below the (nonincreasing) merit parameter, and (36)'s annotation $\in\mathbb N$ is the only part of the display that fails. Opportunity counts use the current $T_k$, while $Q_k$ uses the previous value. An infinite count is represented by finiteness of its index set, never by a real series with a default value.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, pp. 6, 23, 31–33, Assumptions 2, 3, 6; Definition 2; (36), (44), (45)

import Mathlib
import Definitions.Def_StochSQP_Vanishing_Supplement_TrueTrial

namespace StochSQP.Vanishing.Supplement

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

variable {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Random paths in the published Run carrier, with arbitrary sample space. -/
structure Process (Ω : Type*) (n m : ℕ) where
  path : Ω → Run n m

/-- A measurable function of the first k stochastic gradients, before gradient k is drawn. -/
def FromHistory {S : Type*} [MeasurableSpace S] (M : Process Ω n m)
    (k : ℕ) (f : Ω → S) : Prop :=
  ∃ F : (Fin k → E n) → S, Measurable F ∧
    ∀ ω, f ω = F (fun i => (M.path ω).g i.val)

/-- The source's random-variable and fixed-initialization conventions, with causal dependence. -/
def Causal (P : Problem n m) (A : Params) (M : Process Ω n m) : Prop :=
  ∀ k : ℕ,
    Measurable (fun ω => (M.path ω).g k) ∧
    FromHistory M k (fun ω => ((M.path ω).x k, (M.path ω).v k, (M.path ω).H k)) ∧
    FromHistory M (k+1) (fun ω =>
      ((M.path ω).u k, (M.path ω).d k, (M.path ω).y k,
       (M.path ω).β k, (M.path ω).τ k, (M.path ω).χ k,
       (M.path ω).ζ k, (M.path ω).ξ k, (M.path ω).α k)) ∧
    Measurable (fun ω => trueTrial P A (M.path ω) k)

/-- Assumption 2 in event-integral form: conditional mean and conditional second moment,
conditioned on X_k. Integrability rules out the Bochner default value. -/
def GradientMoments (P : Problem n m) (M : Process Ω n m) (μ : Measure Ω) : Prop :=
  ∃ V : ℝ, 0 < V ∧ ∀ k : ℕ,
    Integrable (fun ω => (M.path ω).g k) μ ∧
    Integrable (fun ω => ‖(M.path ω).g k - P.grad ((M.path ω).x k)‖ ^ 2) μ ∧
    ∀ B : Set (E n), MeasurableSet B →
      (∫ ω in {ω | (M.path ω).x k ∈ B}, (M.path ω).g k ∂μ) =
        (∫ ω in {ω | (M.path ω).x k ∈ B}, P.grad ((M.path ω).x k) ∂μ) ∧
      (∫ ω in {ω | (M.path ω).x k ∈ B},
          ‖(M.path ω).g k - P.grad ((M.path ω).x k)‖ ^ 2 ∂μ) ≤
        V * (μ {ω | (M.path ω).x k ∈ B}).toReal

/-- Algorithm 1, Assumptions 1 and 2, and the pathwise part of Assumption 3 on every
realization. Assumption 3's clause that H_k is chosen independently from g_k is not imposed:
the source means it conditionally on reaching x_k, and Lemma 24 and Theorem 5 do not use it. -/
def StochasticModel (P : Problem n m) (A : Params) (M : Process Ω n m)
    (μ : Measure Ω) (X : Set (E n)) (κH ζH : ℝ) : Prop :=
  A.Valid ∧ Assumption1 P A.L A.Γ X ∧ Causal P A M ∧ GradientMoments P M μ ∧
  (∃ β : ℕ → ℝ, ∀ ω k, (M.path ω).β k = β k) ∧
  (∀ ω, IsRun P A (M.path ω) ∧ Assumption3 P (M.path ω) κH ζH ∧
    ∀ k, (M.path ω).x k ∈ X)

/-- Definition 2, as a set of paths. Assumption 6 below requires every realization to belong. -/
noncomputable def lowerEvent (P : Problem n m) (A : Params) (M : Process Ω n m)
    (t : ℝ) : Set Ω := {ω | ∀ k : ℕ, ENNReal.ofReal t ≤ trueTrial P A (M.path ω) k}

noncomputable def opportunity (P : Problem n m) (A : Params) (M : Process Ω n m)
    (k : ℕ) : Set Ω :=
  {ω | trueTrial P A (M.path ω) k < ENNReal.ofReal ((M.path ω).τ k)}

noncomputable def previousOpportunity (P : Problem n m) (A : Params) (M : Process Ω n m)
    (k : ℕ) : Set Ω :=
  {ω | trueTrial P A (M.path ω) k < ENNReal.ofReal (prev (M.path ω).τ A.τ₀ k)}

noncomputable def reduction (A : Params) (M : Process Ω n m) (k : ℕ) : Set Ω :=
  {ω | (M.path ω).τ k < prev (M.path ω).τ A.τ₀ k}

noncomputable def Q (P : Problem n m) (A : Params) (M : Process Ω n m)
    (k : ℕ) (ω : Ω) : Bool := by
  classical
  exact decide (ω ∈ previousOpportunity P A M k)

noncomputable def W (A : Params) (M : Process Ω n m) (k : ℕ) (ω : Ω) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range k, if ω ∈ reduction A M i then 1 else 0

/-- Full signatures, including q_k and w_k; only reachable conditioning sets are used. -/
noncomputable def node (P : Problem n m) (A : Params) (M : Process Ω n m)
    (k : ℕ) (q : ℕ → Bool) (w : ℕ → ℕ) : Set Ω :=
  {ω | ∀ i ≤ k, Q P A M i ω = q i ∧ W A M i ω = w i}

/-- (36), the printed integer ceiling. It is negative only when t > τ₋₁/(1-ϵ_τ), where no
opportunity can occur; the printed annotation "∈ ℕ" fails there, and clamping would weaken (52). -/
noncomputable def sMax (A : Params) (t : ℝ) : ℤ :=
  ⌈Real.log (t / A.τ₀) / Real.log (1 - A.ετ)⌉

/-- Assumption 6 with one p_tau for all finite horizons (equivalently, all k).
The all-realizations bound makes lowerEvent certain; no positive-probability premise is added. -/
def Assumption6 (P : Problem n m) (A : Params) (M : Process Ω n m)
    (μ : Measure Ω) (t pτ : ℝ) : Prop :=
  0 < t ∧ 0 < pτ ∧ pτ ≤ 1 ∧
  (∀ ω : Ω, ω ∈ lowerEvent P A M t) ∧
  (∀ ω k, (M.path ω).χ k = (M.path ω).χ 0 ∧
    (M.path ω).ζ k = (M.path ω).ζ 0 ∧ (M.path ω).ξ k = (M.path ω).ξ 0) ∧
  ∀ (k : ℕ) (q : ℕ → Bool) (w : ℕ → ℕ),
    let C := lowerEvent P A M t ∩ node P A M k q w ∩ previousOpportunity P A M k
    μ C ≠ 0 → ENNReal.ofReal pτ ≤ (cond μ C) (reduction A M k)

noncomputable def opportunityCount (P : Problem n m) (A : Params) (M : Process Ω n m)
    (K : ℕ) (ω : Ω) : ℕ := by
  classical
  exact ∑ k ∈ Finset.range (K+1), if ω ∈ opportunity P A M k then 1 else 0

/-- Finiteness of the indicator sum without a real-valued tsum default. -/
noncomputable def finiteOpportunities (P : Problem n m) (A : Params)
    (M : Process Ω n m) : Set Ω :=
  {ω | Set.Finite {k : ℕ | ω ∈ opportunity P A M k}}

end StochSQP.Vanishing.Supplement


