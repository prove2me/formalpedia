-- Prove2me | Definitions.Def_JointEstimationRobustness_EstimateSupport_Estimation
-- name    : JointEstimationRobustness_EstimateSupport_Estimation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:11:44.992468+00:00
-- url     : https://prove2.me/theorems/697c8faf-7bd1-420d-b6e4-03bae1244774
-- title:
--   Definition 1 — Minimum-loss estimates and estimate uncertainty sets
-- statement:
--   Fix data $D$, a finite parameter dimension $M$, an estimation domain $W\subseteq\mathbb R^M$, and a real estimation metric $\rho(\beta)=\rho(\beta;D)$.
--   A minimizing estimate $\widehat\beta$ belongs to $W$ and satisfies $\rho(\widehat\beta)\le\rho(\beta)$ for every $\beta\in W$. Define its value and its estimate uncertainty set by
--   $$\widehat\rho=\rho(\widehat\beta),\qquad \mathcal E(r;D)=\{\beta\in W:\rho(\beta)\le\widehat\rho+r\}.$$
--   The source uses $r\ge0$. The set is defined by the same expression for every real $r$; Proposition 3 uses only $r>0$. The helper value is defined for any chosen vector and is a minimum value when the minimizing-estimate predicate holds. No uniqueness is assumed.
--
--   This definition supplies the estimation component of the joint estimation and robustness model. It does not identify $W$ with the larger conjugate domain $\bar W$.
--
--   **Formalization Note.** Real vectors are functions on `Fin M`; the data are fixed in the section $\rho$. The predicate records membership and the minimum inequality explicitly, and the set is constructed from the metric and the estimate. No duality property is part of the definition.
-- source:
--   Zhu, Xie and Sim (2022), Joint Estimation and Robustness Optimization, https://doi.org/10.1287/mnsc.2020.3898, supplied artifact PDF/printed p. 5, (4), Definition 1 and (5); domain inclusion p. 4. Citation basis: published, as supplied metadata.

import Mathlib

namespace JointEstimationRobustness.EstimateSupport

/-- Equation (4), supplied artifact p. 5: an attained minimum on the estimation domain. -/
def IsMinimizingEstimate {M : ℕ} (W : Set (Fin M → ℝ))
    (ρ : (Fin M → ℝ) → ℝ) (βhat : Fin M → ℝ) : Prop :=
  βhat ∈ W ∧ ∀ β ∈ W, ρ βhat ≤ ρ β

/-- The value of the metric at the chosen estimate, denoted rho-hat on p. 5. -/
noncomputable def estimateValue {M : ℕ} (ρ : (Fin M → ℝ) → ℝ)
    (βhat : Fin M → ℝ) : ℝ :=
  ρ βhat

/-- Definition 1, (5), p. 5: the loss sublevel set inside W. The source uses r ≥ 0. -/
def estimateSet {M : ℕ} (W : Set (Fin M → ℝ))
    (ρ : (Fin M → ℝ) → ℝ) (βhat : Fin M → ℝ) (r : ℝ) : Set (Fin M → ℝ) :=
  {β ∈ W | ρ β ≤ estimateValue ρ βhat + r}

end JointEstimationRobustness.EstimateSupport


