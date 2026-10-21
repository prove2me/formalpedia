-- Prove2me | Definitions.Def_AccountingRules_Threshold_Model
-- name    : AccountingRules_Threshold_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:05.697318+00:00
-- url     : https://prove2.me/theorems/506530ac-8771-45a6-b8fb-3399018f8ad7
-- title:
--   §2–§3 and Appendix A.1 — the prior, conditional means, regulator payoff and binary accounting program
-- statement:
--   The project can be liquidated for $M>0$ or continued for the random cash flow $\theta$. Its prior $P$ has a density, support $[\underline\theta,\overline\theta]$, $0\le\underline\theta<M<\overline\theta$, and the entrepreneur's private continuation benefit is $B\in[0,M]$. Full support means that every nonempty open subinterval of $[\underline\theta,\overline\theta]$ has positive probability.
--
--   For an event $S$ of positive probability, the conditional mean is
--   $$\mathbb E_P[f(\theta)\mid S]=\frac{\int_S f(\theta)\,dP(\theta)}{P(S)}.$$
--   A posterior $\mu$ induces continuation precisely when its mean exceeds $M-B$; at equality the entrepreneur terminates. Thus the regulator's payoff is $V(\mu)=\mathbb E_\mu[\theta]$ on continuation and $M$ on termination, and an accounting rule represented by a Bayes-plausible distribution $\tau$ over posteriors has value $\int V(\mu)\,d\tau(\mu)$.
--
--   A binary rule is a measurable $m(\theta)\in[0,1]$, the conditional probability of the continuation signal. Its objective is $\int\theta m(\theta)\,dP+M[1-\int m(\theta)\,dP]$. The constraints (A.1) and (A.2) say that the posterior means at the low and high signals respectively lie below and above $M-B$. These definitions are the common model for the target and the appendix milestones.
--
--   **Formalization Note** Integrals against $P$ replace the paper's integrals against its density. The posterior mean uses positive and negative parts; on the bounded support of a Bayes-plausible posterior it is the usual mean. The conditional mean is used only for events whose positive mass follows from the standing support assumption. Proposition 1 and the online appendix's Proposition 6 are outside this model; the entrepreneur's response is fixed by (4) and endnote 6.
-- source:
--   Jiang & Yang, Optimal Accounting Rules, Private Benefits of Control, and Efficient Liquidation, Management Science (Articles in Advance, 2023), doi:10.1287/mnsc.2019.03087, pp. 3–4, 9 (PDF 4–5, 10), §2, §3, (4), (5), Appendix A.1 (A.1)–(A.2)

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_BayesPlausible

open MeasureTheory ProbabilityTheory Set

namespace AccountingRules.Threshold

/-- The standing model of Section 2. The prior has density and full interval support. -/
structure Standing (P : Measure ℝ) (θlo θhi M B : ℝ) : Prop where
  prob : IsProbabilityMeasure P
  density : P ≪ volume
  supp_sub : P (Icc θlo θhi)ᶜ = 0
  supp_full : ∀ a b : ℝ, θlo ≤ a → a < b → b ≤ θhi → 0 < P (Ioo a b)
  θlo_nonneg : 0 ≤ θlo
  M_pos : 0 < M
  M_lt_θhi : M < θhi
  B_nonneg : 0 ≤ B
  B_le_M : B ≤ M

/-- Conditional expectation on an event of positive prior probability. -/
noncomputable def condMean (P : Measure ℝ) (f : ℝ → ℝ) (S : Set ℝ) : ℝ :=
  (∫ θ in S, f θ ∂P) / (P S).toReal

/-- Posterior mean, defined by positive and negative parts of the integral. -/
noncomputable def postMean (μ : Measure ℝ) : ℝ :=
  (∫⁻ θ, ENNReal.ofReal θ ∂μ).toReal - (∫⁻ θ, ENNReal.ofReal (-θ) ∂μ).toReal

/-- Regulator payoff when the entrepreneur terminates on indifference. -/
noncomputable def regPayoff (M B : ℝ) (μ : Measure ℝ) : ℝ :=
  if M - B < postMean μ then postMean μ else M

/-- The expected regulator payoff under a distribution over posteriors. -/
noncomputable def value (M B : ℝ) (τ : Measure (Measure ℝ)) : ℝ :=
  ∫ μ, regPayoff M B μ ∂τ

/-- A measurable binary signal rule, expressed as the probability of signal one. -/
def IsRule (m : ℝ → ℝ) : Prop := Measurable m ∧ ∀ θ, 0 ≤ m θ ∧ m θ ≤ 1

/-- Objective of the binary program in Appendix A.1. -/
noncomputable def objective (P : Measure ℝ) (M : ℝ) (m : ℝ → ℝ) : ℝ :=
  ∫ θ, θ * m θ ∂P + M * (1 - ∫ θ, m θ ∂P)

/-- The low-signal mean constraint (A.1). -/
def A1 (P : Measure ℝ) (M B : ℝ) (m : ℝ → ℝ) : Prop :=
  ∫ θ, θ * (1 - m θ) ∂P ≤ (M - B) * ∫ θ, (1 - m θ) ∂P

/-- The high-signal mean constraint (A.2). -/
def A2 (P : Measure ℝ) (M B : ℝ) (m : ℝ → ℝ) : Prop :=
  (M - B) * ∫ θ, m θ ∂P ≤ ∫ θ, θ * m θ ∂P

end AccountingRules.Threshold


