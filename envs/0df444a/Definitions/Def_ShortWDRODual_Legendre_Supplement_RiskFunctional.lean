-- Prove2me | Definitions.Def_ShortWDRODual_Legendre_Supplement_RiskFunctional
-- name    : ShortWDRODual_Legendre_Supplement_RiskFunctional
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:45:26.866812+00:00
-- url     : https://prove2.me/theorems/a54b981f-e738-4df1-ad5d-677a77066ffb
-- title:
--   Equation (4) — infimum representation of the risk functional
-- statement:
--   Let $A$ be a parameter set and $f_\alpha:\mathcal X\to\mathbb R$ a family of losses. For a probability law $P$, define
--
--   $$J(P)=\inf_{\alpha\in A}\mathbb E_P[f_\alpha].$$
--
--   This is the risk functional in equation (4), before imposing the regularity hypotheses of Theorem 3. The parameter infimum precedes the outer distributional supremum used in the robust-risk definitions. It is not defined by a duality or minimax equality.
--
--   **Formalization Note** The loss family is extended to an arbitrary ambient parameter type; only its restriction to $A$ is used. Infima are in $\overline{\mathbb R}$; an empty $A$ gives $+\infty$. Expectations reuse the published extended integral, with an undefined $\infty-\infty$ assigned $-\infty$. Theorem 3's compact-wise lower bound implies each individual loss is bounded below, so its probability-law expectation is well-defined.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §5.2, p. 11 (PDF p. 11)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral

namespace ShortWDRODual.Legendre.Supplement

open MeasureTheory ModelRiskOT.Duality

/-- Equation (4), p. 11. The infimum is over all parameters in A.
The empty parameter domain has value +∞. No concavity or minimax assertion is assumed. -/
noncomputable def riskFunctional {E X : Type*} [MeasurableSpace X]
    (A : Set E) (f : E → X → ℝ) (P : Measure X) : EReal :=
  ⨅ a ∈ A, extIntegral P (fun x => (f a x : EReal))

end ShortWDRODual.Legendre.Supplement


