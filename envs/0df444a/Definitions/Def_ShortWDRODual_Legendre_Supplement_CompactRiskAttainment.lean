-- Prove2me | Definitions.Def_ShortWDRODual_Legendre_Supplement_CompactRiskAttainment
-- name    : ShortWDRODual_Legendre_Supplement_CompactRiskAttainment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:46:30.387672+00:00
-- url     : https://prove2.me/theorems/51ee8d0f-b4e8-4a7d-9fc7-d143e452cde6
-- title:
--   Equation (5) — a common compact set attaining every law’s risk
-- statement:
--   Let $A$ be a subset of a topological parameter space, $f_\alpha$ a loss family, and $\mathcal U$ a specified set of probability laws. The compact attainment condition is
--
--   $$\exists K\subseteq A\text{ compact},\quad \forall P\in\mathcal U,\qquad
--   \inf_{\alpha\in A}\mathbb E_P[f_\alpha]=\min_{\alpha\in K}\mathbb E_P[f_\alpha].$$
--
--   The compact set is chosen once for the whole uncertainty set, and the minimum must be attained for each law. This expresses exactly equation (5); neither compactness of $A$ nor convexity of $K$ is required. It supplies no exchange of extrema and no duality formula.
--
--   **Formalization Note** The right-hand minimum is an `IsLeast` assertion on the set of expectation values over $K$, at the value of the full parameter infimum. Thus it contains a minimizing parameter, even when the common value is $+\infty$. The definition permits a general set of measures, but Theorem 3 supplies precisely the probability laws in the relevant cost ball.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §5.2, p. 11 (PDF p. 11)

import Mathlib
import Definitions.Def_ShortWDRODual_Legendre_Supplement_RiskFunctional

namespace ShortWDRODual.Legendre.Supplement

open MeasureTheory ModelRiskOT.Duality

/-- Equation (5), p. 11. One compact subset of A serves every law in laws.
IsLeast includes attainment and equality with the infimum over all of A.
It imposes neither convexity of this compact set nor any minimax identity. -/
def compactRiskAttainment {E X : Type*} [TopologicalSpace E] [MeasurableSpace X]
    (A : Set E) (f : E → X → ℝ) (laws : Set (Measure X)) : Prop :=
  ∃ K : Set E, K ⊆ A ∧ IsCompact K ∧ ∀ P ∈ laws,
    IsLeast {y : EReal | ∃ a ∈ K, y = extIntegral P (fun x => (f a x : EReal))}
      (riskFunctional A f P)

end ShortWDRODual.Legendre.Supplement


