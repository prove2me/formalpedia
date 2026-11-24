-- Prove2me | Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Lyapunov
-- name    : TwoSidedExp_DemandLimit_Supplement_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:17:28.157407+00:00
-- url     : https://prove2.me/theorems/238bc461-4114-4728-899d-517bca3a3850
-- title:
--   Log-coordinate objective V (30), its partial derivatives and dissipation
-- statement:
--   For the published objective W of (10), the log-coordinate objective and its dissipation are
--
--   $$V(y)=W((e^{y(\theta)})_\theta),\qquad D(s)=-\sum_\theta\frac{(\partial_\theta V(\log s))^2}{s(\theta)}.$$
--
--   The relevant domains are y(θ) ≤ log ρ(θ) and positive states s in the state space. The partial derivatives are actual Fréchet derivatives applied to coordinate unit vectors. These definitions express the identity in Step 5 of the proof of Theorem 1 without substituting an assumed gradient.
--
--   **Formalization Note** The published W already reads τ(θ) inside the sums of (10), as (30) requires. Positivity of s is supplied by the theorem; no use is made of the total real logarithm at zero. Positive definiteness is asserted for W(s) − W(s*) in the theorem, as explained in DISPROOF.md.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, pp. 12, A1–A2 (PDF 12, 37–38), (10), (30), Proof of Theorem 1 Step 5

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting
import Definitions.Def_TwoSidedExp_DemandLimit_Supplement_Dynamics

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit.Supplement

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

/-- (30), p. A1: V(y) = W(exp y), evaluated on y(θ) ≤ log ρ(θ). -/
noncomputable def V (S : MFSystem Γ Θ) (lam tau : ℝ) (y : Θ → ℝ) : ℝ :=
  S.W lam tau (fun θ => Real.exp (y θ))

/-- The genuine partial derivative of V, rather than an unrelated free vector. -/
noncomputable def partialV (S : MFSystem Γ Θ) (lam tau : ℝ) (y : Θ → ℝ) (θ : Θ) : ℝ := by
  classical
  exact fderiv ℝ (V S lam tau) y (Pi.single θ 1)

/-- Dissipation along a positive state, Step 5, p. A2. -/
noncomputable def dissipation (S : MFSystem Γ Θ) (lam tau : ℝ) (s : Θ → ℝ) : ℝ :=
  -(∑ θ, (partialV S lam tau (fun θ => Real.log (s θ)) θ) ^ 2 / s θ)

end TwoSidedExp.DemandLimit.Supplement


