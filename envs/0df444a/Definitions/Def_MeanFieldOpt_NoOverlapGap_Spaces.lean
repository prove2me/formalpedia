-- Prove2me | Definitions.Def_MeanFieldOpt_NoOverlapGap_Spaces
-- name    : MeanFieldOpt_NoOverlapGap_Spaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:06:16.15153+00:00
-- url     : https://prove2.me/theorems/09c49ab6-2a0f-4a41-bbdf-6af982cb15e4
-- title:
--   The order-parameter spaces $\mathscr U$ (1.4) and $\mathscr L$ (2.6)
-- statement:
--   Let $\xi$ be a mixture. Order parameters are functions $\gamma : [0,1) \to \mathbb R_{\ge 0}$.
--
--   1. The **monotone space** (Eq. (1.4))
--   $$\mathscr U = \Big\{ \gamma : [0,1) \to \mathbb R_{\ge 0} \;:\; \gamma \text{ non-decreasing},\ \int_0^1 \gamma(t)\,dt < \infty \Big\}.$$
--   2. The **extended space** (Eq. (2.6))
--   $$\mathscr L = \Big\{ \gamma : [0,1) \to \mathbb R_{\ge 0} \;:\; \|\xi''\gamma\|_{TV[0,t]} < \infty\ \ \forall t \in [0,1),\ \int_0^1 \xi''(t)\gamma(t)\,dt < \infty \Big\},$$
--   where $\xi''\gamma$ is the pointwise product and $\|f\|_{TV(J)} = \sup_n \sup_{t_0 < \dots < t_n,\, t_i \in J} \sum_{i=1}^n |f(t_i) - f(t_{i-1})|$ is the total variation (Eq. (1.8)).
--
--   The Parisi formula minimises the Parisi functional over $\mathscr U$; the paper's extended variational principle minimises it over the larger space $\mathscr L$, which contains non-monotone functions. One has $\mathscr U \subseteq \mathscr L$.
--
--   **Formalization Note** Order parameters are functions $\mathbb R \to \mathbb R$; both predicates read them only on $[0,1)$. The total variation is Mathlib's `eVariationOn` on $[0,t]$. "$\int < \infty$" for a non-negative function is `IntegrableOn` on $[0,1)$, which also asks for almost-everywhere strong measurability, a condition the paper takes for granted.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 3, Eq. (1.4); p. 7, Eq. (2.6); p. 5, Eq. (1.8)

import Mathlib
import Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture

open MeasureTheory Set

namespace MeanFieldOpt.NoOverlapGap

/-- The space `𝒰` of (1.4), p. 3: `γ : [0,1) → ℝ_{≥0}` non-decreasing with `∫_0^1 γ(t) dt < ∞`.
Functions are taken on `ℝ`; only their values on `[0,1)` are read. -/
def InU (γ : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ γ t) ∧ MonotoneOn γ (Ico (0 : ℝ) 1) ∧
    IntegrableOn γ (Ico (0 : ℝ) 1)

/-- The extended space `ℒ` of (2.6), p. 7: `γ : [0,1) → ℝ_{≥0}` with
`‖ξ''γ‖_{TV[0,t]} < ∞` for all `t ∈ [0,1)` and `∫_0^1 ξ''(t) γ(t) dt < ∞`.
The total variation (1.8) is `eVariationOn`. -/
def InL (ξ : Mixture) (γ : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ico (0 : ℝ) 1, 0 ≤ γ t) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, eVariationOn (fun s => ξ.xi'' s * γ s) (Icc 0 t) ≠ ⊤) ∧
    IntegrableOn (fun s => ξ.xi'' s * γ s) (Ico (0 : ℝ) 1)

end MeanFieldOpt.NoOverlapGap


