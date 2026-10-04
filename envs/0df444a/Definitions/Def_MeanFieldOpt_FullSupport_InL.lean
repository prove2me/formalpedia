-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_InL
-- name    : MeanFieldOpt_FullSupport_InL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:08:06.985132+00:00
-- url     : https://prove2.me/theorems/8273429a-9e45-4485-84ce-61b82fe4c219
-- title:
--   The extended space of order parameters $\mathscr L$ (Eq. (2.6))
-- statement:
--   Let $\xi$ be a mixture. For a function $\gamma : [0,1) \to \mathbb R$ write $\xi''\gamma$ for the pointwise product $t \mapsto \xi''(t)\gamma(t)$. The **extended space of order parameters** is
--
--   $$
--   \mathscr L = \Bigl\{ \gamma : [0,1) \to \mathbb R_{\ge 0} \;:\; \|\xi''\gamma\|_{\mathrm{TV}[0,t]} < \infty \ \ \forall t \in [0,1),\ \ \int_0^1 \xi''(t)\gamma(t)\,dt < \infty \Bigr\},
--   $$
--
--   where the total variation of $f$ on an interval $J$ is $\|f\|_{\mathrm{TV}(J)} = \sup_n \sup_{t_0 < \dots < t_n,\ t_i \in J} \sum_{i=1}^n |f(t_i) - f(t_{i-1})|$ (Eq. (1.8)).
--
--   $\mathscr L$ strictly contains the space $\mathscr U$ of non-decreasing order parameters of the Parisi formula; in particular it contains non-monotone functions. The extended variational principle of the paper minimizes the Parisi functional over $\mathscr L$.
--
--   **Formalization Note** $\gamma$ is a function `ℝ → ℝ` read only on $[0,1)$. The total variation (1.8) is Mathlib's `eVariationOn` on $[0,t]$, required to be finite. "$\int_0^1 \xi''\gamma < \infty$" is `IntegrableOn` on $[0,1)$, which for a non-negative function means finite integral together with a.e.-measurability, which the paper takes for granted.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 7, Eq. (2.6); total variation p. 5, Eq. (1.8)

import Mathlib
import Definitions.Def_MeanFieldOpt_FullSupport_Mixture

open MeasureTheory

namespace MeanFieldOpt.FullSupport

/-- The extended space of order parameters `ℒ` (arXiv:2001.00904v1, p. 7, Eq. (2.6)):
`γ : [0,1) → ℝ_{≥0}` with `‖ξ''γ‖_{TV[0,t]} < ∞` for all `t ∈ [0,1)` and `∫_0^1 ξ''(t)γ(t) dt < ∞`.
The function `γ : ℝ → ℝ` is only read on `[0,1)`; the total variation (1.8) is `eVariationOn`. -/
def InL (ξ : Mixture) (γ : ℝ → ℝ) : Prop :=
  (∀ t ∈ Set.Ico (0 : ℝ) 1, 0 ≤ γ t) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, eVariationOn (fun s => ξ.d2 s * γ s) (Set.Icc 0 t) ≠ ⊤) ∧
    IntegrableOn (fun s => ξ.d2 s * γ s) (Set.Ico 0 1)

end MeanFieldOpt.FullSupport


