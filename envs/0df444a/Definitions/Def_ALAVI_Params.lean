-- Prove2me | Definitions.Def_ALAVI_Params
-- name    : ALAVI_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:35.908886+00:00
-- url     : https://prove2.me/theorems/f5bb2045-c4ae-48ff-9da7-784f2eb6b3fe
-- title:
--   The parameter window of Lemma 4.1
-- statement:
--   The ALAVI parameters $\eta,\alpha,\gamma$ lie in the window of Lemma 4.1 for the constants $L,\tau$:
--
--   $$
--   \frac{\sqrt5-1}{2}\le\eta<1,\qquad 0<\gamma<\frac1\tau,\qquad 0<\alpha\le\frac{1}{2(\gamma\tau^2+L+\tau)\eta}.
--   $$
--
--   **Formalization Note.** $\gamma<1/\tau$ is written $\gamma\tau<1$, equivalent since $\tau>0$ (part of the standing assumptions).
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, Lemma 4.1, p.13

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **The parameter window of Lemma 4.1.** `(√5 - 1)/2 ≤ η < 1`, `0 < γ < 1/τ` and
`0 < α ≤ 1 / (2(γτ² + L + τ)η)`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, Lemma 4.1, p.13.

Formalization Note: `γ < 1/τ` is written `γ * τ < 1`, which is equivalent for `τ > 0`
(`τ > 0` is part of `Standing`). -/
def Params (η α γ L τ : ℝ) : Prop :=
  (Real.sqrt 5 - 1) / 2 ≤ η ∧ η < 1 ∧ 0 < γ ∧ γ * τ < 1 ∧ 0 < α ∧
    α ≤ 1 / (2 * (γ * τ ^ 2 + L + τ) * η)

end ALAVI


