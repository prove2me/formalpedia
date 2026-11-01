-- Prove2me | Definitions.Def_ALAVI_IsVIP
-- name    : ALAVI_IsVIP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:52.469188+00:00
-- url     : https://prove2.me/theorems/786230fe-04fb-40a9-b235-86bee589ced8
-- title:
--   Solutions of the conically constrained mixed variational inequality (VIP)
-- statement:
--   With $\Gamma=\{u\in U:\Theta(u)\in-C\}$, a point $u^*$ **solves (VIP)** if $u^*\in\Gamma$, $J(u^*)<+\infty$ and
--
--   $$
--   \langle G(u^*),u-u^*\rangle+J(u)-J(u^*)\ge0\qquad\forall u\in\Gamma .
--   $$
--
--   **Formalization Note.** $J$ is extended-real valued; the inequality is required at $u\in\Gamma\cap\operatorname{dom}J$ in real arithmetic (at $u\notin\operatorname{dom}J$ it reads $+\infty\ge0$).
-- source:
--   Zhao, Zhu & Zhang, An Augmented Lagrangian Approach to Conically Constrained Non-monotone Variational Inequality Problems, arXiv:2306.01214v1, (VIP), display (1), p.2

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj

namespace ALAVI

/-- **(VIP), display (1).** `u ∈ Γ = {u ∈ U | Θ(u) ∈ -C}` and
`⟨G(u), w - u⟩ + J(w) - J(u) ≥ 0` for all `w ∈ Γ`.

Zhao, Zhu & Zhang, arXiv:2306.01214v1, (VIP) and (1), p.2.

Formalization Note: `J` is extended-real valued. A solution must have `J(u) < +∞`
(`u ∈ effDom J`), and the inequality is required at `w ∈ Γ ∩ dom J`, computed with real values
`(J w).toReal`; at `w ∉ dom J` the printed inequality reads `+∞ ≥ 0`. -/
def IsVIP {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (u : E) : Prop :=
  u ∈ U ∧ -Θ u ∈ C ∧ u ∈ GoldenRatioVI.Fixed.effDom J ∧
    ∀ w ∈ U, -Θ w ∈ C → w ∈ GoldenRatioVI.Fixed.effDom J →
      0 ≤ inner ℝ (G u) (w - u) + (J w).toReal - (J u).toReal

end ALAVI


