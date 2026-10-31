-- Prove2me | Definitions.Def_ROGCones_CondI
-- name    : ROGCones_CondI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:11.644189+00:00
-- url     : https://prove2.me/theorems/67379ba7-448a-4254-bc62-c7f78abf4029
-- title:
--   Condition (i): some $(\alpha_1,\alpha_2) \neq (0,0)$ has $\alpha_1M_1 + \alpha_2M_2 \succeq 0$
-- statement:
--   Two matrices $M_1, M_2$ satisfy **condition (i)** if some nontrivial linear combination of them is positive semidefinite:
--   $$
--   \exists\, (\alpha_1, \alpha_2) \neq (0, 0) :\quad \alpha_1 M_1 + \alpha_2 M_2 \in \mathbb S^n_+ .
--   $$
--   Geometrically, the two constraints then interact only on a single face of $\mathbb S^n_+$. The requirement $(\alpha_1,\alpha_2)\neq(0,0)$ is essential: the zero combination is always positive semidefinite.
--
--   **Formalization Note** $\mathbb S^n_+$ membership is `Matrix.PosSemidef`.
-- source:
--   Argue, Kılınç-Karzan & Wang, Necessary and sufficient conditions for rank-one generated cones, arXiv:2007.07433v2, Theorems 3 and 4, p.15

import Mathlib

namespace ROGCones

/-- **Condition (i) of Theorems 3 and 4**: a nontrivial combination of `M₁, M₂` is PSD.
Argue, Kılınç-Karzan & Wang, arXiv:2007.07433v2, Theorems 3 and 4, p.15: "(i) there exists
(α₁, α₂) ≠ (0, 0) such that α₁M₁ + α₂M₂ ∈ Sⁿ₊".

**Formalization Note.** Sⁿ₊ membership is `Matrix.PosSemidef`. The requirement
`(α₁, α₂) ≠ (0, 0)` is essential: without it the condition always holds. -/
def CondI {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ α₁ α₂ : ℝ, (α₁, α₂) ≠ (0, 0) ∧ (α₁ • M₁ + α₂ • M₂).PosSemidef

end ROGCones


