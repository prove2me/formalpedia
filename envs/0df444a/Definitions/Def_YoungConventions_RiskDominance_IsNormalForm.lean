-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsNormalForm
-- name    : YoungConventions_RiskDominance_IsNormalForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:18.030897+00:00
-- url     : https://prove2.me/theorems/521df0f1-74cc-48dd-baf2-665363233969
-- title:
--   Normal form of a $2\times2$ game with two strict equilibria
-- statement:
--   The payoffs $(a,b)$ of a $2\times2$ game are in **normal form** if
--   $$a_{11}>a_{21},\qquad b_{11}>b_{12},\qquad a_{22}>a_{12},\qquad b_{22}>b_{21}.$$
--   Then $(1,1)$ and $(2,2)$ are the strict pure-strategy Nash equilibria. Every $2\times2$ game with two strict pure equilibria can be written in this form after relabelling strategies ("Without loss of generality", p. 70).
--
--   **Formalization Note** Indices $1,2$ are `0, 1`. Under these inequalities the denominators of $R_1$ and $R_2$ are positive.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70

import Mathlib

namespace YoungConventions.RiskDominance

/-- **The normal form of a `2 × 2` game with two strict equilibria.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70 (PDF p. 15):
"where `a₁₁ > a₂₁`, `b₁₁ > b₁₂`, `a₂₂ > a₁₂`, and `b₂₂ > b₂₁`. The strict, pure strategy Nash
equilibria are `(1, 1)` and `(2, 2)`."

**Formalization Note.** Paper indices `1, 2` are `0, 1`. These four strict inequalities make the
denominators of `R₁`, `R₂` positive. -/
def IsNormalForm (a b : Fin 2 → Fin 2 → ℝ) : Prop :=
  a 1 0 < a 0 0 ∧ b 0 1 < b 0 0 ∧ a 0 1 < a 1 1 ∧ b 1 0 < b 1 1

end YoungConventions.RiskDominance


