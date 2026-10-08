-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_R2
-- name    : YoungConventions_RiskDominance_R2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:24.418902+00:00
-- url     : https://prove2.me/theorems/6cfacb6e-aee0-4089-b6f4-836a558be375
-- title:
--   The risk ratio $R_2$
-- statement:
--   For a $2\times2$ game in normal form,
--   $$R_2=\min\Big\{\frac{a_{22}-a_{12}}{a_{11}-a_{12}-a_{21}+a_{22}},\ \frac{b_{22}-b_{21}}{b_{11}-b_{12}-b_{21}+b_{22}}\Big\}.$$
--   $(1,1)$ weakly risk dominates $(2,2)$ if $R_1\ge R_2$, and risk dominates it (in the terminology of Harsanyi and Selten) if $R_1>R_2$.
--
--   **Formalization Note** Indices $1,2$ are `0, 1`. Under the normal form $0<R_2<1$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72

import Mathlib

namespace YoungConventions.RiskDominance

/-- **`R₂`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72 (PDF p. 17):
`R₂ = min{ (a₂₂ − a₁₂)/(a₁₁ − a₁₂ − a₂₁ + a₂₂), (b₂₂ − b₂₁)/(b₁₁ − b₁₂ − b₂₁ + b₂₂) }`.

**Formalization Note.** Paper indices `1, 2` are `0, 1`. Under `IsNormalForm` both denominators are
positive and `0 < R₂ < 1`. -/
noncomputable def R2 (a b : Fin 2 → Fin 2 → ℝ) : ℝ :=
  min ((a 1 1 - a 0 1) / (a 0 0 - a 0 1 - a 1 0 + a 1 1))
      ((b 1 1 - b 1 0) / (b 0 0 - b 0 1 - b 1 0 + b 1 1))

end YoungConventions.RiskDominance


