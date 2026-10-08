-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_R1
-- name    : YoungConventions_RiskDominance_R1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:11.959125+00:00
-- url     : https://prove2.me/theorems/939f5a02-a585-4395-ad6d-e11d7efb1974
-- title:
--   The risk ratio $R_1$
-- statement:
--   For a $2\times2$ game in normal form,
--   $$R_1=\min\Big\{\frac{a_{11}-a_{21}}{a_{11}-a_{12}-a_{21}+a_{22}},\ \frac{b_{11}-b_{12}}{b_{11}-b_{12}-b_{21}+b_{22}}\Big\}.$$
--   The first ratio is the least fraction of strategy $2$ in Column's sampled plays that makes $2$ a best reply for Row, the second the same for Column. $\lceil R_1k\rceil$ is the resistance of leaving $h_1$ for $h_2$.
--
--   **Formalization Note** Indices $1,2$ are `0, 1`. Under the normal form $0<R_1<1$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 71

import Mathlib

namespace YoungConventions.RiskDominance

/-- **`R₁`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 71 (PDF p. 16):
`R₁ = min{ (a₁₁ − a₂₁)/(a₁₁ − a₁₂ − a₂₁ + a₂₂), (b₁₁ − b₁₂)/(b₁₁ − b₁₂ − b₂₁ + b₂₂) }`.

**Formalization Note.** Paper indices `1, 2` are `0, 1`. Under `IsNormalForm` both denominators are
positive and `0 < R₁ < 1`. -/
noncomputable def R1 (a b : Fin 2 → Fin 2 → ℝ) : ℝ :=
  min ((a 0 0 - a 1 0) / (a 0 0 - a 0 1 - a 1 0 + a 1 1))
      ((b 0 0 - b 0 1) / (b 0 0 - b 0 1 - b 1 0 + b 1 1))

end YoungConventions.RiskDominance


