-- Prove2me | Definitions.Def_LL_SchoenfeldLiS76_liPart
-- name    : LL_SchoenfeldLiS76_liPart
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-23T17:35:03.12084+00:00
-- url     : https://prove2.me/theorems/70e73b8a-580d-4b62-a07e-d7e7ce74b280
-- title:
--   Truncated principal value integral $\int_0^{1-\varepsilon}+\int_{1+\varepsilon}^x$
-- statement:
--   For real $x$ and $\varepsilon$, $\operatorname{liPart}(x,\varepsilon)=\int_0^{1-\varepsilon}\frac{dt}{\log t}+\int_{1+\varepsilon}^{x}\frac{dt}{\log t}$, both oriented interval integrals, with the convention $1/\log t=0$ where $\log t=0$.

import Mathlib

namespace LL_SchoenfeldLiS76

noncomputable section

open Real MeasureTheory Filter Topology Set intervalIntegral

noncomputable def liPart (x e : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1 - e, 1 / log t) + ∫ t in 1 + e..x, 1 / log t

end

end LL_SchoenfeldLiS76


