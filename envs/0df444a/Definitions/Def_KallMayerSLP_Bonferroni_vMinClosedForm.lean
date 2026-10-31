-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_vMinClosedForm
-- name    : KallMayerSLP_Bonferroni_vMinClosedForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:51.022992+00:00
-- url     : https://prove2.me/theorems/cc1eac3d-461c-4813-b8b5-098a8a94054a
-- title:
--   Closed form of the lower Boole–Bonferroni bound
-- statement:
--   The closed form of the lower bound is
--   $$
--   V_{\min}=\frac{2}{k^*+1}S_1-\frac{2}{k^*(k^*+1)}S_2,\qquad k^*=\left\lfloor\frac{2S_2}{S_1}\right\rfloor+1.
--   $$
--   It is the optimal value of the linear program (3.14) when $S_1,S_2$ are binomial moments with $S_1>0$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.15), p.288 (PDF 297)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_kStar

namespace KallMayerSLP.Bonferroni

/-- The lower Boole–Bonferroni bound
`V_min = 2/(k*+1) S₁ - 2/(k*(k*+1)) S₂`, with `k*` as in `kStar`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.15), p.288 (PDF 297). -/
noncomputable def vMinClosedForm (S₁ S₂ : ℝ) : ℝ :=
  2 / ((kStar S₁ S₂ : ℝ) + 1) * S₁
    - 2 / ((kStar S₁ S₂ : ℝ) * ((kStar S₁ S₂ : ℝ) + 1)) * S₂

end KallMayerSLP.Bonferroni


