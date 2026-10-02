-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_ToEReal
-- name    : DiscreteConvex_ConjugacyDualityC_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:10.962522+00:00
-- url     : https://prove2.me/theorems/5176e3d6-422c-4c97-8c4e-9f8d35ac3dab
-- title:
--   ToEReal
-- statement:
--   The canonical embedding $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The canonical embedding `R∪{+∞} ↪ R∪{±∞}`. -/
def ToEReal (v : WithTop ℝ) : EReal := WithBot.some v

end DiscreteConvex.ConjugacyDualityC


