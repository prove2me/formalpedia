-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ToEReal
-- name    : DiscreteConvex_ConjugacyDualityB_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:56.878009+00:00
-- url     : https://prove2.me/theorems/3dc57cbc-380c-4906-be80-822f2ecf2064
-- title:
--   ToEReal
-- statement:
--   The canonical embedding $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The canonical embedding `R∪{+∞} ↪ R∪{±∞}`. -/
def ToEReal (v : WithTop ℝ) : EReal := WithBot.some v

end DiscreteConvex.ConjugacyDualityB


