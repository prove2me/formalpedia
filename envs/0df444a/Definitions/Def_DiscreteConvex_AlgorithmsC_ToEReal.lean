-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_ToEReal
-- name    : DiscreteConvex_AlgorithmsC_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:19:09.574221+00:00
-- url     : https://prove2.me/theorems/3f14a9e1-6bf9-46e6-ba18-52733e7b2ca0
-- title:
--   ToEReal
-- statement:
--   The canonical embedding $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The canonical embedding `R∪{+∞} ↪ R∪{±∞}`. -/
def ToEReal (v : WithTop ℝ) : EReal := WithBot.some v

end DiscreteConvex.AlgorithmsC


