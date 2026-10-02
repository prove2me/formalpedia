-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToEReal
-- name    : DiscreteConvex_EconomicEquilibriumB_ToEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:49.653675+00:00
-- url     : https://prove2.me/theorems/8e0eab4c-a680-413e-9c68-c5b1a0a45326
-- title:
--   ToEReal
-- statement:
--   The canonical embedding $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The canonical embedding `R∪{+∞} ↪ R∪{±∞}`. -/
def ToEReal (v : WithTop ℝ) : EReal := WithBot.some v

end DiscreteConvex.EconomicEquilibriumB


