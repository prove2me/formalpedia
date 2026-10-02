-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot
-- name    : DiscreteConvex_EconomicEquilibriumB_ToERealOfBot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:51.266005+00:00
-- url     : https://prove2.me/theorems/1cd9f323-3bca-48e9-9bab-0bd9ff18e2bf
-- title:
--   ToERealOfBot
-- statement:
--   The canonical embedding $\mathbb R\cup\{-\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared, dualized.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared, dualized

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The canonical embedding `R∪{−∞} ↪ R∪{±∞}`. -/
noncomputable def ToERealOfBot (v : WithBot ℝ) : EReal := v.elim ⊥ (fun r => (r : EReal))

end DiscreteConvex.EconomicEquilibriumB


