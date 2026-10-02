-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_ToEReal3
-- name    : DiscreteConvex_IntegralConvexityC_ToEReal3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:17.150598+00:00
-- url     : https://prove2.me/theorems/91360e69-ce7b-4a18-bb62-114e30bd0afb
-- title:
--   Embedding WithTop R into EReal
-- statement:
--   $\mathbb R\cup\{+\infty\}\hookrightarrow\mathbb R\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508

import Mathlib

/-!
The embedding `R ∪ {+∞} ↪ R ∪ {±∞}`, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The canonical embedding `WithTop ℝ → EReal`. -/
def ToEReal3 (v : WithTop ℝ) : EReal :=
  WithBot.some v

end DiscreteConvex.IntegralConvexityC


