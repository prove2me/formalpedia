-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR
-- name    : DiscreteConvex_IntegralConvexityB_EmbedZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:01.143636+00:00
-- url     : https://prove2.me/theorems/bfc24231-042b-4be9-85f0-62d0fc7d1f6f
-- title:
--   Embedding of integer vectors into real vectors
-- statement:
--   $\mathbb Z^V\hookrightarrow\mathbb R^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508

import Mathlib

/-!
The standard embedding of integer vectors into real vectors, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The embedding `Zⱽ ↪ Rⱽ`. -/
def EmbedZR {V : Type*} (x : V → ℤ) : V → ℝ :=
  fun v => (x v : ℝ)

end DiscreteConvex.IntegralConvexityB


