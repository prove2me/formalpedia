-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_EmbedZR
-- name    : DiscreteConvex_IntegralConvexityC_EmbedZR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:14.127089+00:00
-- url     : https://prove2.me/theorems/d604bebd-03aa-4b96-8382-ff33fe0920cb
-- title:
--   Embedding of integer vectors into real vectors
-- statement:
--   $\mathbb Z^n\hookrightarrow\mathbb R^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508

import Mathlib

/-!
The standard embedding of integer vectors into real vectors, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The embedding `Zⁿ ↪ Rⁿ`. -/
def EmbedZR {n : ℕ} (x : Fin n → ℤ) : Fin n → ℝ :=
  fun i => (x i : ℝ)

end DiscreteConvex.IntegralConvexityC


