-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsTotallyUnimodular
-- name    : DiscreteConvex_IntegralConvexityB_IsTotallyUnimodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:04.148253+00:00
-- url     : https://prove2.me/theorems/ca2b2166-4cc9-4b2a-9983-e2f4875bb48e
-- title:
--   Totally unimodular matrix
-- statement:
--   Every minor is $0$, $1$, or $-1$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.88.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.88

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.88: a totally unimodular matrix, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `A` is **totally unimodular**: every minor (determinant of a square submatrix formed by
choosing any `k` rows and any `k` columns via injective index maps) equals `0`, `1`, or `-1`. -/
def IsTotallyUnimodular {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
    (A : Matrix W V ℝ) : Prop :=
  ∀ (k : ℕ) (rs : Fin k → W) (cs : Fin k → V), Function.Injective rs → Function.Injective cs →
    (A.submatrix rs cs).det = 0 ∨ (A.submatrix rs cs).det = 1 ∨ (A.submatrix rs cs).det = -1

end DiscreteConvex.IntegralConvexityB


