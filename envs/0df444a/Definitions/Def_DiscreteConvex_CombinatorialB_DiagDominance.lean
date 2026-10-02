-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance
-- name    : DiscreteConvex_CombinatorialB_DiagDominance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:14.213653+00:00
-- url     : https://prove2.me/theorems/f1d2dc92-5a56-427e-a799-f69d35167573
-- title:
--   Diagonal dominance (2.10)
-- statement:
--   A matrix $L$ has **diagonal dominance**: $\sum_j \ell_{ij} \ge 0$ for every row $i$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.62, Eq. (2.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.62, Eq. (2.10)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.62, Eq. (2.10): diagonal dominance of a
symmetric matrix, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- **Diagonal dominance** (2.10): the row sums of `L` are nonnegative,
`∑_j ℓ_ij ≥ 0` for every `i`. -/
def DiagDominance {V : Type*} [Fintype V] [DecidableEq V] (L : Matrix V V ℝ) : Prop :=
  ∀ i : V, 0 ≤ ∑ j, L i j

end DiscreteConvex.CombinatorialB


