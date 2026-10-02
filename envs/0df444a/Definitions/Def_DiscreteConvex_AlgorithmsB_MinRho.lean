-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
-- name    : DiscreteConvex_AlgorithmsB_MinRho
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:47.252976+00:00
-- url     : https://prove2.me/theorems/fb635c61-f6c5-4e36-9cc2-0372c39a8c6a
-- title:
--   MinRho
-- statement:
--   $\min\{\rho(X)\mid X\subseteq V\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.11)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `min{ρ(X) | X ⊆ V}`. -/
def MinRho (rho : Finset V → ℤ) : ℤ :=
  (Finset.univ : Finset (Finset V)).inf' ⟨∅, Finset.mem_univ _⟩ rho

end DiscreteConvex.AlgorithmsB


