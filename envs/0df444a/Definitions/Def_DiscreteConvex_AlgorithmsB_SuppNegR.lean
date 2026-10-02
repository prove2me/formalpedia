-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNegR
-- name    : DiscreteConvex_AlgorithmsB_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:02.552991+00:00
-- url     : https://prove2.me/theorems/34e25757-15c5-41d5-9dbb-0472848a36dc
-- title:
--   SuppNegR
-- statement:
--   The negative support of a real vector.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, adjacent to Eq. (10.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, adjacent to Eq. (10.10)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The negative support of a real vector. -/
noncomputable def SuppNegR' (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < 0)

-- ===== Linear orderings, extreme bases (§10.2.1) =====

end DiscreteConvex.AlgorithmsB


