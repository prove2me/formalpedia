-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPosR
-- name    : DiscreteConvex_AlgorithmsB_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:50:01.46635+00:00
-- url     : https://prove2.me/theorems/b48d2e46-3c9b-4f32-a7dc-a311021b4226
-- title:
--   SuppPosR
-- statement:
--   The positive support of a real vector.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, adjacent to Eq. (10.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, adjacent to Eq. (10.10)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The positive support of a real vector. -/
noncomputable def SuppPosR' (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => 0 < x v)

end DiscreteConvex.AlgorithmsB


