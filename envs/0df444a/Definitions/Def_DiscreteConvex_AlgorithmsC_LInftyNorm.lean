-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_LInftyNorm
-- name    : DiscreteConvex_AlgorithmsC_LInftyNorm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:55.342503+00:00
-- url     : https://prove2.me/theorems/3b446a2a-e9d3-466c-a15d-c9d8d779ba76
-- title:
--   LInftyNorm
-- statement:
--   The $\ell^\infty$-norm of an integer vector.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.38), adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.38), adjacent

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `ℓ∞`-norm of an integer vector. -/
noncomputable def LInftyNorm {W : Type*} [Fintype W] [Nonempty W] (x : W → ℤ) : ℤ :=
  (Finset.univ : Finset W).sup' Finset.univ_nonempty (fun v => |x v|)

end DiscreteConvex.AlgorithmsC


