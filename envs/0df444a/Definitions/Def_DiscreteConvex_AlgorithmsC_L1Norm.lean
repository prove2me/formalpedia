-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_L1Norm
-- name    : DiscreteConvex_AlgorithmsC_L1Norm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:50.934352+00:00
-- url     : https://prove2.me/theorems/f2a88787-10ba-4a6e-a244-542bb3289771
-- title:
--   L1Norm
-- statement:
--   The $\ell^1$-norm of an integer vector.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.34)/(10.37), adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.307, Eq. (10.34)/(10.37), adjacent

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `ℓ¹`-norm of an integer vector. -/
def L1Norm {W : Type*} [Fintype W] (x : W → ℤ) : ℤ := ∑ v, |x v|

end DiscreteConvex.AlgorithmsC


