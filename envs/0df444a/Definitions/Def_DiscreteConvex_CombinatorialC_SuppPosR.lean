-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_SuppPosR
-- name    : DiscreteConvex_CombinatorialC_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:22.458972+00:00
-- url     : https://prove2.me/theorems/f76a8e98-0b58-41d9-ae3d-7f02caf7c4b2
-- title:
--   Positive support of a real vector
-- statement:
--   The positive support $\operatorname{supp}^+(x)=\{i : x_i>0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Eq. (2.21).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Eq. (2.21)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, Eq. (2.21): the positive support of a real
vector, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The positive support `supp⁺(x) = \{i | x_i > 0\}` (Eq. (2.21)), as a `Finset`. -/
noncomputable def SuppPosR {W : Type*} [Fintype W] [DecidableEq W] (x : W → ℝ) : Finset W :=
  Finset.univ.filter (fun i => 0 < x i)

end DiscreteConvex.CombinatorialC


