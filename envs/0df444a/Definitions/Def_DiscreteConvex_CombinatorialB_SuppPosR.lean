-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
-- name    : DiscreteConvex_CombinatorialB_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:14.205489+00:00
-- url     : https://prove2.me/theorems/6221d2ef-cef1-482d-a46e-1ae81fff134c
-- title:
--   Positive support of a real vector
-- statement:
--   The positive support $\operatorname{supp}^+(x)=\{i : x_i>0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, Eq. (2.21).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, Eq. (2.21)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, Eq. (2.21): the positive support of a
real vector, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- The positive support `supp⁺(x) = \{i | x_i > 0\}` (Eq. (2.21)), as a `Finset` (`V` finite). -/
noncomputable def SuppPosR {V : Type*} [Fintype V] [DecidableEq V] (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun i => 0 < x i)

end DiscreteConvex.CombinatorialB


