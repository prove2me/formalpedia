-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_SuppNegR
-- name    : DiscreteConvex_CombinatorialC_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:24.054316+00:00
-- url     : https://prove2.me/theorems/d733da36-9ac1-42cd-9b05-7485cb33e8d9
-- title:
--   Negative support of a real vector
-- statement:
--   The negative support $\operatorname{supp}^-(x)=\{i : x_i<0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Eq. (2.21).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, Eq. (2.21)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, Eq. (2.21): the negative support of a real
vector, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The negative support `supp⁻(x) = \{i | x_i < 0\}` (Eq. (2.21)), as a `Finset`. -/
noncomputable def SuppNegR {W : Type*} [Fintype W] [DecidableEq W] (x : W → ℝ) : Finset W :=
  Finset.univ.filter (fun i => x i < 0)

end DiscreteConvex.CombinatorialC


