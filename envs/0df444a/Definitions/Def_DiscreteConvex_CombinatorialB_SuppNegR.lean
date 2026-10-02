-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR
-- name    : DiscreteConvex_CombinatorialB_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:12.287509+00:00
-- url     : https://prove2.me/theorems/4a62f45d-b1e5-451b-b814-802f9af63bb8
-- title:
--   Negative support of a real vector
-- statement:
--   The negative support $\operatorname{supp}^-(x)=\{i : x_i<0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, Eq. (2.21).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, Eq. (2.21)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, Eq. (2.21): the negative support of a
real vector, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- The negative support `supp⁻(x) = \{i | x_i < 0\}` (Eq. (2.21)), as a `Finset` (`V` finite). -/
noncomputable def SuppNegR {V : Type*} [Fintype V] [DecidableEq V] (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun i => x i < 0)

end DiscreteConvex.CombinatorialB


