-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_ExtendOn
-- name    : DiscreteConvex_CombinatorialC_ExtendOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:03.131084+00:00
-- url     : https://prove2.me/theorems/ae296196-c437-4f22-b8c8-d296e5d8bf41
-- title:
--   Extending a vector on a subset by a background vector
-- statement:
--   Agrees with $v_P$ on $P$, with the background vector outside $P$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83

import Mathlib

/-!
Extending a vector defined on a subset `P` of arcs by a fixed background vector elsewhere,
used to view `F(w,c)` as a function of `w_P` (or `c_P`) alone (Murota, *Discrete Convex
Analysis*, SIAM 2003, p.83), in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- `ExtendOn base P vP` agrees with `vP` on `P` and with `base` outside `P`. -/
def ExtendOn {A : Type*} [DecidableEq A] (base : A → ℝ) (P : Finset A) (vP : P → ℝ) : A → ℝ :=
  fun a => if h : a ∈ P then vP ⟨a, h⟩ else base a

end DiscreteConvex.CombinatorialC


