-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_Boundary
-- name    : DiscreteConvex_CombinatorialC_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:02.428516+00:00
-- url     : https://prove2.me/theorems/f6bd0fb2-dc22-4783-ba7a-1689f5c38252
-- title:
--   Boundary (net outflow) of a flow
-- statement:
--   $\partial\xi(v)=\sum_{a:\partial^+a=v}\xi(a)-\sum_{a:\partial^-a=v}\xi(a)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.74, Eq. (2.27).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.74, Eq. (2.27)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.74, Eq. (2.27): the boundary (net outflow) of
a flow, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The boundary `∂ξ(v) = ∑_{a: ∂⁺a=v} ξ(a) − ∑_{a: ∂⁻a=v} ξ(a)` (Eq. (2.27)): the net flow
leaving vertex `v`, given the initial-vertex map `src` and terminal-vertex map `dst`. -/
noncomputable def Boundary {V A : Type*} [Fintype A] (src dst : A → V) [DecidableEq V]
    (xi : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => src a = v), xi a) -
    (∑ a ∈ Finset.univ.filter (fun a => dst a = v), xi a)

end DiscreteConvex.CombinatorialC


