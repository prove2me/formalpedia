-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_M2ConvexPolyhedronR
-- name    : DiscreteConvex_NetworkFlowsB_M2ConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:08.661135+00:00
-- url     : https://prove2.me/theorems/4fcd4315-769e-434d-abaf-16e9b29d1e66
-- title:
--   Real M2-convex polyhedron
-- statement:
--   The class $M^0_2[\mathbb{R}]$ of **real** $M_2$-convex polyhedra: the intersection of two real M-convex polyhedra.
--
--   Theorem 9.15 (1) holds in this class; integrality is what its separate clause (2) adds.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.3, Theorem 9.15.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.3, Theorem 9.15

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_MConvexPolyhedronR

namespace DiscreteConvex.NetworkFlowsB

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `M⁰₂[R]` of **real** M₂-convex polyhedra: the intersection of two real M-convex
polyhedra. `M2ConvexPolyhedron` is the convex hull of an integer M₂-convex set, i.e. the integral
class; Theorem 9.15 (1) holds in the real class and the integrality is its separate clause (2). -/
def M2ConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  ∃ P1 P2 : Set (V → ℝ), MConvexPolyhedronR P1 ∧ MConvexPolyhedronR P2 ∧ P = P1 ∩ P2

end DiscreteConvex.NetworkFlowsB


