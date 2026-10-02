-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_MConvexPolyhedronR
-- name    : DiscreteConvex_NetworkFlowsB_MConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:22:56.185321+00:00
-- url     : https://prove2.me/theorems/b8d1335b-c6b7-4023-a53a-a8715189172c
-- title:
--   Real M-convex polyhedron
-- statement:
--   The class $M^0[\mathbb{R}]$ of **real** M-convex polyhedra: a polyhedron satisfying the real exchange axiom (B-EXC[R]). Unlike the convex hull of an integer M-convex set, it need not be integral.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.3

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `M⁰[R]` of **real** M-convex polyhedra: a polyhedron satisfying the real exchange
axiom (B-EXC[R]). Unlike `MConvexPolyhedron`, the convex hull of an integer M-convex set, it is
not integral. -/
def MConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedron P ∧
    ∀ x ∈ P, ∀ y ∈ P, ∀ i : V, 0 < x i - y i →
      ∃ j : V, x j - y j < 0 ∧ ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
        (fun v => x v - α * ((if v = i then (1 : ℝ) else 0) - (if v = j then 1 else 0))) ∈ P ∧
        (fun v => y v + α * ((if v = i then (1 : ℝ) else 0) - (if v = j then 1 else 0))) ∈ P

end DiscreteConvex.NetworkFlowsB


