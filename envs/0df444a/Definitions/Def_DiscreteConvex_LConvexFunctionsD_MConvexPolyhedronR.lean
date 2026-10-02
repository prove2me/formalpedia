-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
-- name    : DiscreteConvex_LConvexFunctionsD_MConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:31.509791+00:00
-- url     : https://prove2.me/theorems/37c2ff6c-3484-4231-af21-f1db1ef866e8
-- title:
--   Real M-convex polyhedron
-- statement:
--   The class $M^0[\mathbb{R}]$ of **real** M-convex polyhedra: a polyhedron satisfying the real exchange axiom (B-EXC[R]).
--
--   It is strictly larger than the integral class $M^0[\mathbb{Z}|\mathbb{R}]$ of convex hulls of integer M-convex sets: the segment from $(0,0)$ to $(1/2,-1/2)$ lies in $M^0[\mathbb{R}]$ and is the convex hull of no integer set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §7.6, Theorem 7.45 (c).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §7.6, Theorem 7.45

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsPolyhedronW

namespace DiscreteConvex.LConvexFunctionsD

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `M⁰[R]` of **real** M-convex polyhedra: a polyhedron satisfying the real exchange
axiom (B-EXC[R]). `MConvexPolyhedron` is the convex hull of an integer M-convex set, i.e. the
*integral* class `M⁰[Z|R]`. Theorem 7.45 (c) concludes in the real class: the subdifferential of
`g(p) = (1/2) max(p₁ - p₂, 0)` at `0` is the segment from `(0,0)` to `(1/2,-1/2)`, which is the
convex hull of no integer set. -/
def MConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedronW P ∧
    ∀ x ∈ P, ∀ y ∈ P, ∀ i : V, 0 < x i - y i →
      ∃ j : V, x j - y j < 0 ∧ ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
        (fun v => x v - α * ((if v = i then (1 : ℝ) else 0) - (if v = j then 1 else 0))) ∈ P ∧
        (fun v => y v + α * ((if v = i then (1 : ℝ) else 0) - (if v = j then 1 else 0))) ∈ P

end DiscreteConvex.LConvexFunctionsD


