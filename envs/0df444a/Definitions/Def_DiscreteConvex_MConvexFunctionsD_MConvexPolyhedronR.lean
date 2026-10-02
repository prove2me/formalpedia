-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_MConvexPolyhedronR
-- name    : DiscreteConvex_MConvexFunctionsD_MConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:52:10.57514+00:00
-- url     : https://prove2.me/theorems/c90a0f7d-fff5-4602-ad2b-42278706b917
-- title:
--   Real M-convex polyhedron
-- statement:
--   The class $M^0[\mathbb{R}]$ of **real** M-convex polyhedra: a polyhedron $P$ whose indicator satisfies the real exchange axiom (M-EXC[R]).
--
--   This is the class Proposition 6.53 uses. It is strictly larger than the integral class $M^0[\mathbb{Z}|\mathbb{R}]$ of convex hulls of integer M-convex sets: the segment from $(0,0)$ to $(1/2,-1/2)$ lies in $M^0[\mathbb{R}]$ and is the convex hull of no integer set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §6.11, Proposition 6.53.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §6.11, Proposition 6.53

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex

namespace DiscreteConvex.MConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `M⁰[R]` of **real** M-convex polyhedra: a polyhedron whose indicator satisfies the
real exchange axiom (M-EXC[R]). This is the book's class; `MConvexPolyhedron` is the convex hull
of an integer M-convex set, i.e. the *integral* class `M⁰[Z|R]`, whose members have integral
vertices. The segment from `(0,0)` to `(1/2,-1/2)` is in `M⁰[R]` and is the hull of no integer
set, so Proposition 6.53 is false with the integral class. -/
noncomputable def MConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  (∃ (m : ℕ) (a : Fin m → V → ℝ) (b : Fin m → ℝ),
    P = {x : V → ℝ | ∀ i, ∑ v, a i v * x v ≤ b i}) ∧
  MExchangeAxiomR (fun x => if x ∈ P then (0 : WithTop ℝ) else ⊤)

end DiscreteConvex.MConvexFunctionsD


