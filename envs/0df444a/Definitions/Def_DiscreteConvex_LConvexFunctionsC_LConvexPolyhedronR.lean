-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LConvexPolyhedronR
-- name    : DiscreteConvex_LConvexFunctionsC_LConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:34:48.737296+00:00
-- url     : https://prove2.me/theorems/ab1aaf53-09ed-4c6f-bd06-ef18824b5fac
-- title:
--   Real L-convex polyhedron
-- statement:
--   The class $L^0[\mathbb{R}]$ of **real** L-convex polyhedra: a polyhedron $P$ whose indicator satisfies (SBF[R]) and (TRF[R]), i.e. a polyhedron closed under $\vee$, $\wedge$ and translation by the all-ones vector.
--
--   It is strictly larger than the integral class $L^0[\mathbb{Z}|\mathbb{R}]$ of convex hulls of integer L-convex sets: $\{p : p_1 - p_2 \le 1/2\}$ lies in $L^0[\mathbb{R}]$ and is the convex hull of no integer set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §7.5, Proposition 7.34.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §7.5, Proposition 7.34

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedron
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `L⁰[R]` of **real** L-convex polyhedra: a polyhedron whose indicator satisfies
(SBF[R]) and (TRF[R]), i.e. a polyhedron closed under `⊔`, `⊓` and translation by the all-ones
vector. `LConvexPolyhedron` is the convex hull of an integer L-convex set, i.e. the *integral*
class `L⁰[Z|R]`. Proposition 7.34 concludes in the real class: for `g(p) = max(p₁ - p₂ - 1/2, 0)`
the minimizer set `{p : p₁ - p₂ ≤ 1/2}` is the convex hull of no integer set. -/
noncomputable def LConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedron P ∧
    SBFR (fun p => if p ∈ P then (0 : WithTop ℝ) else ⊤) ∧
    TRFR (fun p => if p ∈ P then (0 : WithTop ℝ) else ⊤)

end DiscreteConvex.LConvexFunctionsC


