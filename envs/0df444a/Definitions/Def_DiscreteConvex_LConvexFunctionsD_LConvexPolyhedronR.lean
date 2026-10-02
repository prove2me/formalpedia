-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_LConvexPolyhedronR
-- name    : DiscreteConvex_LConvexFunctionsD_LConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:53.546758+00:00
-- url     : https://prove2.me/theorems/4bd2e56c-dfe4-438c-9958-987a83d934fd
-- title:
--   Real L-convex polyhedron
-- statement:
--   The class $L^0[\mathbb{R}]$ of **real** L-convex polyhedra: a polyhedron whose indicator satisfies (SBF[R]) and (TRF[R]), i.e. a polyhedron closed under $\vee$, $\wedge$ and translation by the all-ones vector.
--
--   It is strictly larger than the integral class $L^0[\mathbb{Z}|\mathbb{R}]$: the minimizer set $\{p : p_1 - p_2 \le 1/2\}$ of $g(p)=\max(p_1-p_2-1/2,0)$ is the convex hull of no integer set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §7.6, Theorem 7.45 (d).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §7.6, Theorem 7.45

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsPolyhedronW
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_TRFR

namespace DiscreteConvex.LConvexFunctionsD

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `L⁰[R]` of **real** L-convex polyhedra: a polyhedron whose indicator satisfies
(SBF[R]) and (TRF[R]), i.e. a polyhedron closed under `⊔`, `⊓` and translation by the all-ones
vector. `LConvexPolyhedron` is the convex hull of an integer L-convex set, i.e. the *integral*
class `L⁰[Z|R]`. Theorem 7.45 (d) concludes in the real class: the minimizer set of
`g(p) = max(p₁ - p₂ - 1/2, 0)` is `{p : p₁ - p₂ ≤ 1/2}`, the convex hull of no integer set. -/
noncomputable def LConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedronW P ∧
    SBFR (fun p => if p ∈ P then (0 : WithTop ℝ) else ⊤) ∧
    TRFR (fun p => if p ∈ P then (0 : WithTop ℝ) else ⊤)

end DiscreteConvex.LConvexFunctionsD


