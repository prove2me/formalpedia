-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_AssocFn
-- name    : DiscreteConvex_LConvexFunctionsB_AssocFn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:22:11.031058+00:00
-- url     : https://prove2.me/theorems/cceb3939-3411-46b0-95fa-e7a8428d82c5
-- title:
--   AssocFn
-- statement:
--   The function $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ with $\operatorname{dom} g\subseteq\{0,1\}^V$ associated to a set function $\rho$: $g(\chi_X)=\rho(X)$, $g(p)=+\infty$ otherwise.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, Eq. (7.5).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.179, Eq. (7.5)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_IndicatorVec

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The function `g : Zⱽ → R∪{+∞}` with `dom g ⊆ {0,1}ⱽ` associated to a set function `ρ`,
Eq. (7.5): `g(χ_X) = ρ(X)`, `g(p) = +∞` otherwise. -/
noncomputable def AssocFn (rho : Finset V → WithTop ℝ) : (V → ℤ) → WithTop ℝ :=
  fun p => if h : ∃ X : Finset V, p = IndicatorVec X then rho h.choose else ⊤

end DiscreteConvex.LConvexFunctionsB


