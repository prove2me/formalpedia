-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_QMw
-- name    : DiscreteConvex_MConvexFunctions_Quasi_QMw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:48.080339+00:00
-- url     : https://prove2.me/theorems/30d3891e-85e3-4410-86dc-fe04c91b5b19
-- title:
--   Weak quasi M-convexity (QMw)
-- statement:
--   Axiom **(QMw)**: for distinct $x, y \in \operatorname{dom} f$, there exist $u \in \operatorname{supp}^+(x-y)$ and $v \in \operatorname{supp}^-(x-y)$ with $f(x-\chi_u+\chi_v) \le f(x)$ or $f(y+\chi_u-\chi_v) \le f(y)$. A function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ with $\operatorname{dom} f \ne \emptyset$ satisfying this is **weakly quasi M-convex**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.169, axiom (QMw).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.169, axiom (QMw)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.169, axiom (QMw): the weak quasi M-convexity
condition, in `DiscreteConvex.MConvexFunctions.Quasi`. Builds on chunk `06-mconvex-functions-i`'s
`DiscreteConvex.MConvexFunctions` definitions per the series' shared book namespace.
-/

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Axiom **(QMw)** (p.169): for distinct `x, y ∈ dom f`, there exist `u ∈ supp⁺(x-y)` and
`v ∈ supp⁻(x-y)` with `f(x - χ_u + χ_v) ≤ f(x)` or `f(y + χ_u - χ_v) ≤ f(y)`. A function
`f : Zⱽ → R ∪ {+∞}` with `dom f ≠ ∅` satisfying this is **weakly quasi M-convex**. -/
def QMw {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f (fun w => x w - CharVec u w + CharVec v w) ≤ f x ∨
      f (fun w => y w + CharVec u w - CharVec v w) ≤ f y

end DiscreteConvex.MConvexFunctions.Quasi


