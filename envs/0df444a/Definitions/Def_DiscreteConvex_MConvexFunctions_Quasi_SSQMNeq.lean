-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeq
-- name    : DiscreteConvex_MConvexFunctions_Quasi_SSQMNeq
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:02:12.732995+00:00
-- url     : https://prove2.me/theorems/4d7fceb2-af72-4c4f-b596-8bbd931b00bd
-- title:
--   Strict-sense quasi M-convexity relevant to minimization (SSQM-neq)
-- statement:
--   Axiom **(SSQM$_{\ne}$)**: for $x, y \in \operatorname{dom} f$ with $f(x) \ne f(y)$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ with $f(x-\chi_u+\chi_v) < f(x)$, or $f(y+\chi_u-\chi_v) < f(y)$, or both $f(x-\chi_u+\chi_v)=f(x)$ and $f(y+\chi_u-\chi_v)=f(y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, axiom (SSQM≠).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, axiom (SSQM≠)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.172, axiom (SSQM≠): the strict-sense quasi
M-convexity condition relevant to minimization, in `DiscreteConvex.MConvexFunctions.Quasi`.
-/

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Axiom **(SSQM≠)** (p.172): for `x, y ∈ dom f` with `f(x) ≠ f(y)` and `u ∈ supp⁺(x-y)`,
there is `v ∈ supp⁻(x-y)` with `f(x-χ_u+χ_v) < f(x)`, or `f(y+χ_u-χ_v) < f(y)`, or both
`f(x-χ_u+χ_v) = f(x)` and `f(y+χ_u-χ_v) = f(y)`. -/
def SSQMNeq {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f (fun w => x w - CharVec u w + CharVec v w) < f x ∨
      f (fun w => y w + CharVec u w - CharVec v w) < f y ∨
      (f (fun w => x w - CharVec u w + CharVec v w) = f x ∧
        f (fun w => y w + CharVec u w - CharVec v w) = f y)

end DiscreteConvex.MConvexFunctions.Quasi


