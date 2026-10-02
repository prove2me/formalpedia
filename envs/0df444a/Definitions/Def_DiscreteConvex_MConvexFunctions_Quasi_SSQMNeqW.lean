-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_Quasi_SSQMNeqW
-- name    : DiscreteConvex_MConvexFunctions_Quasi_SSQMNeqW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:02:30.921989+00:00
-- url     : https://prove2.me/theorems/7a668026-9c29-4a6d-8639-5b0f4549e250
-- title:
--   Weak variant of SSQM-neq (SSQM-neq-w)
-- statement:
--   Axiom **(SSQM$_{\ne,w}$)**: for $x, y \in \operatorname{dom} f$ with $f(x) \ne f(y)$, there exist $u \in \operatorname{supp}^+(x-y)$ and $v \in \operatorname{supp}^-(x-y)$ with $f(x-\chi_u+\chi_v) < f(x)$, or $f(y+\chi_u-\chi_v) < f(y)$, or both $f(x-\chi_u+\chi_v)=f(x)$ and $f(y+\chi_u-\chi_v)=f(y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, axiom (SSQM≠_w).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, axiom (SSQM≠_w)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.172, axiom (SSQM≠_w): the weak variant of
(SSQM≠), in `DiscreteConvex.MConvexFunctions.Quasi`.
-/

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.MConvexFunctions.Quasi

/-- Axiom **(SSQM≠_w)** (p.172): for `x, y ∈ dom f` with `f(x) ≠ f(y)`, there exist
`u ∈ supp⁺(x-y)` and `v ∈ supp⁻(x-y)` with `f(x-χ_u+χ_v) < f(x)`, or `f(y+χ_u-χ_v) < f(y)`, or
both `f(x-χ_u+χ_v) = f(x)` and `f(y+χ_u-χ_v) = f(y)`. -/
def SSQMNeqW {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, f x ≠ f y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f (fun w => x w - CharVec u w + CharVec v w) < f x ∨
      f (fun w => y w + CharVec u w - CharVec v w) < f y ∨
      (f (fun w => x w - CharVec u w + CharVec v w) = f x ∧
        f (fun w => y w + CharVec u w - CharVec v w) = f y)

end DiscreteConvex.MConvexFunctions.Quasi


