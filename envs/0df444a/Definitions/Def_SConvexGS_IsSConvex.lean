-- Prove2me | Definitions.Def_SConvexGS_IsSConvex
-- name    : SConvexGS_IsSConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:01.231426+00:00
-- url     : https://prove2.me/theorems/90afab0d-cbff-4b32-acc5-8e3b6c99d6ea
-- title:
--   S-convex function
-- statement:
--   A function $g:\mathbb R^n\to(-\infty,\infty]$ is called an **S-convex function** if $g$ is convex and satisfies the exchange property (S-EXC).
--
--   S-convexity is the class of functions the paper introduces. It contains M$^\natural$-convexity as the case $\beta=1$.
--
--   **Formalization Note** The codomain $(-\infty,\infty]$ is the first clause, $g(x)\ne-\infty$ for all $x$.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Definition 1, p.10

import Mathlib
import Definitions.Def_SConvexGS_IsConvexFn
import Definitions.Def_SConvexGS_SExc

namespace SConvexGS

/-- S-convex functions (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of
2021-10-29), Definition 1, p.10): `g : ℝⁿ → (−∞, ∞]` is S-convex if it is convex and satisfies
(S-EXC).

Formalization Note: the codomain `(−∞, ∞]` is the clause `∀ x, g x ≠ ⊥`. -/
def IsSConvex {n : ℕ} (g : (Fin n → ℝ) → EReal) : Prop :=
  (∀ x, g x ≠ ⊥) ∧ IsConvexFn g ∧ SExc g

end SConvexGS


