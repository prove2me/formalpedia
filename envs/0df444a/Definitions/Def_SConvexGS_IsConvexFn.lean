-- Prove2me | Definitions.Def_SConvexGS_IsConvexFn
-- name    : SConvexGS_IsConvexFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:59.719934+00:00
-- url     : https://prove2.me/theorems/7292522a-af64-4a09-a956-82c6c4583e88
-- title:
--   Convex function with values in $(-\infty,\infty]$
-- statement:
--   A function $g:\mathbb R^n\to(-\infty,\infty]$ is convex if $\operatorname{dom}(g)$ is a convex set and $g$ satisfies the convexity inequality on it.
--
--   This is the convexity clause of Definition 1.
--
--   **Formalization Note** Mathlib's `ConvexOn` needs a module as target, so the inequality is stated for the real function $x\mapsto g(x)$ on $\operatorname{dom}(g)$, and `ConvexOn` includes convexity of that set. The codomain is a separate clause of `IsSConvex`.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9, and Definition 1, p.10

import Mathlib
import Definitions.Def_SConvexGS_dom

namespace SConvexGS

/-- Convexity of a function `g : ℝⁿ → (−∞, ∞]` (Chen, Li, *S-Convexity and Gross Substitutability*,
SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9, and Definition 1, p.10).

Formalization Note: Mathlib's `ConvexOn` needs a module as target and `EReal` is not one, so the
inequality is stated for `toReal ∘ g` on `dom g`, which includes convexity of `dom g`. Since
`toReal ⊤ = 0`, the set must be `dom g` and never `Set.univ`. Together with `∀ x, g x ≠ ⊥` this is
convexity of the extended-valued `g`. -/
def IsConvexFn {n : ℕ} (g : (Fin n → ℝ) → EReal) : Prop :=
  ConvexOn ℝ (dom g) (fun x => (g x).toReal)

end SConvexGS


