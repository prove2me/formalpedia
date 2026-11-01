-- Prove2me | Definitions.Def_SConvexGS_IsConcaveFn
-- name    : SConvexGS_IsConcaveFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:05.780227+00:00
-- url     : https://prove2.me/theorems/62cd5c37-6372-4b92-843f-607214a43e26
-- title:
--   Concave function with values in $[-\infty,\infty)$
-- statement:
--   A function $f:\mathbb R^n\to[-\infty,\infty)$ is concave if $\operatorname{dom}(f)$ is a convex set and $f$ satisfies the concavity inequality on it.
--
--   It is the concavity needed for the conjugate duality between $f$ and $f_*$.
--
--   **Formalization Note** The inequality is stated for the real function $x\mapsto f(x)$ on $\operatorname{dom}(f)$, because `ConcaveOn` needs a module as target. The codomain is a hypothesis of each theorem.
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9

import Mathlib
import Definitions.Def_SConvexGS_dom

namespace SConvexGS

/-- Concavity of a function `f : ℝⁿ → [−∞, ∞)` (Chen, Li, *S-Convexity and Gross Substitutability*,
SSRN 3549632 (PDF of 2021-10-29), §1.4, p.9).

Formalization Note: Mathlib's `ConcaveOn` needs a module as target and `EReal` is not one, so the
inequality is stated for `toReal ∘ f` on `dom f`, which includes convexity of `dom f`. Since
`toReal ⊥ = 0`, the set must be `dom f` and never `Set.univ`. Together with `∀ x, f x ≠ ⊤` this is
concavity of the extended-valued `f`. -/
def IsConcaveFn {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  ConcaveOn ℝ (dom f) (fun x => (f x).toReal)

end SConvexGS


