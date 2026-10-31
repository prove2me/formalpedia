-- Prove2me | Definitions.Def_LeastMajorized_IsLeastABMajorized
-- name    : LeastMajorized_IsLeastABMajorized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:33.416083+00:00
-- url     : https://prove2.me/theorems/63c951c9-96b7-44ed-93ee-a636ba2052c6
-- title:
--   Least $(a,b)$-majorized element of a set $C$
-- statement:
--   Given $C\subseteq\mathbb R^n$, a vector $x\in C$ is a **least $(a,b)$-majorized element** of $C$ if
--
--   $$
--   x\prec_{(a,b)}y\qquad\text{for all }y\in C .
--   $$
--
--   Such an element simultaneously minimizes every separable objective $\sum_i a_i\phi((y_i+b_i)/a_i)$, $\phi$ continuous convex, over $C$. Its existence for all $(a,b)$ characterizes base polyhedra (Theorem 5).
--
--   **Formalization Note** Membership $x\in C$ is part of the definition, as in the paper.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §3.2, p.9

import Mathlib
import Definitions.Def_LeastMajorized_ABMajorized

namespace LeastMajorized

/-- **Least `(a, b)`-majorized element**, Schoot Uiterkamp, arXiv:2201.06596v2, §3.2, p.9: given
`C ⊆ ℝⁿ`, "a vector `x ∈ C` is a least `(a, b)`-majorized element of `C` if `x ≺_(a,b) y` for all
`y ∈ C`."

**Formalization Note** Membership `x ∈ C` is part of the definition, as in the paper. -/
def IsLeastABMajorized {n : ℕ} (a b : Fin n → ℝ) (C : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, ABMajorized a b x y

end LeastMajorized


