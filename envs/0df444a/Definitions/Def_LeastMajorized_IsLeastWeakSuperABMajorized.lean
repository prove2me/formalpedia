-- Prove2me | Definitions.Def_LeastMajorized_IsLeastWeakSuperABMajorized
-- name    : LeastMajorized_IsLeastWeakSuperABMajorized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:35.421538+00:00
-- url     : https://prove2.me/theorems/02e0fef6-00b6-419b-9c7e-253d4a8d2b54
-- title:
--   Least weakly $(a,b)$-supermajorized element of a set $C$
-- statement:
--   Given $C\subseteq\mathbb R^n$, a vector $x\in C$ is a **least weakly $(a,b)$-supermajorized element** of $C$ if
--
--   $$
--   x\prec^{\uparrow}_{(a,b)}y\qquad\text{for all }y\in C .
--   $$
--
--   Its existence for all $b$ (with $a=1$) is the hypothesis of Lemma 14.
--
--   **Formalization Note** Membership $x\in C$ is part of the definition, as in the paper.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §3.2, p.9

import Mathlib
import Definitions.Def_LeastMajorized_WeakSuperABMajorized

namespace LeastMajorized

/-- **Least weakly `(a, b)`-supermajorized element**, Schoot Uiterkamp, arXiv:2201.06596v2, §3.2,
p.9: given `C ⊆ ℝⁿ`, "a vector `x ∈ C` is a least weakly `(a, b)`-supermajorized element of `C`
if `x ≺↑_(a,b) y` for all `y ∈ C`."

**Formalization Note** Membership `x ∈ C` is part of the definition, as in the paper. -/
def IsLeastWeakSuperABMajorized {n : ℕ} (a b : Fin n → ℝ) (C : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, WeakSuperABMajorized a b x y

end LeastMajorized


