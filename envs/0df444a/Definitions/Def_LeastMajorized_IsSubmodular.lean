-- Prove2me | Definitions.Def_LeastMajorized_IsSubmodular
-- name    : LeastMajorized_IsSubmodular
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:35.782228+00:00
-- url     : https://prove2.me/theorems/997082d3-cef2-4f37-8b12-f08bf95b3ca1
-- title:
--   Submodular set function $f:2^N\to\mathbb R$ with $f(\emptyset)=0$
-- statement:
--   Let $N=\{1,\dots,n\}$ and let $2^N$ be its power set. A set function $f:2^N\to\mathbb R$ is **submodular** if $f(\emptyset)=0$ and
--
--   $$
--   f(A)+f(B)\ \ge\ f(A\cup B)+f(A\cap B)\qquad\text{for all }A,B\in 2^N .
--   $$
--
--   Submodular functions define the submodular and base polyhedra $P(f)$ and $B(f)$, the central objects of the mission's characterization.
--
--   **Formalization Note** $N$ is `Fin n` (0-based) and $2^N$ is `Finset (Fin n)`. The normalization $f(\emptyset)=0$ is part of the definition, as in the paper ("where we assume that $f(\emptyset)=0$"). The paper prints the codomain as $\mathbb R^n$, a typo for $\mathbb R$.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §2.2, p.5

import Mathlib

namespace LeastMajorized

/-- **Submodular set function**, Schoot Uiterkamp, *A characterization of simultaneous
optimization, majorization, and (bi)submodular polyhedra*, arXiv:2201.06596v2, §2.2, p.5:
"A set function `f: 2^N → ℝⁿ` is submodular if `f(A) + f(B) ≥ f(A ∪ B) + f(A ∩ B)` for all
`A, B ∈ 2^N`, where we assume that `f(∅) = 0`."

**Formalization Note** The ground set `N = {1, …, n}` is `Fin n` (0-based) and `2^N` is
`Finset (Fin n)`. The printed codomain `ℝⁿ` is a typo for `ℝ` (the values `f(A)` are compared
with the scalars `x(A)` in `P(f)`). The normalization `f(∅) = 0` is part of the definition, as
in the paper. -/
def IsSubmodular {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  f ∅ = 0 ∧ ∀ A B : Finset (Fin n), f (A ∪ B) + f (A ∩ B) ≤ f A + f B

end LeastMajorized


