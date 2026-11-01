-- Prove2me | Definitions.Def_OfflineToOnline_IsHalfspaceSatisfiable
-- name    : OfflineToOnline_IsHalfspaceSatisfiable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:41.960745+00:00
-- url     : https://prove2.me/theorems/540876ba-b927-4f9a-bae9-a5181e7b1262
-- title:
--   Halfspace-satisfiable target set
-- statement:
--   A target set $S\subseteq\mathbb R^d$ is **halfspace-satisfiable** in the Blackwell game $(\mathcal X,\mathcal Y,\boldsymbol p)$ if every halfspace containing $S$ is satisfiable: for every $a\in\mathbb R^d$ and $c\in\mathbb R$ with $S\subseteq H=\{u:\langle a,u\rangle\le c\}$ there is $x\in\mathcal X$ with $\boldsymbol p(x,y)\in H$ for all $y\in\mathcal Y$.
--
--   The halfspace condition is Blackwell's original criterion; the "halfspace oracle" it provides is the building block of the reduction from approachability to online linear optimization.
--
--   **Formalization Note** $a=0$ is allowed, in which case $H$ is empty or all of $\mathbb R^d$.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Proposition 1 item 2, p.45

import Mathlib
import Definitions.Def_OfflineToOnline_IsSatisfiable

namespace OfflineToOnline

/-- Halfspace-satisfiability (Proposition 1, item 2, p.45): `S` is halfspace-satisfiable in
`(X, Y, p)` if every halfspace `H ⊇ S` is satisfiable.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Proposition 1 item 2, p.45.

Formalization Note: a halfspace is `{u : ∑_j a_j u_j ≤ c}` for `a ∈ ℝ^d`, `c ∈ ℝ`; `a = 0` is
allowed (then the set is `∅` or all of `ℝ^d`). -/
def IsHalfspaceSatisfiable {m k d : ℕ} (X : Set (Fin m → ℝ)) (Y : Set (Fin k → ℝ))
    (p : (Fin m → ℝ) → (Fin k → ℝ) → (Fin d → ℝ)) (S : Set (Fin d → ℝ)) : Prop :=
  ∀ (a : Fin d → ℝ) (c : ℝ), S ⊆ {u | ∑ j, a j * u j ≤ c} →
    IsSatisfiable X Y p {u | ∑ j, a j * u j ≤ c}

end OfflineToOnline


