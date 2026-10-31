-- Prove2me | Definitions.Def_MinVolEllipsoid_Zval
-- name    : MinVolEllipsoid_Zval
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:41.425846+00:00
-- url     : https://prove2.me/theorems/bae9ad9d-35ec-45b8-91df-22500f68e1f0
-- title:
--   The value $Z(A,b)=\sup_{x\in\mathcal P}\|Ax+b\|^2$, display (1)
-- statement:
--   For a set $\mathcal P\subseteq\mathbb R^K$, a matrix $A\in\mathbb R^{K\times K}$ and $b\in\mathbb R^K$,
--
--   $$
--   Z(A,b)=\sup_{x\in\mathcal P}\|Ax+b\|^2=\sup_{x\in\mathcal P}\{x^\top A^2x+2b^\top Ax+b^\top b\}.
--   $$
--
--   The constraint $Z(A,b)\le1$ of problem (MVE) says that every point of $\mathcal P$ lies in the ellipsoid $\mathcal E(A,b)=\{x:\|Ax+b\|^2\le1\}$.
--
--   **Formalization Note** $\|v\|^2$ is the dot product $v\cdot v$. The supremum is the real `sSup`, which returns $0$ on an empty or unbounded-above set; every statement that uses $Z$ assumes $\mathcal P$ nonempty and compact (Assumption 1), where the supremum is a genuine maximum.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, display (1), p.5

import Mathlib

open Matrix

namespace MinVolEllipsoid

/-- **The value `Z(A, b) = sup_{x∈𝒫} ‖Ax + b‖²`** (Mittal & Hanasusanto, arXiv:1807.07507v4,
display (1), p.5:
`Z(A, b) = sup_{x∈𝒫} ‖Ax + b‖² = sup_{x∈𝒫} {x⊤A²x + 2b⊤Ax + b⊤b}`).

`Zval P A b` is the supremum over `x ∈ P` of the squared Euclidean norm `‖Ax + b‖²`.

**Formalization Note** `‖v‖²` is `v ⬝ᵥ v` (the pi type carries the sup norm, not the Euclidean
one). The supremum is Mathlib's real `sSup`, which returns `0` on an empty or unbounded-above set;
every statement that uses `Zval` assumes `P` nonempty and compact (Assumption 1), so the supremum
is a genuine maximum there. -/
noncomputable def Zval {n : ℕ} (P : Set (Fin n → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) : ℝ :=
  sSup ((fun x => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) '' P)

end MinVolEllipsoid


