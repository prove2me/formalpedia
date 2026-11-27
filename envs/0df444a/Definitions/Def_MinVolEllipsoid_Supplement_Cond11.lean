-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_Cond11
-- name    : MinVolEllipsoid_Supplement_Cond11
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:30:51.66888+00:00
-- url     : https://prove2.me/theorems/488370c7-ba1c-4886-9692-2d1e755e1897
-- title:
--   The semidefinite certificate (11)
-- statement:
--   Let $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$, $A\in\mathbb R^{K\times K}$, $b\in\mathbb R^K$. A tuple $(N,F,g,h)$ with $N\in\mathbb R^{J\times J}$, $F\in\mathbb R^{K\times K}$, $g\in\mathbb R^K$, $h\in\mathbb R$ **satisfies (11)** if $N\in\mathbb R^{J\times J}_+$ (all entries nonnegative), $F\in\mathbb S^K$, and
--
--   $$
--   \begin{bmatrix}F & g\\ g^\top & h-1\end{bmatrix}\preceq-\begin{bmatrix}-S^\top\\ t^\top\end{bmatrix}N\begin{bmatrix}-S & t\end{bmatrix},
--   \qquad
--   \begin{bmatrix}F & g & A\\ g^\top & h & b^\top\\ A & b & \mathbb I\end{bmatrix}\succeq0 .
--   $$
--
--   Here $P\preceq Q$ means $Q-P\in\mathbb S_+$, the order of p.5. These are the constraints of Theorem 2 and of the SDP (12).
--
--   **Formalization Note** `PosSemidef` in Mathlib includes symmetry, as the p.5 order is defined on symmetric matrices; $N$ itself is not required to be symmetric. The two block matrices are the published `MinVolEllipsoid.borderedMatrix F g g (h - 1)` and `MinVolEllipsoid.ineq3Right A b F g h`.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 2, display (11), p.10; display (12), p.11; order ⪰, p.5

import Mathlib
import Definitions.Def_MinVolEllipsoid_borderedMatrix
import Definitions.Def_MinVolEllipsoid_ineq3Right
import Definitions.Def_MinVolEllipsoid_Supplement_calS

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The certificate (11)** (Mittal & Hanasusanto, arXiv:1807.07507v4, Theorem 2, display (11),
p.10; the feasible set of (12), p.11).

`Cond11 S t A b N F g h` says that `N ∈ ℝ^{J×J}_+` (entrywise nonnegative), `F ∈ 𝕊ᴷ`, and

`[F g; g⊤ h − 1] ⪯ −[−S⊤; t⊤] N [−S t]`   and   `[F g A; g⊤ h b⊤; A b 𝕀] ⪰ 0`.   (11)

**Formalization Note** `P ⪯ Q` is the paper's order of p.5 (`Q − P ∈ 𝕊₊`), written
`(Q - P).PosSemidef`; Mathlib's `PosSemidef` includes symmetry, so for a non-symmetric `N` the first
inequality also requires `−𝒮⊤N𝒮` to be symmetric, as the p.5 order is only defined on `𝕊ᴷ⁺¹`.
`N` itself is not required symmetric. `[F g; g⊤ h − 1]` is the published
`MinVolEllipsoid.borderedMatrix F g g (h - 1)`, the second matrix the published
`MinVolEllipsoid.ineq3Right A b F g h`, and `[−S t]` is `calS S t`. No condition on `A`, `b`,
`g`, `h` is bundled. -/
def Cond11 {n m : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (N : Matrix (Fin m) (Fin m) ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (h : ℝ) : Prop :=
  (∀ i j, 0 ≤ N i j) ∧ F.IsSymm ∧
    (-((calS S t)ᵀ * N * calS S t) - MinVolEllipsoid.borderedMatrix F g g (h - 1)).PosSemidef ∧
    (MinVolEllipsoid.ineq3Right A b F g h).PosSemidef

end MinVolEllipsoid.Supplement


