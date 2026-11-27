-- Prove2me | Definitions.Def_MinVolEllipsoid_Supplement_quadSet
-- name    : MinVolEllipsoid_Supplement_quadSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:32:10.723817+00:00
-- url     : https://prove2.me/theorems/d54f61b2-cfe5-48b4-9d0d-c0eff1b11f75
-- title:
--   The set (16) cut out by affine and ellipsoidal constraints
-- statement:
--   Let $S\in\mathbb R^{J\times K}$, $t\in\mathbb R^J$, and for each $i\in[I]$ let $Q_i\in\mathbb R^{K\times K}$ and $q_i\in\mathbb R^K$. The set of display (16) is
--
--   $$
--   \mathcal P=\bigl\{x\in\mathbb R^K:\ Sx\le t,\ \|Q_ix+q_i\|^2\le1\ \ \forall i\in[I]\bigr\}.
--   $$
--
--   It extends the polytope (10) by finitely many ellipsoidal constraints, and is the domain of Theorem 4.
--
--   **Formalization Note** $[I]$ is `Fin p` (possibly empty) and $[J]$ is `Fin m`; $\|v\|^2$ is $v^\top v$. The paper's requirement $Q_i\in\mathbb S^K$ is not built in; Theorem 4 states it.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, §3.1, display (16), p.15

import Mathlib

open Matrix

namespace MinVolEllipsoid.Supplement

/-- **The set (16) with affine and quadratic constraints** (Mittal & Hanasusanto,
arXiv:1807.07507v4, §3.1, display (16), p.15).

For `S ∈ ℝ^{J×K}`, `t ∈ ℝᴶ`, and `Q_i ∈ 𝕊ᴷ`, `q_i ∈ ℝᴷ` for `i ∈ [I]`,

`𝒫 = {x ∈ ℝᴷ : Sx ≤ t, ‖Q_i x + q_i‖² ≤ 1 ∀ i ∈ [I]}`.

**Formalization Note** `I` is `Fin p` (possibly empty) and `J` is `Fin m`. `‖v‖²` is `v ⬝ᵥ v`.
The symmetry `Q_i ∈ 𝕊ᴷ` is not bundled here; Theorem 4 states it. -/
def quadSet {n m p : ℕ} (S : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (Q : Fin p → Matrix (Fin n) (Fin n) ℝ) (q : Fin p → Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | S *ᵥ x ≤ t ∧ ∀ i, (Q i *ᵥ x + q i) ⬝ᵥ (Q i *ᵥ x + q i) ≤ 1}

end MinVolEllipsoid.Supplement


