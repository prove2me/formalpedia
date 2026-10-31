-- Prove2me | Definitions.Def_MinVolEllipsoid_lift
-- name    : MinVolEllipsoid_lift
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:40.854975+00:00
-- url     : https://prove2.me/theorems/604ca505-ec95-4c6a-bf13-a34af7df27f0
-- title:
--   The lift $x \mapsto [x;1]$
-- statement:
--   For $x\in\mathbb R^K$, the **lift** $[x;1]\in\mathbb R^{K+1}$ is the vector obtained by appending the coordinate $1$ below $x$ (vertical concatenation $[u;v]$, notation of p.5).
--
--   The lift embeds $\mathbb R^K$ as the affine hyperplane $\{\tau=1\}$ of $\mathbb R^{K+1}$; the cone $\mathcal K$ of display (2) is the conic hull of the lifted set $\{[x;1]:x\in\mathcal P\}$.
--
--   **Formalization Note** The dimension is written $n$ (the paper's $K$ clashes with the cone $\mathcal K$). $\mathbb R^{K+1}$ is the function type `Fin n ⊕ Unit → ℝ`, the paper's last coordinate being the `Unit` coordinate. The lift is `Sum.elim x (fun _ => 1)`.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 1, display (2), p.6; notation [u; v], p.5

import Mathlib

namespace MinVolEllipsoid

/-- **The lift `x ↦ [x; 1]`** (Mittal & Hanasusanto, *Finding Minimum Volume Circumscribing
Ellipsoids Using Generalized Copositive Programming*, arXiv:1807.07507v4, Theorem 1, display (2),
p.6; vertical concatenation `[u; v]`, notation, p.5).

`lift x` is the vector of `ℝᴷ⁺¹` obtained by appending the coordinate `1` below `x ∈ ℝᴷ`.

**Formalization Note** The dimension is written `n` (the paper's `K` clashes with the cone `𝒦`).
`ℝᴷ⁺¹` is `Fin n ⊕ Unit → ℝ`; the paper's last coordinate is the `Unit` coordinate, and the
concatenation `[x; τ]` is `Sum.elim x (fun _ => τ)`. -/
def lift {n : ℕ} (x : Fin n → ℝ) : Fin n ⊕ Unit → ℝ :=
  Sum.elim x (fun _ => (1 : ℝ))

end MinVolEllipsoid


