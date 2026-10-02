-- Prove2me | Definitions.Def_HunterPDE_Compactness_HalfSpace
-- name    : HunterPDE_Compactness_HalfSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:47:39.911217+00:00
-- url     : https://prove2.me/theorems/75fc5efe-a7cf-4c0b-a0f6-b33cc1acfb8c
-- title:
--   The half-space ℝⁿ₊, its closure, the boundary ∂ℝⁿ₊ = ℝⁿ⁻¹ and C_c^∞(ℝ̄ⁿ₊) (§3.9)
-- statement:
--   Write $x = (x', x_n) \in \mathbb{R}^n$ with $x' \in \mathbb{R}^{n-1}$. The **upper half-space** is $\mathbb{R}^n_+ = \{x : x_n > 0\}$, its closure is $\overline{\mathbb{R}}^n_+ = \{x : x_n \ge 0\}$, and its boundary $\partial\mathbb{R}^n_+ = \{(x', 0)\}$ is identified with $\mathbb{R}^{n-1}$.
--
--   The space $C_c^\infty(\overline{\mathbb{R}}^n_+)$ consists of the functions that are smooth up to the boundary and vanish on $\overline{\mathbb{R}}^n_+$ outside a compact set. Such functions need not vanish on $\partial\mathbb{R}^n_+$, unlike those in $C_c^\infty(\mathbb{R}^n_+)$, whose support lies in the open half-space.
--
--   **Formalization Note.** The dimension is written $n = m + 1$ (so $n \ge 1$), and the book's last coordinate $x_n$ is `Fin.last m`. The boundary point $(x', 0)$ is `boundaryPoint x'` for $x' \in \mathbb{R}^m$. "Smooth up to the boundary" is `ContDiffOn ℝ ∞` on the closed half-space. $C_c^\infty(\mathbb{R}^n_+)$ is `IsTestFunction (upperHalfSpace m)`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 71–72, §3.9

import Mathlib

open scoped ContDiff

namespace HunterPDE.Compactness

/-- The open upper half-space `ℝⁿ₊ = {x = (x′, xₙ) : xₙ > 0}` of Hunter §3.9, written in
dimension `m + 1` (the book's `n` is `m + 1`, so `n ≥ 1`); the book's last coordinate `xₙ` is
the coordinate `Fin.last m`. -/
def upperHalfSpace (m : ℕ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | 0 < x (Fin.last m)}

/-- The closed upper half-space `ℝ̄ⁿ₊ = {x : xₙ ≥ 0}`. -/
def closedUpperHalfSpace (m : ℕ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | 0 ≤ x (Fin.last m)}

/-- The point `(x′, 0) ∈ ∂ℝⁿ₊` for `x′ ∈ ℝⁿ⁻¹ = ℝᵐ`: the boundary `∂ℝⁿ₊` is identified with
`ℝⁿ⁻¹` as in the book ("`(x′, 0) ∈ ∂ℝⁿ₊ = ℝⁿ⁻¹`"). -/
noncomputable def boundaryPoint {m : ℕ} (x' : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x' i) 0)

/-- `φ ∈ C_c^∞(ℝ̄ⁿ₊)`: `φ` is infinitely differentiable on the *closed* half-space (smooth up to
the boundary, `ContDiffOn ℝ ∞`) and vanishes on `ℝ̄ⁿ₊` outside a compact set. Such functions need
not vanish on `∂ℝⁿ₊`; only their values on `ℝ̄ⁿ₊` matter. -/
def IsSmoothCompactClosedHalfSpace {m : ℕ} (φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) : Prop :=
  ContDiffOn ℝ ∞ φ (closedUpperHalfSpace m) ∧
    ∃ K : Set (EuclideanSpace ℝ (Fin (m + 1))), IsCompact K ∧
      ∀ x ∈ closedUpperHalfSpace m, x ∉ K → φ x = 0

end HunterPDE.Compactness


