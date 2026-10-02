-- Prove2me | Definitions.Def_LeblSCV_CR_IsSmoothHypersurface
-- name    : LeblSCV_CR_IsSmoothHypersurface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:53:32.340102+00:00
-- url     : https://prove2.me/theorems/d6a14f40-a691-487d-b811-2d1159ed60f6
-- title:
--   Definition 2.2.1 — smooth real hypersurface and local defining function
-- statement:
--   Let $M \subset \mathbb{C}^n \cong \mathbb{R}^{2n}$ and $p \in M$. A **defining function** of $M$ at $p$ is a smooth ($C^\infty$) function $r : V \to \mathbb{R}$ on an open neighborhood $V$ of $p$ whose real derivative $dr$ vanishes nowhere on $V$ and such that
--   $$M \cap V = \{ x \in V : r(x) = 0 \}.$$
--   The set $M$ is a **smooth real hypersurface** if it has a defining function at each of its points.
--
--   **Formalization Note.** `IsLocalDefiningFunction M p V r` is the structure (open `V ∋ p`, `ContDiffOn ℝ ∞ r V`, `fderiv ℝ r x ≠ 0` on `V`, `M ∩ V = {x ∈ V : r x = 0}`); `IsSmoothHypersurface M` asks for one at every point of `M`. "Smooth" is $C^\infty$ (`∞`, not `ω`). This restates the book's Definition 2.2.1 (case $k = \infty$) locally in this mission's namespace.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 54, Definition 2.2.1 (k = ∞)

import Mathlib

open scoped ContDiff

namespace LeblSCV.CR

/-- Definition 2.2.1 (Lebl, p. 54), `k = ∞`, in `ℂⁿ ≅ ℝ^{2n}`: `r` is a (local) defining function
of `M` at `p` on the open neighbourhood `V` of `p`: `r : V → ℝ` is smooth with nonvanishing
derivative and `M ∩ V = {x ∈ V : r x = 0}`. -/
structure IsLocalDefiningFunction {n : ℕ} (M : Set (Fin n → ℂ)) (p : Fin n → ℂ)
    (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ) : Prop where
  isOpen : IsOpen V
  mem : p ∈ V
  smooth : ContDiffOn ℝ ∞ r V
  fderiv_ne_zero : ∀ x ∈ V, fderiv ℝ r x ≠ 0
  inter_eq : M ∩ V = {x | x ∈ V ∧ r x = 0}

/-- Definition 2.2.1 (Lebl, p. 54), `k = ∞`: `M ⊂ ℂⁿ ≅ ℝ^{2n}` is a smooth real hypersurface if it
has a defining function at each of its points. -/
def IsSmoothHypersurface {n : ℕ} (M : Set (Fin n → ℂ)) : Prop :=
  ∀ p ∈ M, ∃ (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ), IsLocalDefiningFunction M p V r

end LeblSCV.CR


