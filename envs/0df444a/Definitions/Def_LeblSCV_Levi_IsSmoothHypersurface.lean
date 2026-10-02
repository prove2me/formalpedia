-- Prove2me | Definitions.Def_LeblSCV_Levi_IsSmoothHypersurface
-- name    : LeblSCV_Levi_IsSmoothHypersurface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:39:44.337628+00:00
-- url     : https://prove2.me/theorems/fa4b9728-cc42-49c8-8a80-a9ed65fe8e5e
-- title:
--   Definition 2.2.1 — smooth real hypersurface in $\mathbb{C}^n$
-- statement:
--   A set $M \subset \mathbb{C}^n \cong \mathbb{R}^{2n}$ is a **smooth real hypersurface** if at each $p \in M$ there is a $C^\infty$ function $r : V \to \mathbb{R}$ with nonvanishing derivative on a neighbourhood $V$ of $p$ such that
--   $$M \cap V = \{ x \in V : r(x) = 0 \}.$$
--
--   **Formalization Note.** $V$ is taken open; `r` is an ambient real function smooth on `V` (`ContDiffOn ℝ ∞`) with `fderiv ℝ r x ≠ 0` for `x ∈ V`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 54, Definition 2.2.1

import Mathlib

open scoped ContDiff

namespace LeblSCV.Levi

/-- Definition 2.2.1 (Lebl, p. 54), `k = ∞`, in `ℂⁿ ≅ ℝ^{2n}`: `M` is a smooth real hypersurface
if at every `p ∈ M` there is an open `V ∋ p` and a smooth `r : V → ℝ` with nonvanishing
derivative such that `M ∩ V = {x ∈ V : r x = 0}`. -/
def IsSmoothHypersurface {n : ℕ} (M : Set (Fin n → ℂ)) : Prop :=
  ∀ p ∈ M, ∃ (V : Set (Fin n → ℂ)) (r : (Fin n → ℂ) → ℝ), IsOpen V ∧ p ∈ V ∧
    ContDiffOn ℝ ∞ r V ∧ (∀ x ∈ V, fderiv ℝ r x ≠ 0) ∧ M ∩ V = {x | x ∈ V ∧ r x = 0}

end LeblSCV.Levi


