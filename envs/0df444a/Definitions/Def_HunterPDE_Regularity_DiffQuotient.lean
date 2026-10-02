-- Prove2me | Definitions.Def_HunterPDE_Regularity_DiffQuotient
-- name    : HunterPDE_Regularity_DiffQuotient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:15:42.715392+00:00
-- url     : https://prove2.me/theorems/eabbad54-4125-4493-88cc-bb96a35fef1a
-- title:
--   Difference quotients D_i^h u (Definition 4.51) and compact containment Ω′ ⋐ Ω
-- statement:
--   Let $u : \mathbb{R}^n \to \mathbb{R}$ and $h \in \mathbb{R} \setminus \{0\}$. The $i$th **difference quotient** of $u$ of size $h$ is the function
--   $$D_i^h u(x) = \frac{u(x + h e_i) - u(x)}{h},$$
--   where $e_i$ is the unit vector in the $i$th direction. The vector of difference quotients is $D^h u = (D_1^h u, \dots, D_n^h u)$, with pointwise Euclidean length $|D^h u|(x) = \big(\sum_i (D_i^h u(x))^2\big)^{1/2}$.
--
--   A nonempty open set $\Omega'$ is **compactly contained** in an open set $\Omega$, written $\Omega' \Subset \Omega$, if its closure $\overline{\Omega'}$ is compact and $\overline{\Omega'} \subset \Omega$.
--
--   Difference quotients replace derivatives in the proof of interior regularity: uniform bounds on them in $h$ give weak derivatives.
--
--   **Formalization Note.** Coordinates are 0-based (`i : Fin n`), so the book's index $i \in \{1,\dots,n\}$ is Lean's `i - 1`. $e_i$ is `EuclideanSpace.single i 1`. At $h = 0$ Lean's division returns the junk value $0$; every statement assumes $h \ne 0$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 124, Definition 4.51; p. 1 (Ω′ ⋐ Ω)

import Mathlib

namespace HunterPDE.Regularity

/-- Definition 4.51 of Hunter, *Notes on PDEs*: the `i`th difference quotient of `u : ℝⁿ → ℝ` of
size `h`, `D_i^h u(x) = (u(x + h eᵢ) − u(x)) / h`, where `eᵢ = EuclideanSpace.single i 1` is the
unit vector in the `i`th direction. Coordinates are 0-based (`i : Fin n` is the book's `i + 1`).
The book takes `h ∈ ℝ ∖ {0}`; at `h = 0` Lean's division gives the junk value `0`, and every
statement using `diffQuot` assumes `h ≠ 0`. -/
noncomputable def diffQuot {n : ℕ} (i : Fin n) (h : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (u (x + h • EuclideanSpace.single i (1 : ℝ)) - u x) / h

/-- The pointwise Euclidean length `|D^h u(x)| = (∑ᵢ (D_i^h u(x))²)^{1/2}` of the vector of
difference quotients `D^h u = (D_1^h u, …, D_n^h u)` of Definition 4.51; `‖D^h u‖_{Lᵖ}` is the
`Lᵖ` norm of this function. -/
noncomputable def diffQuotNorm {n : ℕ} (h : ℝ) (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ i : Fin n, (diffQuot i h u x) ^ 2)

/-- `Ω′ ⋐ Ω` (Hunter, p. 1): a nonempty open set `Ω′` is compactly contained in `Ω` if its closure
`Ω̄′` is compact and `Ω̄′ ⊂ Ω`. -/
def CompactlyContained {n : ℕ} (Ω' Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Ω'.Nonempty ∧ IsOpen Ω' ∧ IsCompact (closure Ω') ∧ closure Ω' ⊆ Ω

end HunterPDE.Regularity


