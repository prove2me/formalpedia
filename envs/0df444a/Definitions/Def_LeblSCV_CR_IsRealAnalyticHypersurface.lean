-- Prove2me | Definitions.Def_LeblSCV_CR_IsRealAnalyticHypersurface
-- name    : LeblSCV_CR_IsRealAnalyticHypersurface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:43:33.119437+00:00
-- url     : https://prove2.me/theorems/ba863cf9-9952-4217-9806-ccf2b4e2d3a9
-- title:
--   Definition 3.1.9 — real-analytic hypersurface in $\mathbb{C}^n \cong \mathbb{R}^{2n}$
-- statement:
--   Identify $\mathbb{C}^n$ with $\mathbb{R}^{2n}$ by writing $z_k = x_k + i y_k$; the $2n$ real coordinates are $x_1, y_1, \dots, x_n, y_n$. A set $M \subset \mathbb{C}^n$ is a **real-analytic hypersurface** if locally at every point it is the graph of a real-analytic function: for every $p \in M$ one of the $2n$ real coordinates, call it $y$, can be chosen (relabeling coordinates), with the remaining $2n-1$ real coordinates collected as $x \in \mathbb{R}^{2n-1}$, together with an open neighborhood $V$ of $p$ and a real-analytic function $\varphi$ on an open set $W \subset \mathbb{R}^{2n-1}$ containing the $x$-coordinates of all points of $V$, such that
--   $$M \cap V = \{ (x, y) \in V : y = \varphi(x) \}.$$
--
--   **Formalization Note.** The real coordinates are indexed by `Fin n × Bool`: `realCoord (k, false) z = Re z_k` and `realCoord (k, true) z = Im z_k`; the graph coordinate is an index `j`, and the other coordinates form a vector in `{i // i ≠ j} → ℝ` (`otherRealCoords j z`). The book's definition is for $M \subset \mathbb{R}^n$; the mission only uses $\mathbb{R}^{2n} \cong \mathbb{C}^n$. Neighborhoods are taken open. The graphing function is real-analytic in the sense of Definition 3.1.1 (`IsRealAnalyticOn W φ`). The file also defines `realCoord` and `otherRealCoords`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 109, Definition 3.1.9

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticOn

namespace LeblSCV.CR

/-- The `2n` real coordinates of `ℂⁿ ≅ ℝ^{2n}`, `z_k = x_k + i y_k`, indexed by `Fin n × Bool`:
`(k, false) ↦ x_k = Re z_k` and `(k, true) ↦ y_k = Im z_k`. -/
def realCoord {n : ℕ} (j : Fin n × Bool) (z : Fin n → ℂ) : ℝ :=
  if j.2 then (z j.1).im else (z j.1).re

/-- The real coordinates of `z` other than the coordinate `j`. -/
def otherRealCoords {n : ℕ} (j : Fin n × Bool) (z : Fin n → ℂ) :
    {i : Fin n × Bool // i ≠ j} → ℝ :=
  fun i => realCoord i.1 z

/-- Definition 3.1.9 (Lebl, p. 109), for `M ⊂ ℂⁿ ≅ ℝ^{2n}`: `M` is a real-analytic hypersurface if
near every point `p ∈ M`, after relabeling the real coordinates (choosing which real coordinate
`j` plays the role of `y`), `M` is the graph `y = φ(x)` of a real-analytic function `φ` of the
remaining real coordinates `x`: there is an open `V ∋ p` and a real-analytic
`φ : W → ℝ` on an open set `W` of the remaining coordinates containing the `x`-coordinates of `V` with
`M ∩ V = {z ∈ V : y(z) = φ(x(z))}`. -/
def IsRealAnalyticHypersurface {n : ℕ} (M : Set (Fin n → ℂ)) : Prop :=
  ∀ p ∈ M, ∃ (j : Fin n × Bool) (V : Set (Fin n → ℂ))
    (W : Set ({i : Fin n × Bool // i ≠ j} → ℝ)) (φ : ({i : Fin n × Bool // i ≠ j} → ℝ) → ℝ),
    IsOpen V ∧ p ∈ V ∧ IsRealAnalyticOn W φ ∧ (∀ z ∈ V, otherRealCoords j z ∈ W) ∧
    M ∩ V = {z | z ∈ V ∧ realCoord j z = φ (otherRealCoords j z)}

end LeblSCV.CR


