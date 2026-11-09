-- Prove2me | Definitions.Def_ListReplicableBias_LowerBound_Geometry
-- name    : ListReplicableBias_LowerBound_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:12.910128+00:00
-- url     : https://prove2.me/theorems/814a1170-4650-4c96-8020-0a13f0adc8e8
-- title:
--   Cubes, open sup-norm balls and Sperner/KKM colorings
-- statement:
--   For dimension $d\in\mathbb N$ and real endpoints $a,b$, write $[a,b]^d$ for the vectors whose coordinates lie between $a$ and $b$. For a vector $p$ and radius $r$, set
--   $$B^\circ_\infty(r,p)=\{q:\|p-q\|_\infty<r\},\qquad R=[1/2-2\varepsilon,1/2+2\varepsilon]^d.$$
--   For $a<b$, a map $\chi:[a,b]^d\to C$ is a Sperner/KKM coloring if any two points on opposite faces in any coordinate have different colors. The color set is arbitrary, and neither measurability nor finiteness is required.
--
--   These objects describe the geometry used by the lower bound. Lean represents vectors by functions on `Fin d`, with the sup norm; a coloring is an ambient map whose values outside the cube are ignored. The definitions also have literal total-function values outside their intended parameter domains: the cube is empty for $a>b$ in positive dimension, the open ball is empty for $r\le0$, and the face rule is used only when $a<b$.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, §3.1, PDF p. 2; Definition 5.1, PDF p. 4; §5.4, PDF p. 6

import Mathlib

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- Coordinate cube, §3.1 and Definition 5.1, PDF pp. 2, 4. -/
def cube (d : ℕ) (a b : ℝ) : Set (Fin d → ℝ) :=
  {p | ∀ i, a ≤ p i ∧ p i ≤ b}

/-- Open ball for the sup norm, §3.1, PDF p. 2. -/
def openBall {d : ℕ} (p : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {q | ‖p - q‖ < r}

/-- The central cube used in §5.4 and Appendix B, PDF pp. 6, 15. -/
def region (d : ℕ) (ε : ℝ) : Set (Fin d → ℝ) :=
  cube d (1 / 2 - 2 * ε) (1 / 2 + 2 * ε)

/-- Definition 5.1, PDF p. 4. No regularity or finiteness of colors is assumed.
Values of the ambient map outside the cube are ignored. -/
def IsSpernerKKMColoring {d : ℕ} {C : Type*} (a b : ℝ)
    (χ : (Fin d → ℝ) → C) : Prop :=
  ∀ x ∈ cube d a b, ∀ y ∈ cube d a b, ∀ i : Fin d,
    x i = a → y i = b → χ x ≠ χ y

end ListReplicableBias.LowerBound


