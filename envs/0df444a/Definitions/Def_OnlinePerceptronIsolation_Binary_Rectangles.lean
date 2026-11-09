-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Rectangles
-- name    : OnlinePerceptronIsolation_Binary_Rectangles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:28.550977+00:00
-- url     : https://prove2.me/theorems/75250b7d-447f-49ab-a8a3-e85313add32f
-- title:
--   Half-open rectangles with infinite endpoints
-- statement:
--   For endpoints $a_j,b_j\in[-\infty,+\infty]$, define
--   $$\operatorname{Rect}(a,b)=\{x\in\mathbb R^m:\forall j,\ a_j\le x_j<b_j\}.$$
--   The approximation theorem requires $a_j\le b_j$ and quantifies over every such pair. This includes empty intervals, unbounded intervals, upper orthants and the full space. Endpoints live in the extended reals only for ordering against finite coordinates; no extended-real arithmetic occurs. This supplies the full class of rectangles in the Berry-Esseen estimate.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem A.1, Eq. (A.3), printed p.18, PDF p.20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

/-- (A.3): half-open coordinate intervals with extended endpoints, including empty and
unbounded rectangles. For real x, -∞ ≤ x and x < +∞ automatically hold. -/
def rectangle {m : ℕ} (a b : Fin m → EReal) : Set (Fin m → ℝ) :=
  {x | ∀ j, a j ≤ (x j : EReal) ∧ (x j : EReal) < b j}

end OnlinePerceptronIsolation.Binary


