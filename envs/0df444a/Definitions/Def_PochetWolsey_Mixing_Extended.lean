-- Prove2me | Definitions.Def_PochetWolsey_Mixing_Extended
-- name    : PochetWolsey_Mixing_Extended
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:11.403497+00:00
-- url     : https://prove2.me/theorems/612be6c3-abe5-49f0-a0d7-5db299646a73
-- title:
--   Projection of the simplex-and-ray formulation
-- statement:
--   For $b\in\mathbb R^K$, put $f_0=0$ and $f_j=b_j-\lfloor b_j\rfloor$. Define $E(b)$ to be the set of real pairs $(s,y)$ for which there exist nonnegative real weights $\delta_0,\ldots,\delta_K$ and a nonnegative real number $\mu$ satisfying
--   $$
--   \sum_{j=0}^K\delta_j=1,\qquad
--   s=\sum_{j=0}^K f_j\delta_j+\mu,\qquad
--   y_k\ge\sum_{j=0}^K\lceil b_k-f_j\rceil\delta_j-\mu\quad(1\le k\le K).
--   $$
--   This is existential projection of an explicitly given linear system. Its equality to the convex hull of the original mixing set is the mission goal; no convex-hull claim is built into this definition.
--
--   **Formalization Note** All projected coordinates are real. Zero simplex weights and $\mu=0$ are allowed. `Option (Fin K)` represents the $K+1$ weights, including the distinguished zero level. The definition also makes sense for $K=0$, when it describes the nonnegative half-line.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 245–246 (PDF 259–260), Theorem 8.6

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model

namespace PochetWolsey.Mixing

noncomputable def extendedProjection {K : ℕ} (b : Fin K → ℝ) : Set (Point K) :=
  {p | ∃ δ : Option (Fin K) → ℝ, ∃ μ : ℝ,
    (∀ j, 0 ≤ δ j) ∧ 0 ≤ μ ∧ (∑ j, δ j) = 1 ∧
    p.1 = (∑ j, level b j * δ j) + μ ∧
    ∀ k, (∑ j, (⌈b k - level b j⌉ : ℝ) * δ j) - μ ≤ p.2 k}

end PochetWolsey.Mixing


