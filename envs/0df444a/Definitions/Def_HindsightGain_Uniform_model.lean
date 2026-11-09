-- Prove2me | Definitions.Def_HindsightGain_Uniform_model
-- name    : HindsightGain_Uniform_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:40.606599+00:00
-- url     : https://prove2.me/theorems/e3e549ff-8c17-4793-8bbe-3c8a0798fc2f
-- title:
--   Compact local domains and multilinear interaction coefficients
-- statement:
--   Fix integers $n,D\ge1$ and $r\ge2$. Each variable $i\in[n]$ has a nonempty compact local domain $K_i\subseteq\mathbb R^D$ contained in the closed Euclidean unit ball. No convexity or containment of the origin is required. Each unordered $r$-element set $e=\{i_1<\cdots<i_r\}$ carries arbitrary real coefficients $(A_e)_a$, with $a\in[D]^r$, defining
--   $$A_e(x_e)=\sum_{a\in[D]^r}(A_e)_a\prod_{j=1}^r x_{i_j,a_j}.$$
--   The model stores precisely these data and their standing assumptions. Coefficients need not be symmetric, nonnegative or bounded, and $n<r$ is allowed. This interface is shared by all source-specific optimization statements.
--   **Formalization Note** Indices use `Fin`, and local vectors have the Euclidean norm. Edges are cardinality-$r$ finite subsets; the coefficients uniquely specify every multilinear map in orthonormal coordinates.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, §1.1, pp.3–4; §2, p.12

import Mathlib

set_option autoImplicit false

namespace HindsightGain.Uniform

abbrev Vec (D : ℕ) := EuclideanSpace ℝ (Fin D)
abbrev Edge (n r : ℕ) := {e : Finset (Fin n) // e.card = r}

/-- The data and precisely the standing assumptions of §§1.1 and 2, pp.3,12. -/
structure Model (n D r : ℕ) where
  hn : 1 ≤ n
  hD : 1 ≤ D
  hr : 2 ≤ r
  K : Fin n → Set (Vec D)
  nonempty : ∀ i, (K i).Nonempty
  compact : ∀ i, IsCompact (K i)
  unitBall : ∀ i, K i ⊆ Metric.closedBall 0 1
  A : Edge n r → (Fin r → Fin D) → ℝ

end HindsightGain.Uniform


