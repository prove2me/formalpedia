-- Prove2me | Definitions.Def_DRSub4633_Supplement_width
-- name    : DRSub4633_Supplement_width
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:30:43.1413+00:00
-- url     : https://prove2.me/theorems/afb3fd23-c38c-48e0-b600-b85e1e4c12c2
-- title:
--   Coordinate width $w_i=\max_{x\in K}x_i$
-- statement:
--   For $K\subseteq\mathbb R^n$ and a coordinate $i$, the width of $K$ in coordinate $i$ is
--   $$w_i=\max_{x\in K}x_i .$$
--
--   **Formalization Note** It is written as the supremum of $\{x_i : x\in K\}$. For a nonempty compact $K$, as in Theorem 6.3, the supremum is attained.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 6.2, p.35

import Mathlib

namespace DRSub4633.Supplement

/-- **Coordinate width `wᵢ = max_{x ∈ K} xᵢ`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 6.2, p.35: "Width normalization
computes the width `wᵢ = max_{x∈K} xᵢ` of each coordinate".

**Formalization Note.** Written as `sSup` of the image of `K` under the `i`-th coordinate. For
the nonempty compact `K` of Theorem 6.3 the supremum is attained, so it is the paper's
maximum. -/
noncomputable def width {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin n) => x i) '' K)

end DRSub4633.Supplement


