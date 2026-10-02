-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_unitSphere
-- name    : LeblSCV_BallPolydisc_unitSphere
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:16:18.460905+00:00
-- url     : https://prove2.me/theorems/22dfefdf-4a8a-4c4d-b713-140ec2a17167
-- title:
--   Unit sphere $S^{2n-1} = \partial\mathbb{B}_n$ (Euclidean norm)
-- statement:
--   The **unit sphere** in $\mathbb{C}^n$ is the boundary of the unit ball,
--   $$S^{2n-1} = \partial \mathbb{B}_n = \{ z \in \mathbb{C}^n : |z_1|^2 + |z_2|^2 + \cdots + |z_n|^2 = 1 \}.$$
--   It is a real hypersurface of real dimension $2n-1$.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; the Euclidean condition $\sum_k |z_k|^2 = 1$ is written out explicitly (the Mathlib sup-norm sphere would be the boundary of the polydisc).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 34, Proposition 1.4.6 (notation S^{2n−1} = ∂𝔹_n)

import Mathlib

namespace LeblSCV.BallPolydisc

/-- The unit sphere `S^{2n-1} = ∂𝔹_n = {z ∈ ℂⁿ : ‖z‖ = 1}` of Lebl, p. 34, for the **Euclidean**
norm `‖z‖² = |z_1|² + ⋯ + |z_n|²`. -/
def unitSphere (n : ℕ) : Set (Fin n → ℂ) :=
  {z | ∑ k : Fin n, ‖z k‖ ^ 2 = 1}

end LeblSCV.BallPolydisc


