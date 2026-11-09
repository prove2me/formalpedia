-- Prove2me | Definitions.Def_CEPolytopeHard_nnorm
-- name    : CEPolytopeHard_nnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:24.960005+00:00
-- url     : https://prove2.me/theorems/23284d5c-edc5-4f8c-90cc-58e4f31a7560
-- title:
--   Normalized Euclidean norm $\|x\|_2 = (\tfrac1d\sum_i x_i^2)^{1/2}$
-- statement:
--   For $x \in \mathbb R^d$ the **normalized Euclidean norm** is
--   $$
--   \|x\|_2 = \Big(\frac1d \sum_{i=1}^d x_i^2\Big)^{1/2}.
--   $$
--   Sections 3 and 4 of the paper use this convention throughout (following Rubinstein), so that $\|x\|_2 \le 1$ for $x \in [0,1]^d$. Inner products are not normalized, and $|\langle x, y\rangle|/d \le \|x\|_2\|y\|_2$.
--
--   **Formalization Note** Coordinates are indexed by a finite type with $d$ elements (a lifted vector of $\mathbb R^{dr}$ uses the index type of pairs (layer, coordinate)). For $d = 0$ the value is $0$.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Notation, p.9

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **normalized Euclidean norm** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Notation, p.9: "In the technical overview and Sections
3 and 4, following Rubinstein [72], for x ∈ R^d and 1 ≤ p < ∞ we adopt the normalized norm
convention ∥x∥_p = ((1/d) ∑_{i=1}^d |x_i|^p)^{1/p}"), for `p = 2`:
`‖v‖₂ = ((1/D) ∑_i v_i²)^{1/2}`, `D` the number of coordinates.

**Formalization Note** Coordinates are indexed by a finite type `ι`, `D = card ι` (for a lifted
vector in `ℝ^{dr}` the index type is `Fin r × Fin d`). For `D = 0` the value is `0`. -/
noncomputable def nnorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt ((1 / (Fintype.card ι : ℝ)) * ∑ i, v i ^ 2)

end CEPolytopeHard


