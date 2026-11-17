-- Prove2me | Definitions.Def_SpencerEight_Supplement_pauliP
-- name    : SpencerEight_Supplement_pauliP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:50:51.569204+00:00
-- url     : https://prove2.me/theorems/bc80eede-2ea5-4356-a588-51b1c7da9d9d
-- title:
--   The signed permutation $P_{u,v}$
-- statement:
--   For $u,v\in\mathbb F_2^k$, $P_{u,v}$ is the real $2^k\times2^k$ matrix with rows and columns indexed by $\mathbb F_2^k$ and entries
--   $$
--   (P_{u,v})_{y,\,y\oplus u}=(-1)^{v\cdot y}\quad(y\in\mathbb F_2^k),\qquad 0\text{ elsewhere},
--   $$
--   where $v\cdot y=\sum_iv_iy_i\in\mathbb F_2$.
--
--   **Formalization Note** $\mathbb F_2^k$ is `Fin k → ZMod 2`, and $(-1)^{v\cdot y}$ is $(-1)$ raised to the representative $0$ or $1$ of $v\cdot y$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 15.6, p.291 (PDF p.291)

import Mathlib

namespace SpencerEight.Supplement

/-- The matrix `P_{u,v}` of Theorem 15.6 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.291 (PDF p.291)): for `u, v ∈ F₂^k`,
the real matrix with rows and columns indexed by `F₂^k` whose entry at `(y, y ⊕ u)` is `(−1)^{v·y}`
and whose other entries are `0`; `v·y = ∑ᵢ vᵢ yᵢ ∈ F₂` is the dot product.

**Formalization Note** `F₂^k` is `Fin k → ZMod 2` (so `2^k` rows and columns, indexed by the vectors
themselves, as in the source); `y ⊕ u` is `y + u`; `(−1)^{v·y}` is `(−1)^{(v·y).val}` with
`(v·y).val ∈ {0, 1}`. -/
def pauliP {k : ℕ} (u v : Fin k → ZMod 2) : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  fun y z => if z = y + u then (-1 : ℝ) ^ (∑ i, v i * y i).val else 0

end SpencerEight.Supplement


