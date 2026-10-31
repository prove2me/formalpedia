-- Prove2me | Definitions.Def_ParriloTheta_matrix65
-- name    : ParriloTheta_matrix65
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:13.245876+00:00
-- url     : https://prove2.me/theorems/b3270ebd-22f7-447a-8a3d-219fbe76806e
-- title:
--   The matrix (6.5)
-- statement:
--   Let $\alpha>k\ge2$ be integers, $b\in\mathbb R$, and let $W$ be a set of $\alpha-k$ elements. The matrix (6.5) is indexed by $W\cup\{v\}$:
--   $$
--   \begin{pmatrix} M_b & \big(\tfrac{\alpha}{2}-\tfrac{\alpha}{2k}-1\big)\mathbf 1\\[2pt] \big(\tfrac{\alpha}{2}-\tfrac{\alpha}{2k}-1\big)\mathbf 1^{T} & \alpha-1\end{pmatrix},
--   $$
--   where $M_b$ is the $W\times W$ matrix with $a$ on the diagonal and $c$ off the diagonal, with $a,c$ from (6.6). In the paper it is the principal submatrix $P(v)[W\cup\{v\}]$ of a symmetric $\mathcal K^{(1)}$-certificate of $M_G$ for $G=H\oplus\overline{K_{\alpha-k}}$.
--
--   **Formalization Note** $W$ is `Fin (α - k)` and $\{v\}$ is `Unit`. The page's "$M_b$ is indexed by $V$" is a misprint for $W$.
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, eqs. (6.5)–(6.6), p.21 (Lemma 6.10)

import Mathlib
import Definitions.Def_ParriloTheta_coeffA
import Definitions.Def_ParriloTheta_coeffC

namespace ParriloTheta

/-- **The matrix (6.5).**
Laurent & Vargas, arXiv:2109.12876v1, eqs. (6.5)–(6.6), p.21:
"P(v)[W ∪ {v}] = ( M_b , α/2 − α/(2k) − 1 ; α/2 − α/(2k) − 1 , α − 1 ), where the blocks are
indexed by W and {v}, respectively", with `M_b` the `|W| × |W|` matrix with `a` on the diagonal
and `c` off the diagonal (6.6), and `|W| = α − k`.

`matrix65 α k b` is this `(α − k + 1) × (α − k + 1)` matrix: on the `W`-block it is `a` on the
diagonal and `c` off it, the border entries are `α/2 − α/(2k) − 1`, and the corner is `α − 1`.

**Formalization Note.** `W` is `Fin (α − k)` and `{v}` is `Unit`; `a = coeffA α k b`,
`c = coeffC k b`. The page's "Mb is indexed by V" is read as `W` (the block is indexed by `W`).
All arithmetic is in `ℝ`. -/
noncomputable def matrix65 (α k : ℕ) (b : ℝ) :
    Matrix (Fin (α - k) ⊕ Unit) (Fin (α - k) ⊕ Unit) ℝ :=
  Matrix.fromBlocks
    (Matrix.of fun i j => if i = j then coeffA α k b else coeffC k b)
    (Matrix.of fun _ _ => (α : ℝ) / 2 - (α : ℝ) / (2 * (k : ℝ)) - 1)
    (Matrix.of fun _ _ => (α : ℝ) / 2 - (α : ℝ) / (2 * (k : ℝ)) - 1)
    (Matrix.of fun _ _ => (α : ℝ) - 1)

end ParriloTheta


