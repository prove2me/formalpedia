-- Prove2me | Definitions.Def_TSPSDPGap_IsSDP1Feasible
-- name    : TSPSDPGap_IsSDP1Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:09.639995+00:00
-- url     : https://prove2.me/theorems/18d8875d-c4d0-442a-8d89-019abfbc7b59
-- title:
--   Feasible set of SDP (1) (and of SDP (2) on $n+1$ vertices)
-- statement:
--   A symmetric matrix $Y\in\mathbb S^{n^2\times n^2}$, viewed as an $n\times n$ array of $n\times n$ blocks, is **feasible for SDP (1)** (the Povh–Rendl relaxation of the quadratic assignment problem specialized to the TSP) if
--   $$
--   \begin{aligned}
--   &\operatorname{trace}\bigl((I_n\otimes E^{(n)}_{jj})Y\bigr)=1,\qquad \operatorname{trace}\bigl((E^{(n)}_{jj}\otimes I_n)Y\bigr)=1 \qquad (j=1,\dots,n),\\
--   &\operatorname{trace}\bigl((I_n\otimes(J_n-I_n)+(J_n-I_n)\otimes I_n)Y\bigr)=0,\qquad \operatorname{trace}(J_{n^2}Y)=n^2,\\
--   &Y\ge0 \text{ entrywise},\qquad Y\succeq0 .
--   \end{aligned}
--   $$
--   Here $E^{(n)}_{jj}=e_je_j^{\mathsf T}$, $J_m$ is the all-ones matrix and $\otimes$ the Kronecker product. Up to dimension these are also exactly the constraints of the de Klerk–Sotirov SDP (2) on $n+1$ vertices, whose last equality reads $\operatorname{trace}((J_n\otimes J_n)Y)=n^2$, the same constraint because $J_n\otimes J_n=J_{n^2}$.
--
--   For every permutation matrix $X$, the lift $Y=\operatorname{vec}(X)\operatorname{vec}(X)^{\mathsf T}$ is feasible, which is why both SDPs relax the TSP.
--
--   **Formalization Note** $Y$ is indexed by `Fin n × Fin n`; with Mathlib's Kronecker product $(P\otimes Q)_{(a,i),(b,j)}=P_{ab}Q_{ij}$ the first coordinate is the block index. $Y\succeq0$ is `Matrix.PosSemidef`, which already includes symmetry; symmetry is also listed explicitly.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, SDP (1), p.6; SDP (2) on n+1 vertices, p.7

import Mathlib

open scoped Kronecker

namespace TSPSDPGap

/-- **The feasible set of SDP (1)** (Povh–Rendl relaxation specialized to the TSP), which is
also the feasible set of SDP (2) on `n + 1` vertices.
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, (1), p.6:
"subject to trace((I_n ⊗ E^{(n)}_{jj})Y) = 1, j = 1, ..., n;
trace((E^{(n)}_{jj} ⊗ I_n)Y) = 1, j = 1, ..., n;
trace((I_n ⊗ (J_n − I_n) + (J_n − I_n) ⊗ I_n)Y) = 0; trace(J_{n²}Y) = n²;
Y ≥ 0, Y ⪰ 0, Y ∈ S^{n²×n²}", and p.7: "up to dimension, the constraints of SDPs (1) and (2)
are exactly the same" (SDP (2) on `n + 1` vertices writes `trace((J_n ⊗ J_n)Y) = n²`, the same
constraint since `J_n ⊗ J_n = J_{n²}`).

`Y` is feasible iff it satisfies the two families of assignment constraints, the zero-pattern
constraint, total entry sum `n²`, entrywise nonnegativity, symmetry and positive
semidefiniteness.

**Formalization Note.** `Y` is an `n² × n²` real matrix indexed by `Fin n × Fin n`; with
Mathlib's Kronecker product `(P ⊗ₖ Q) (a, i) (b, j) = P a b * Q i j`, the first (outer)
coordinate is the block index of the paper's `n × n` block structure and the second (inner)
coordinate is the index inside a block. Indices are 0-based. `E^{(n)}_{jj}` is
`Matrix.single j j 1`, `J_m` is the all-ones matrix, `I_n` is `1`. `Y ⪰ 0` is
`Matrix.PosSemidef` (which already contains symmetry over `ℝ`); symmetry is also stated
separately as `Y.transpose = Y`. -/
def IsSDP1Feasible (n : ℕ) (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) : Prop :=
  (∀ j : Fin n, Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ Matrix.single j j (1 : ℝ)) * Y) = 1) ∧
  (∀ j : Fin n, Matrix.trace ((Matrix.single j j (1 : ℝ) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Y) = 1) ∧
  Matrix.trace (((1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (Matrix.of (fun _ _ => (1 : ℝ)) - 1) +
      (Matrix.of (fun _ _ => (1 : ℝ)) - 1) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)) * Y) = 0 ∧
  Matrix.trace (Matrix.of (fun _ _ => (1 : ℝ)) * Y) = (n : ℝ) ^ 2 ∧
  (∀ a b, 0 ≤ Y a b) ∧
  Y.transpose = Y ∧
  Y.PosSemidef

end TSPSDPGap


