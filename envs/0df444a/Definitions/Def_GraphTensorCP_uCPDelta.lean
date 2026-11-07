-- Prove2me | Definitions.Def_GraphTensorCP_uCPDelta
-- name    : GraphTensorCP_uCPDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:19.205034+00:00
-- url     : https://prove2.me/theorems/52196720-99b8-4208-b055-583d22e9729c
-- title:
--   Path-strengthened copositive bound $U^\Delta_{\mathrm{CP}}(W)$
-- statement:
--   Let $W$ be a symmetric nonnegative zero-diagonal real $n\times n$ matrix and let $J=\mathbf 1\mathbf 1^{\mathsf T}$ be the all-one matrix. Recall that a symmetric matrix $X$ is **copositive**, $X\in\mathrm{COP}_n$, if $a^{\mathsf T}Xa\ge0$ for every $a\in\mathbb R^n_{\ge0}$. The **path-strengthened completely positive bound** is
--
--   $$U^\Delta_{\mathrm{CP}}(W)=\max\Big\{\sum_{1\le i<j\le n}W_{i,j}P_{i,j}\ :\ P=P^{\mathsf T},\ P_{i,i}=0,\ P_{i,j}\ge0,\ J-2P\in\mathrm{COP}_n,\ P_{i,j}\le P_{i,k}+P_{k,j}\ (i,j,k\text{ distinct})\Big\},$$
--
--   where all indices in the constraints range over $1,\dots,n$; the variables $P_{i,j}$ exist for every pair, edges and non-edges alike.
--
--   Without the path inequalities, this is the dual of the completely positive covering program $U_{\mathrm{CP}}$. The mission's goal states that $U^\Delta_{\mathrm{CP}}(W)$ bounds the logarithmic asymptotic rank of $\mathsf{WT}(Q)$ from above.
--
--   **Formalization Note** Copositivity is the published `MurtyKabadi.Reduction.Copositive` ($x^{\mathsf T}Mx\ge0$ for all $x\ge0$); it is not positive semidefiniteness. $U^\Delta_{\mathrm{CP}}$ is the real supremum of the feasible objective values: the set is nonempty ($P=0$) and bounded, because copositivity at $e_i+e_j$ forces $P_{i,j}\le1$, and the paper notes that the maximum is attained.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 5.5, eq. (14), p.48; Definition 2.32, p.28 (COP_n); §5 preamble, p.45 (J)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

namespace GraphTensorCP

/-- Feasibility for the **path-strengthened copositive program** (14) (Zhou, *Asymptotic Rank of
Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of
2026-11-03), Definition 5.5, p.48): "P = Pᵀ, P_{i,i} = 0, P_{i,j} ≥ 0, J − 2P ∈ COP_n,
P_{i,j} ≤ P_{i,k} + P_{k,j} (i, j, k distinct). All indices in the constraints range from 1 to n."

**Formalization Note.** `J` is the all-one matrix, diagonal included (§5 preamble, p.45).
Copositivity is `MurtyKabadi.Reduction.Copositive`: `xᵀ(J − 2P)x ≥ 0` for every `x ≥ 0`
(Definition 2.32, p.28; `J − 2P` is symmetric because `P` is). It is **not** positive
semidefiniteness. The path inequalities range over all distinct triples, edges or not. -/
def IsPathCPFeasible {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.IsSymm ∧ (∀ i, P i i = 0) ∧ (∀ i j, 0 ≤ P i j) ∧
    MurtyKabadi.Reduction.Copositive (Matrix.of (fun _ _ => (1 : ℝ)) - (2 : ℝ) • P) ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → P i j ≤ P i k + P k j

/-- **Path-strengthened completely positive bound** `U^Δ_CP(W)` (Zhou, arXiv:2610.34273
(version of 2026-11-03), Definition 5.5, eq. (14), p.48):
"U^Δ_CP(W) = max_{P feasible} ( Σ_{1≤i<j≤n} W_{i,j}P_{i,j} )".

**Formalization Note.** A real `sSup` over the values of feasible `P`. The value set is
nonempty (`P = 0` is feasible) and bounded above by `Σ_{i<j} |W_{i,j}|`, since copositivity at
`e_i + e_j` forces `P_{i,j} ≤ 1` (proof of Proposition 5.3, p.47); the paper notes that the
maximum is attained (p.48), so the supremum is the paper's maximum. The objective sums over
unordered pairs `i < j`. -/
noncomputable def uCPDelta {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {v : ℝ | ∃ P : Matrix (Fin n) (Fin n) ℝ, IsPathCPFeasible P ∧
    v = ∑ i, ∑ j, if i < j then W i j * P i j else 0}

end GraphTensorCP


