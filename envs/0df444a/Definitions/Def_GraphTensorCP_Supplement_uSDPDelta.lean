-- Prove2me | Definitions.Def_GraphTensorCP_Supplement_uSDPDelta
-- name    : GraphTensorCP_Supplement_uSDPDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:22:36.608647+00:00
-- url     : https://prove2.me/theorems/e3590cfd-8d73-4f4c-b98a-5c23355186f4
-- title:
--   Path-strengthened semidefinite value $U^\Delta_{\mathrm{SDP}}(W)$
-- statement:
--   For a symmetric nonnegative zero-diagonal weight matrix $W$, define the **path-strengthened semidefinite value** by
--
--   $$
--   U^\Delta_{\mathrm{SDP}}(W)=\max\left\{\sum_{i<j}W_{i,j}P_{i,j}: P=P^{\mathsf T},\ P_{i,i}=0,\ J-2P\succeq0,\ P_{i,j}\le P_{i,k}+P_{k,j}\right\},
--   $$
--
--   where the last inequalities range over all distinct triples $i,j,k$. It is the semidefinite analogue of $U^\Delta_{\mathrm{CP}}$: positive-semidefinite feasibility replaces copositivity while retaining every path inequality.
--
--   **Formalization Note** Entrywise nonnegativity of $P$ is not added because the correlation-matrix constraint implies it. The maximum is represented by a real supremum; the paper proves that the feasible set is nonempty and compact.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 5.11, p.52

import Mathlib

namespace GraphTensorCP

namespace Supplement

/-- Feasibility for the **path-strengthened semidefinite program** (Zhou,
*Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*,
arXiv:2610.34273 (version of 2026-11-03), Definition 5.11, p.52): `P` is symmetric and
zero-diagonal, `J - 2P` is positive semidefinite, and all path inequalities
`P_ij ≤ P_ik + P_kj` hold for distinct `i,j,k`.

**Formalization Note.** `J` is the all-one matrix including its diagonal. The paper observes that
entrywise nonnegativity of `P` follows from the correlation-matrix constraint, so it is not added
as a separate condition. -/
def IsPathSDPFeasible {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.IsSymm ∧ (∀ i, P i i = 0) ∧
    (Matrix.of (fun _ _ => (1 : ℝ)) - (2 : ℝ) • P).PosSemidef ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → P i j ≤ P i k + P k j

/-- The **path-strengthened semidefinite value** `U^Δ_SDP(W)` (Zhou,
arXiv:2610.34273 (version of 2026-11-03), Definition 5.11, p.52): the maximum of
`Σ_{i<j} W_ij P_ij` over `IsPathSDPFeasible P`.

**Formalization Note.** The maximum is represented by `sSup`; the paper proves the feasible set
is nonempty and compact, so it is attained. This differs from the published `uCPDelta` only by
positive-semidefinite rather than copositive feasibility. -/
noncomputable def uSDPDelta {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {v : ℝ | ∃ P : Matrix (Fin n) (Fin n) ℝ, IsPathSDPFeasible P ∧
    v = ∑ i, ∑ j, if i < j then W i j * P i j else 0}

end Supplement

end GraphTensorCP


