-- Prove2me | Definitions.Def_GraphTensorCP_IsDimMatrix
-- name    : GraphTensorCP_IsDimMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:10.219237+00:00
-- url     : https://prove2.me/theorems/70e3a003-49a3-4d20-aa47-cda0138b8279
-- title:
--   Dimension matrix $Q$, logarithmic edge weights $W=\log_2 Q$, and nonnegative weight matrices
-- statement:
--   A **dimension matrix** of order $n$ is a symmetric $n\times n$ matrix $Q$ of positive integers with all diagonal entries equal to $1$. Its **logarithmic edge-weight matrix** is the real symmetric matrix $W$ with entries
--
--   $$W_{i,j}=\log_2 Q_{i,j}\qquad(1\le i,j\le n).$$
--
--   Thus $W$ is nonnegative with zero diagonal, and an entry $Q_{i,j}=1$ (weight $0$) represents an absent edge. More generally, a **nonnegative weight matrix** is a symmetric real matrix with nonnegative entries and zero diagonal; this is the domain of the maximum cut, the weighted graph exponent $\Gamma_{\mathbb F}$ and the bound $U^\Delta_{\mathrm{CP}}$.
--
--   A dimension matrix specifies, for every pair of tensor legs, the dimension of the edge (identity) tensor shared by them; $W$ records these dimensions in bits.
--
--   **Formalization Note** Vertices are indexed by $\mathrm{Fin}\,n=\{0,\dots,n-1\}$. $\log_2$ is `Real.logb 2`; for a dimension matrix every entry is at least $1$, so no default value of the logarithm is used. The standing assumption $n\ge2$ is stated in each theorem.
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.21, p.22; Definitions 2.26–2.27, p.25

import Mathlib

namespace GraphTensorCP

/-- **Dimension matrix** (Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely
Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 2.21, p.22):
"A symmetric positive integer matrix Q of order n with diagonal entries one is called a
dimension matrix."

**Formalization Note.** Vertices are `Fin n = {0, …, n−1}` (the paper's `1, …, n`). The
paper's standing assumption `n ≥ 2` (§2.3, p.22) is stated in each theorem, not here. -/
def IsDimMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  Q.IsSymm ∧ (∀ i j, 1 ≤ Q i j) ∧ ∀ i, Q i i = 1

/-- **Logarithmic edge-weight matrix** (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definition 2.21, p.22): "Its logarithmic edge-weight matrix is the real symmetric matrix W whose
entries are W_{i,j} = log₂ Q_{i,j} for 1 ≤ i, j ≤ n."

**Formalization Note.** `log₂` is `Real.logb 2`. For a dimension matrix every entry is
`≥ 1`, so no junk value of the logarithm is used. -/
noncomputable def logWeight {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.logb 2 (Q i j)

/-- **Nonnegative weight matrix** (Zhou, arXiv:2610.34273 (version of 2026-11-03),
Definitions 2.26–2.27, p.25): a "nonnegative symmetric real matrix W of order n with zero
diagonal". This is the domain of `MaxCut`, `Γ_F` and `U^Δ_CP`. -/
def IsWeightMatrix {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  W.IsSymm ∧ (∀ i, W i i = 0) ∧ ∀ i j, 0 ≤ W i j

end GraphTensorCP


