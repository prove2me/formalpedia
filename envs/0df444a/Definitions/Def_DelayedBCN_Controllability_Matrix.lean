-- Prove2me | Definitions.Def_DelayedBCN_Controllability_Matrix
-- name    : DelayedBCN_Controllability_Matrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:03:28.176339+00:00
-- url     : https://prove2.me/theorems/cc1a818d-53aa-4bba-9649-f23371da2516
-- title:
--   The transition-count matrix Q, its zeroed and deleted forbidden-set versions, and irreducibility (Definition 3.7)
-- statement:
--   Let $F$ be a delayed Boolean control network with $n$ state nodes, $m$ inputs and delay length $\mu$, as in the model file.
--
--   1. **The matrix $Q=L\ltimes\mathbf 1_{2^m}$ (p. 483).** Its rows and columns are indexed by trajectories, and
--   $$
--   Q_{b,a}=\#\{u\in\mathcal D^m:\ \text{one step from the trajectory } a \text{ under the input } u \text{ gives } b\},
--   $$
--   the row being the target and the column the source (this is what the proof of Proposition 3.5 establishes for $y_b^{\mathsf T}Qy_a$).
--   2. **$Q_{C_t}$ (Proposition 3.5).** For a set $C_t$ of trajectories, the matrix obtained from $Q$ by substituting zeros in the rows and columns of the trajectories in $C_t$; it keeps the size of $Q$.
--   3. **$\mathbb Q_{C_t}$ (before Theorem 3.12).** The matrix obtained from $Q$ by deleting the rows and columns of the trajectories in $C_t$; it is $q\times q$ with $q=2^{\mu n}-|C_t|$.
--   4. **Definition 3.7.** A real $N\times N$ matrix $A$ with $N\ge2$ is **reducible** if there are a permutation matrix $P$ and an integer $1\le r\le N-1$ with
--   $$
--   P^{\mathsf T}AP=\begin{pmatrix}A_{11}&A_{12}\\ 0&A_{22}\end{pmatrix},
--   $$
--   where $A_{11}$ is $r\times r$ and the zero block is $(N-r)\times r$. A matrix is **irreducible** if it is not reducible; in particular every $1\times1$ matrix (and the empty matrix) is irreducible.
--
--   Theorems 3.10 and 3.12 characterize trajectory controllability by the irreducibility of $Q$ and $\mathbb Q_{C_t}$; Proposition 3.5 and Theorem 5.1 count control sequences by powers of the zeroed matrices.
--
--   **Formalization Note** Rows and columns are indexed by trajectories rather than by their index $j$ in $\delta^j_{2^{\mu n}}$; the paper's $Q$ is obtained by the simultaneous relabelling of Lemma 2.6, and every statement of the mission (entries of powers, sums over sets of trajectories, Definition 3.7) is invariant under it. $\mathbb Q_{C_t}$ is indexed by the subtype of allowed trajectories; Definition 3.7 is invariant under reindexing, so its order is immaterial. Definition 3.7 is encoded with a bijection $e$ from $\{0,\dots,N-1\}$ onto the index set, $(P^{\mathsf T}AP)_{ij}=A_{e(i),e(j)}$. It is **not** Mathlib's `Matrix.IsIrreducible`, which calls the $1\times1$ zero matrix reducible. Entries are natural numbers; the irreducibility statements cast them to $\mathbb R$.
-- source:
--   Lu, Zhong, Ho, Tang & Cao, On Controllability of Delayed Boolean Control Networks, SIAM J. Control Optim. 54(2) 2016, pp. 483, 485-486, definition of Q (p. 483), Proposition 3.5 (Q_{C_t}), Definition 3.7, definition of ℚ_{C_t} (p. 486)

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model

namespace DelayedBCN.Controllability

/-- `Q = L ⋉ 1_{2^m}` read entrywise: `Q b a` is the number of input values `u` with
`step F u a = b` (row = target trajectory, column = source trajectory). Rows and columns are
indexed by trajectories instead of their `δ`-index. -/
def Q {μ n m : ℕ} (F : Network μ n m) : Matrix (Traj μ n) (Traj μ n) ℕ :=
  fun b a => (Finset.univ.filter (fun u : Input m => step F u a = b)).card

/-- `Q_{C_t}` (Proposition 3.5): `Q` with zeros substituted in the rows and columns of the
trajectories in `Ct` (same size as `Q`). -/
def QZeroed {μ n m : ℕ} (F : Network μ n m) (Ct : Finset (Traj μ n)) :
    Matrix (Traj μ n) (Traj μ n) ℕ :=
  fun b a => if b ∈ Ct ∨ a ∈ Ct then 0 else Q F b a

/-- `ℚ_{C_t}` (before Theorem 3.12): `Q` with the rows and columns of the trajectories in `Ct`
deleted, indexed by the allowed trajectories. -/
def QDeleted {μ n m : ℕ} (F : Network μ n m) (Ct : Finset (Traj μ n)) :
    Matrix {a : Traj μ n // a ∉ Ct} {a : Traj μ n // a ∉ Ct} ℕ :=
  fun b a => Q F b.1 a.1

/-- Definition 3.7 (reducible): for `N = card ι`, there are a relabelling `e` of `Fin N` onto the
index set (the permutation matrix `P`, `(Pᵀ A P) i j = A (e i) (e j)`) and `1 ≤ r ≤ N - 1` such that
the lower-left `(N - r) × r` block of `Pᵀ A P` vanishes. Requires `N ≥ 2`. This is **not** Mathlib's
`Matrix.IsIrreducible`. -/
def IsReducibleMat {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ e : Fin (Fintype.card ι) ≃ ι, ∃ r : ℕ, 1 ≤ r ∧ r ≤ Fintype.card ι - 1 ∧
    ∀ i j : Fin (Fintype.card ι), r ≤ i.val → j.val < r → A (e i) (e j) = 0

/-- Definition 3.7 (irreducible): not reducible. Every `1 × 1` (and the empty) matrix is
irreducible. -/
def IsIrreducibleMat {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ¬ IsReducibleMat A

end DelayedBCN.Controllability


