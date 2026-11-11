-- Prove2me | Definitions.Def_LpSubspaceCoreset_SmallP_Instance
-- name    : LpSubspaceCoreset_SmallP_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:47:49.138252+00:00
-- url     : https://prove2.me/theorems/ce79c5e7-5214-4d9d-b5c0-662cb2a1669f
-- title:
--   Instance encoding and output decoding for the randomized real RAM
-- statement:
--   An instance $(A,k)$ with $A\in\mathbb R^{n\times d}$ is given by its nonzero entries. A **sparse listing** of $A$ is a duplicate-free list of the positions $(i,j)$ (0-based) of exactly the nonzero entries of $A$, in any order; $\mathrm{nnz}(A)$ is the number of nonzero entries.
--
--   **Input.** The integer memory holds, from cell $0$, $n,d,k,\mathrm{nnz}(A)$ followed by the row and column of each listed position; the real memory holds, from cell $0$, the real parameters (for the main theorem $p,\varepsilon$) followed by the listed entry values in the same order.
--
--   **Output.** Integer cell $-1$ holds the number $s$ of output pairs, integer cell $-2-j$ the row index $i_j$ and real cell $-1-j$ the weight $s_j$ of pair $j$. A valid reweighted row subset has every $i_j\in[0,n)$ and every $s_j>0$; it decodes to $S\in\mathbb R^{s\times n}$ with row $j$ equal to $s_je_{i_j}^\top$, so $\mathrm{cost}_{SA}(F)=\sum_js_j^p\|Q_Fa_{i_j}\|_2^p$ (repeated indices are merged automatically), and its size is the number of distinct $i_j$. An index-set output (Lemma 2.5) uses the integer cells only.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 3–4 and §2.1 p. 8 (nnz(A)); reading of the mission

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Machine

namespace LpSubspaceCoreset.SmallP

/-!
# Instance encoding and output decoding for the randomized real RAM

Lin, Mirrokni, Woodruff, arXiv:2608.26047: `A ∈ ℝ^{n×d}` is "given by its nonzero entries"
(running times are in terms of `nnz(A)`, §2.1, p. 8). This layout is a reading of the mission.

**Input.** A sparse listing of `A` is a duplicate-free list `L` of the positions `(i, j)`
(0-based) of exactly the nonzero entries of `A`, in any order.
* Integer memory, from cell `0`: `n, d, k, nnz(A)`, then for each listed position its row and
  its column (`2·nnz(A)` cells).
* Real memory, from cell `0`: the real parameters `params` (for the goal `[p, ε]`), then the
  listed entry values `A_{ij}` in the order of `L`.

**Output** (read from the halted state).
* Integer cell `−1` holds the number `s` of output pairs; integer cell `−2 − j` holds the row
  index `i_j` (0-based) of pair `j` and real cell `−1 − j` its weight `s_j` (`0 ≤ j < s`).
* A valid row-subset output has `s ≥ 0`, every `i_j ∈ [0, n)` and every `s_j > 0`.
* The decoded sampling matrix `S ∈ ℝ^{s×n}` has row `j` equal to `s_j e_{i_j}^⊤`, so `SA` has
  rows `s_j a_{i_j}^⊤` and repeated indices are merged automatically:
  `cost_{SA}(F) = Σ_j s_j^p ‖Q_F a_{i_j}‖^p`. Its size is the number of distinct `i_j`.
* An index-set output (Lemma 2.5) uses the same integer cells and ignores the real cells.
-/

/-- `nnz(A)`: the number of nonzero entries of `A`. -/
noncomputable def nnz {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : ℕ :=
  by classical exact (Finset.univ.filter fun e : Fin n × Fin d => A e.1 e.2 ≠ 0).card

/-- `L` lists, without repetition, exactly the positions of the nonzero entries of `A`. -/
def IsSparseListing {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (L : List (Fin n × Fin d)) :
    Prop :=
  L.Nodup ∧ ∀ e : Fin n × Fin d, e ∈ L ↔ A e.1 e.2 ≠ 0

/-- The initial state on the instance `(A, k)` given by the listing `L`, with the real
parameters `params` in front of the entry values. -/
noncomputable def inputState {n d : ℕ} (k : ℕ) (params : List ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (L : List (Fin n × Fin d)) : State :=
  initState
    ([(n : ℤ), (d : ℤ), (k : ℤ), (L.length : ℤ)] ++
      L.flatMap fun e => [((e.1 : ℕ) : ℤ), ((e.2 : ℕ) : ℤ)])
    (params ++ L.map fun e => A e.1 e.2)

/-- The number of output pairs (integer cell `−1`). -/
def outCount (s : State) : ℤ := s.intMem (-1)

/-- The row index of output pair `j` (integer cell `−2 − j`). -/
def outIndex (s : State) (j : ℕ) : ℤ := s.intMem (-2 - (j : ℤ))

/-- The weight of output pair `j` (real cell `−1 − j`). -/
def outWeight (s : State) (j : ℕ) : ℝ := s.core.mem (-1 - (j : ℤ))

/-- The output is a list of row indices in `[0, n)`. -/
def ValidIndexOutput (n : ℕ) (s : State) : Prop :=
  0 ≤ outCount s ∧ ∀ j : ℕ, (j : ℤ) < outCount s → 0 ≤ outIndex s j ∧ outIndex s j < n

/-- The output is a reweighted row subset: indices in `[0, n)` and positive weights. -/
def ValidRowSubsetOutput (n : ℕ) (s : State) : Prop :=
  ValidIndexOutput n s ∧ ∀ j : ℕ, (j : ℤ) < outCount s → 0 < outWeight s j

/-- The decoded sampling matrix `S ∈ ℝ^{s×n}`: row `j` is `s_j e_{i_j}^⊤`. -/
noncomputable def outMatrix (n : ℕ) (s : State) :
    Matrix (Fin (outCount s).toNat) (Fin n) ℝ :=
  fun j i => if outIndex s j = ((i : ℕ) : ℤ) then outWeight s j else 0

/-- The set of distinct output row indices. -/
noncomputable def outRows (n : ℕ) (s : State) : Finset (Fin n) :=
  by classical exact
    Finset.univ.filter fun i : Fin n => ∃ j : Fin (outCount s).toNat, outIndex s j = ((i : ℕ) : ℤ)

end LpSubspaceCoreset.SmallP


