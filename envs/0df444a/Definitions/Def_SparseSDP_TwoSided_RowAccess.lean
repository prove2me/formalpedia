-- Prove2me | Definitions.Def_SparseSDP_TwoSided_RowAccess
-- name    : SparseSDP_TwoSided_RowAccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:21.433848+00:00
-- url     : https://prove2.me/theorems/887463e5-643e-47cc-a456-01f214744948
-- title:
--   Charged row access to a family of real matrices, and charged matrix–vector products
-- statement:
--   A **sparse row** is a list of (column, value) pairs. `IsRow row v` says the columns are distinct, each value is the entry of $v$, and every nonzero of $v$ is listed.
--
--   A **row access** for $k$ real $d\times d$ matrices is a charged procedure reading row $i$ of matrix $j$. `RowAccess.Spec acc M s c` says: from every state, the procedure returns the true row with at most $cs$ entries, pays at most $cs$ and does not move the cursor. Algorithm 7 reads its matrices only through such an access, so one statement covers both plain $A_j$ and the derived $D_j(g)$: "All accesses to these derived matrices below are complete row scans or matrix–vector products" (p. 19).
--
--   `Implements mv K TK` says the charged procedure `mv` computes $v\mapsto Kv$ at cost at most $T_K$.
--
--   **Formalization Note** Zero entries may be listed, because merging a diagonal term can cancel an entry and the paper needs no oracle for nonzeros after cancellation.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §2.6.2, p. 19; Eq. (350), p. 62

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Prog

open Matrix

namespace SparseSDP.TwoSided

variable {d k : ℕ}

/-- A row in sparse form: a list of (column, value) pairs. -/
abbrev SparseRow (d : ℕ) : Type := List (Fin d × ℝ)

/-- `row` represents the row `v`: its columns are distinct, each value is the entry of `v`, and every
nonzero of `v` is listed.

**Formalization Note.** Zero entries may be listed: the paper's derived rows merge a diagonal term,
and "no constant-time oracle for the k-th nonzero after cancellation is needed" (p. 19). -/
def IsRow (row : SparseRow d) (v : Vec d) : Prop :=
  (row.map Prod.fst).Nodup ∧ (∀ p ∈ row, v p.1 = p.2) ∧ ∀ c, v c ≠ 0 → c ∈ row.map Prod.fst

/-- The inner product of a sparse row with a stored vector, as in Eq. (350), p. 62. -/
noncomputable def rowDot (row : SparseRow d) (x : Vec d) : Prog ℝ :=
  op (2 * row.length + 1) (row.map fun p => p.2 * x p.1).sum

/-- A charged row reader for `k` real matrices of size `d`. Algorithm 7 reads its matrices only
through it, so it covers both plain `Aⱼ` and the derived `Dⱼ(g)`: "All accesses to these derived
matrices below are complete row scans or matrix–vector products" (§2.6.2, p. 19). -/
structure RowAccess (d k : ℕ) where
  /-- Read row `i` of matrix `j`. -/
  read : Fin k → Fin d → Prog (SparseRow d)

/-- `acc` reads the matrices `M`: from every state it returns the true row with at most `c s` entries,
pays at most `c s`, and leaves the cursor alone. -/
def RowAccess.Spec (acc : RowAccess d k) (M : Fin k → Mat d) (s : ℕ) (c : ℝ) : Prop :=
  ∀ j i tape cur cnt,
    IsRow ((acc.read j i).exec tape cur cnt).1.1 (M j i) ∧
    (((acc.read j i).exec tape cur cnt).1.1.length : ℝ) ≤ c * s ∧
    ((acc.read j i).exec tape cur cnt).1.2 = cur ∧
    cnt ≤ ((acc.read j i).exec tape cur cnt).2 ∧
    (((acc.read j i).exec tape cur cnt).2 : ℝ) ≤ cnt + c * s

/-- `mv` is a charged product with `K` of cost at most `TK` (the `T_K` of Fact 4.2, p. 26). -/
def Implements (mv : Vec d → Prog (Vec d)) (K : Mat d) (TK : ℝ) : Prop :=
  ∀ v tape cur cnt,
    ((mv v).exec tape cur cnt).1.1 = K *ᵥ v ∧
    ((mv v).exec tape cur cnt).1.2 = cur ∧
    cnt ≤ ((mv v).exec tape cur cnt).2 ∧
    (((mv v).exec tape cur cnt).2 : ℝ) ≤ cnt + TK

end SparseSDP.TwoSided


