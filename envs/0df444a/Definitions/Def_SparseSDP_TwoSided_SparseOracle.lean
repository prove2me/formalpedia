-- Prove2me | Definitions.Def_SparseSDP_TwoSided_SparseOracle
-- name    : SparseSDP_TwoSided_SparseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:22.904197+00:00
-- url     : https://prove2.me/theorems/1dd23c89-7741-49a5-b95c-77b43128514e
-- title:
--   Sparse oracle access (Definition 2.1) and charged row reads
-- statement:
--   **Definition 2.1.** Sparse access to a matrix $M$ consists of $O_{\mathrm{sparse}}(M,i,k)$, the column of the $k$-th nonzero of row $i$ or a null symbol if the row has fewer than $k$ nonzeros, and $O_M(i,\ell)$, the entry. Each threshold $b_j$ is available by random access.
--
--   `SparseOracle I` holds $O_{\mathrm{sparse}}$ for $C$ and every $A_j$. `qCol`, `qEntry` and `qB` are the charged accessors, at unit cost, and they are the only places where a program reads the instance. `readRow` calls $O_{\mathrm{sparse}}$ for $k=1,2,\dots$ until null and reads each entry.
--
--   **Formalization Note** "The $k$-th nonzero" is read as any fixed enumeration of the row's nonzeros without repetition; column order is one instance.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Definition 2.1, p. 15; §1, p. 1

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Instance
import Definitions.Def_SparseSDP_TwoSided_RowAccess

open Matrix

namespace SparseSDP.TwoSided

variable {n m : ℕ}

/-- The input matrix with identifier `id`: `none` is `C`, `some j` is `Aⱼ`. -/
def matOf (I : Instance ℂ n m) : Option (Fin m) → Matrix (Fin n) (Fin n) ℂ
  | none => I.C
  | some j => I.A j

/-- Sparse oracle access (Definition 2.1, p. 15): `col id i k` is `O_sparse(M, i, k)`, the column of
the `k`-th nonzero of row `i` (`k = 1, 2, …`), or `none` if row `i` has fewer than `k` nonzeros.

**Formalization Note.** "The `k`-th nonzero" is read as any fixed enumeration of the row's nonzeros
without repetition; column order is one instance. -/
structure SparseOracle (I : Instance ℂ n m) where
  /-- `O_sparse`. -/
  col : Option (Fin m) → Fin n → ℕ → Option (Fin n)
  /-- `col` enumerates the nonzeros of the row. -/
  enum : ∀ id i, ∃ l : List (Fin n), l.Nodup ∧ (∀ c, c ∈ l ↔ matOf I id i c ≠ 0) ∧
    ∀ k, col id i (k + 1) = l[k]?

variable {I : Instance ℂ n m}

/-- One call to `O_sparse`, at unit cost. -/
def qCol (orc : SparseOracle I) (id : Option (Fin m)) (i : Fin n) (k : ℕ) :
    Prog (Option (Fin n)) := op 1 (orc.col id i k)

/-- One call to `O_M`, at unit cost. The entries of `I` are read here and nowhere else. -/
def qEntry (_orc : SparseOracle I) (id : Option (Fin m)) (i c : Fin n) : Prog ℂ :=
  op 1 (matOf I id i c)

/-- One random access to a threshold `bⱼ`, at unit cost (§2.2, p. 15). `I.b` is read here and nowhere
else. -/
def qB (_orc : SparseOracle I) (j : Fin m) : Prog ℝ := op 1 (I.b j)

/-- Read a row by calling `O_sparse` for `k = 1, 2, …` until `none`, reading each entry. A row has at
most `n` nonzeros, so `n + 1` calls always reach `none`. -/
def readRow (orc : SparseOracle I) (id : Option (Fin m)) (i : Fin n) :
    Prog (List (Fin n × ℂ)) := do
  let mut out : List (Fin n × ℂ) := []
  for k in List.range (n + 1) do
    tick 1
    let c ← qCol orc id i (k + 1)
    match c with
    | none => break
    | some cc =>
      let z ← qEntry orc id i cc
      tick 1
      out := (cc, z) :: out
  pure out

end SparseSDP.TwoSided


