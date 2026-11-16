-- Prove2me | Definitions.Def_MatMulDS_Supplement_DynOK
-- name    : MatMulDS_Supplement_DynOK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:12:06.817639+00:00
-- url     : https://prove2.me/theorems/60390a59-3923-4386-bd26-6eb660c399ef
-- title:
--   Worst-case guarantees of a dynamic data structure along an operation sequence
-- statement:
--   A **dynamic data structure** keeps its machine memories between operations. An operation is written to the negative cells $-1,-2,\dots$ of the memories (words and field elements), the data structure's program runs on the memories left by the previous operation, and an answer is read from negative cells afterwards.
--
--   Given an abstract state (the current matrix or graph), the guarantee along a list of operations is: every operation that is valid in the current state halts within its worst-case bound, its answer is correct for the current state, and the remaining operations are performed from the updated state and memories. Once an operation is invalid (for instance an update that makes a matrix singular), nothing more is required.
--
--   The machine is deterministic and every finite list is covered, so sequences of operations chosen adaptively from earlier answers are covered too. This expresses the worst-case update and query bounds of Theorems 8.8, 8.15 and 8.17.
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorems 8.8, 8.15, 8.17, pp.55–60 (PDF pp.57–62)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM

set_option autoImplicit false

open MatroidSensOracle

namespace MatMulDS.Supplement

/-- The memories `mem` with the words `ws` of an operation written to the word cells `−1, −2, …` and its field
elements `fs` to the field cells `−1, −2, …`; every other cell is kept. -/
def withOp {F : Type} [Zero F] {w : ℕ} (mem : (ℤ → BitVec w) × (ℤ → F)) (ws : List ℤ) (fs : List F) :
    (ℤ → BitVec w) × (ℤ → F) :=
  (fun a => if a < 0 ∧ (-a - 1).toNat < ws.length then BitVec.ofInt w (ws.getD (-a - 1).toNat 0) else mem.1 a,
   fun a => if a < 0 ∧ (-a - 1).toNat < fs.length then fs.getD (-a - 1).toNat 0 else mem.2 a)

/-- **Worst-case guarantees of a dynamic data structure along a sequence of operations.** Starting from the abstract
state `s` (the matrix or graph) and the machine memories `m`, every operation `op` of the list that is valid in the
current state halts, by `run m op t m'`, within `t ≤ bound s op m'` steps, its result `m'` satisfies `good s op m'`
(the answer of a query, read from `m'`), and the remaining operations are performed from `next s op` and `m'`. Once an
operation is invalid, nothing more is required.

Source: Alman, Nogler, Vassilevska Williams, STOC 2027 submission (held file sha256 6c5a1c16…), Theorems 8.8, 8.15,
8.17, pp.55–60: "worst-case" bounds per operation, for every sequence of operations.

**Formalization Note.**
* The memories persist between operations: an operation runs the data structure's program on the memories left by the
  previous one, with the operation written to the negative cells (`withOp`).
* The machine is deterministic and every finite sequence is covered, so sequences chosen adaptively, from earlier
  answers, are covered too. -/
def DynOK {S Op M : Type} (run : M → Op → ℕ → M → Prop) (valid : S → Op → Prop) (next : S → Op → S)
    (good : S → Op → M → Prop) (bound : S → Op → M → ℝ) : S → M → List Op → Prop
  | _, _, [] => True
  | s, m, op :: ops =>
    valid s op → ∃ (t : ℕ) (m' : M), run m op t m' ∧ (t : ℝ) ≤ bound s op m' ∧ good s op m' ∧
      DynOK run valid next good bound (next s op) m' ops

end MatMulDS.Supplement


