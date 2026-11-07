-- Prove2me | Definitions.Def_MultiphaseDisj_CellProbe
-- name    : MultiphaseDisj_CellProbe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:45.656944+00:00
-- url     : https://prove2.me/theorems/4889124f-a6ae-4b3a-a989-e549c5e7e432
-- title:
--   Cell-probe programs over $w$-bit words
-- statement:
--   In the **cell-probe model** memory consists of $2^w$ cells, each holding a $w$-bit word; cells are addressed by $w$-bit words. A read or a write of one cell costs one **probe**, and all computation is free.
--
--   An operation is a **probe program**, an adaptive decision tree: at each node it either stops with a result, reads a cell $a$ and continues according to the full content $c$ of that cell, or writes a word $c$ into a cell $a$ and continues. Running a program on a memory $M$ gives its result, the memory afterwards, the number of probes made (a cell probed twice counts twice) and the set of cells written. A **read-only program** has no write nodes; running it gives its answer, its number of probes and the list of cells it read, in order.
--
--   These are the operations of every data structure in the mission: insertions are probe programs, queries are read-only probe programs.
--
--   **Formalization Note** Words are `BitVec w`; a memory is a function from words to words. Branching on the whole content of every cell read is what makes computation and temporary workspace within an operation free (§2.1): any computation on the values read so far is encoded in the shape of the tree. A query that writes into temporary workspace can be replaced by a read-only one with no more probes.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), §1.1.2, p.3 (cell-probe model); §2.1 Cell-probe conventions, p.11

import Mathlib

set_option autoImplicit false

namespace MultiphaseDisj

/-- A `w`-bit word, used both for cell addresses and for cell contents
(Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904,
held version sha256 ba26649b…, §2.1 Cell-probe conventions, p.11: "Cells and addresses have
w bits").

**Formalization Note** Words are `BitVec w`; there are `2 ^ w` cells. -/
abbrev Word (w : ℕ) : Type := BitVec w

/-- A memory state of the cell-probe model: the content of every one of the `2 ^ w` cells
(arXiv:2610.10904, §1.1.2, p.3: "memory consists of w-bit cells"). -/
abbrev Mem (w : ℕ) : Type := Word w → Word w

/-- A cell-probe program that may read and write memory, returning a value of type `α`
(arXiv:2610.10904, §1.1.2, p.3 and §2.1, p.11). It is an adaptive decision tree: `read a k`
probes cell `a` and continues with `k c`, where `c` is the content read; `write a c k`
overwrites cell `a` with `c` and continues with `k`; `ret x` stops with result `x`.

**Formalization Note** Computation and temporary workspace within an operation are free
(§2.1): the program branches on the full content of every cell it has read, so any computation
on the values read so far is encoded in the shape of the tree, at no cost. Only `read` and
`write` are charged. -/
inductive Prog (w : ℕ) (α : Type) : Type where
  | ret : α → Prog w α
  | read : Word w → (Word w → Prog w α) → Prog w α
  | write : Word w → Word w → Prog w α → Prog w α

namespace Prog

variable {w : ℕ} {α : Type}

/-- Run a program on a memory: its result and the memory afterwards. -/
def run : Prog w α → Mem w → α × Mem w
  | ret x, M => (x, M)
  | read a k, M => run (k (M a)) M
  | write a c k, M => run k (Function.update M a c)

/-- The number of probes of a run: one per `read` and one per `write` (a cell probed twice
counts twice). -/
def probes : Prog w α → Mem w → ℕ
  | ret _, _ => 0
  | read a k, M => probes (k (M a)) M + 1
  | write a c k, M => probes k (Function.update M a c) + 1

/-- The set of cells written during a run. -/
def writes : Prog w α → Mem w → Finset (Word w)
  | ret _, _ => ∅
  | read a k, M => writes (k (M a)) M
  | write a c k, M => insert a (writes k (Function.update M a c))

end Prog

/-- A read-only cell-probe program (a query: "it does not write", arXiv:2610.10904, Problem 1,
p.5). `read a k` probes cell `a` and continues with `k c`; `ret x` answers `x`.

**Formalization Note** A query that writes into temporary workspace is simulated by a
read-only one with no more probes, because workspace within an operation is free (§2.1). -/
inductive QProg (w : ℕ) (α : Type) : Type where
  | ret : α → QProg w α
  | read : Word w → (Word w → QProg w α) → QProg w α

namespace QProg

variable {w : ℕ} {α : Type}

/-- The answer of a read-only program on a memory. -/
def eval : QProg w α → Mem w → α
  | ret x, _ => x
  | read a k, M => eval (k (M a)) M

/-- The number of cells read by a run (with repetitions). -/
def probes : QProg w α → Mem w → ℕ
  | ret _, _ => 0
  | read a k, M => probes (k (M a)) M + 1

/-- The list of cells read by a run, in order. -/
def probed : QProg w α → Mem w → List (Word w)
  | ret _, _ => []
  | read a k, M => a :: probed (k (M a)) M

end QProg

end MultiphaseDisj


