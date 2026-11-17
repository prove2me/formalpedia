-- Prove2me | Definitions.Def_MatMulTimeLP_Supplement_LabeledRowQueryStructure
-- name    : MatMulTimeLP_Supplement_LabeledRowQueryStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:57:04.80482+00:00
-- url     : https://prove2.me/theorems/cf95414d-db13-40b9-938a-531399565341
-- title:
--   Stateful exact-real-RAM interface for labeled row queries
-- statement:
--   A **labeled row-query structure** of dimension $n$ with $K$ layers consists of four persistent exact-real-RAM programs implementing initialization, exact row queries, value changes and label changes. The fixed matrix $H$ remains in read-only input memory, while the mutable vector $x$ and labels $\ell(i)\in\{0,\ldots,K-1\}$ occupy disjoint state blocks.
--
--   Operation loaders reset only the program counter and write the requested coordinate and new value or label. The decoded state therefore makes the exact post-call semantics and instruction count independently checkable. The accompanying layer-count functions give $|L_{\ge a}|$, $|L_{>a}|$ and $|L_{[p,q]}|$ from the labels before a call.
--
--   This interface supports the complete four-operation statement of Theorem 5.13 while retaining the paper’s fixed-matrix, mutable-state interpretation.
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…), Theorem 5.13 and Eq. (12), pp.32–34

import Mathlib
import Definitions.Def_MatMulTimeLP_Supplement_ResidualSamplerImplementation

namespace MatMulTimeLP

namespace Supplement

set_option autoImplicit false

/-!
# Stateful exact-real-RAM interface for labeled row queries

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 5.13 and Eq. (12), pp.32–34.

**Formalization Note** `H` is present in read-only input memory, matching the paper's `O(n)`
initialization despite its `n^2` entries.  The mutable vector begins at real address `n*n`; labels
begin at index address `4`.  Call loaders reset the program counter and write only their arguments,
so they cannot update the caches for free.  All work is the number of executed instructions through
the first halt of the published exact-real RAM.
-/

/-- Address of `x_i` in a row-query state. -/
def rowXAddr (n : ℕ) (i : Fin n) : ℕ := n * n + i

/-- Reserved real argument cell and query-output cell. -/
def rowArgAddr (n : ℕ) : ℕ := n * n + n
def rowOutputAddr (n : ℕ) : ℕ := n * n + n + 1

/-- Address of label `ℓ(i)` in the index bank. -/
def rowLabelAddr (i : ℕ) : ℕ := 4 + i

/-- Initial memory with the fixed matrix already present and `K` in index cell `3`. -/
noncomputable def rowInitState {n K : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : State :=
  let s := initState (matToList H)
  { s with N := Function.update s.N 3 K }

/-- Load `Query(i)`. -/
def loadRowQuery {n : ℕ} (s : State) (i : Fin n) : State :=
  { s with pc := 0, N := Function.update s.N 0 i }

/-- Load `SetValue(i,ξ)`. -/
def loadRowSetValue {n : ℕ} (s : State) (i : Fin n) (xi : ℝ) : State :=
  { s with
    pc := 0
    R := Function.update s.R (rowArgAddr n) xi
    N := Function.update s.N 0 i }

/-- Load `SetLabel(i,c)`, with `c : Fin K`. -/
def loadRowSetLabel {n K : ℕ} (s : State) (i : Fin n) (c : Fin K) : State :=
  { s with pc := 0, N := Function.update (Function.update s.N 0 i) 1 c }

/-- The maintained vector and labels decoded from a state. -/
def rowStateX {n : ℕ} (s : State) : Fin n → ℝ := fun i => s.R (rowXAddr n i)
def rowStateLabel {n : ℕ} (s : State) (i : Fin n) : ℕ := s.N (rowLabelAddr i)

/-- The fixed matrix is still present and every current label lies in `{0,…,K-1}`. -/
def RowValidState {n K : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : State) : Prop :=
  (∀ (i j : Fin n), s.R ((i : ℕ) * n + (j : ℕ)) = H i j) ∧
    ∀ i : Fin n, rowStateLabel s i < K

/-- Number of current coordinates in layers at least `a`. -/
def rowLayersGE {n : ℕ} (s : State) (a : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin n => a ≤ rowStateLabel s j).card

/-- Number of current coordinates in layers strictly above `a`. -/
def rowLayersGT {n : ℕ} (s : State) (a : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin n => a < rowStateLabel s j).card

/-- Number of current coordinates in the inclusive layer interval `[p,q]`. -/
def rowLayersBetween {n : ℕ} (s : State) (p q : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin n => p ≤ rowStateLabel s j ∧ rowStateLabel s j ≤ q).card

/-- Uniform real-RAM programs and first-halt-time witnesses for all fixed matrices of shape
`n × n` with `K` labels.  The programs are selected before the matrix. -/
structure LabeledRowQueryStructure (n K : ℕ) where
  initProgram : Program
  queryProgram : Program
  setValueProgram : Program
  setLabelProgram : Program
  initTime : Matrix (Fin n) (Fin n) ℝ → Tape → ℕ
  queryTime : State → Fin n → Tape → ℕ
  setValueTime : State → Fin n → ℝ → Tape → ℕ
  setLabelTime : State → Fin n → Fin K → Tape → ℕ

noncomputable def LabeledRowQueryStructure.initResult {n K : ℕ}
    (Q : LabeledRowQueryStructure n K) (H : Matrix (Fin n) (Fin n) ℝ) (ω : Tape) : State :=
  stateAtFrom Q.initProgram ω (rowInitState (K := K) H) (Q.initTime H ω)

noncomputable def LabeledRowQueryStructure.queryResult {n K : ℕ}
    (Q : LabeledRowQueryStructure n K) (s : State) (i : Fin n) (ω : Tape) : State :=
  stateAtFrom Q.queryProgram ω (loadRowQuery s i) (Q.queryTime s i ω)

noncomputable def LabeledRowQueryStructure.setValueResult {n K : ℕ}
    (Q : LabeledRowQueryStructure n K) (s : State) (i : Fin n) (xi : ℝ) (ω : Tape) : State :=
  stateAtFrom Q.setValueProgram ω (loadRowSetValue s i xi) (Q.setValueTime s i xi ω)

noncomputable def LabeledRowQueryStructure.setLabelResult {n K : ℕ}
    (Q : LabeledRowQueryStructure n K) (s : State) (i : Fin n) (c : Fin K) (ω : Tape) : State :=
  stateAtFrom Q.setLabelProgram ω (loadRowSetLabel s i c) (Q.setLabelTime s i c ω)

/-- One post-initialization operation of the labeled row-query structure. -/
inductive RowOp (n K : ℕ) where
  | query (i : Fin n)
  | setValue (i : Fin n) (xi : ℝ)
  | setLabel (i : Fin n) (c : Fin K)

noncomputable def rowRunAux {n K : ℕ} (Q : LabeledRowQueryStructure n K) :
    List (RowOp n K) → State → ℕ → CallTapes → State
  | [], s, _, _ => s
  | op :: ops, s, q, Ω =>
      let s' := match op with
        | RowOp.query i => Q.queryResult s i (Ω q)
        | RowOp.setValue i xi => Q.setValueResult s i xi (Ω q)
        | RowOp.setLabel i c => Q.setLabelResult s i c (Ω q)
      rowRunAux Q ops s' (q + 1) Ω

/-- State after initialization and a finite interleaving of row-query operations. -/
noncomputable def rowRun {n K : ℕ} (Q : LabeledRowQueryStructure n K)
    (H : Matrix (Fin n) (Fin n) ℝ) (ops : List (RowOp n K)) (Ω : CallTapes) : State :=
  rowRunAux Q ops (Q.initResult H (Ω 0)) 1 Ω

/-- A state reachable from the prescribed initialization through finitely many calls.  This carries
the cache invariant of Eq. (12) without exposing the implementation's private cache layout. -/
def LabeledRowQueryStructure.Reachable {n K : ℕ} (Q : LabeledRowQueryStructure n K)
    (H : Matrix (Fin n) (Fin n) ℝ) (s : State) : Prop :=
  ∃ (ops : List (RowOp n K)) (Ω : CallTapes), rowRun Q H ops Ω = s

end Supplement

end MatMulTimeLP


