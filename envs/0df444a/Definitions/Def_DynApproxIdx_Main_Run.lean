-- Prove2me | Definitions.Def_DynApproxIdx_Main_Run
-- name    : DynApproxIdx_Main_Run
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:51:20.69132+00:00
-- url     : https://prove2.me/theorems/60b133b8-5654-47b9-a6d8-21e45bd5b74d
-- title:
--   An online run of a randomized word-RAM program, operation by operation: time, output and space
-- statement:
--   The machine is the published word RAM `DynBrooks_Machine`: a program is a finite instruction list fixed before the word size $w$; memory is $\mathbb N\to\{0,1\}^w$, all zero at the start; arithmetic, bitwise operations, indirect addressing and jumps cost one step each; `coin` stores the next independent uniform $w$-bit word of the coin tape $\omega$; `read` stores the next pending input word and **blocks** while none is pending; `write` appends a word to the output.
--
--   A data structure is run **online**. Operation $0$ (initialization or preprocessing) starts at the all-zero configuration with its input words pending. The machine reaches a **completed state** when it is blocked at a `read` with no pending input; then the words of the next operation are delivered. For an operation $j$:
--   - its **time** is the number of steps from its start to the next completed state ($\infty$ if there is none, or if an earlier operation never completes);
--   - its **output** is the list of words written from its start until it completes;
--   - its **space** at a configuration is the number of memory cells holding a nonzero word.
--
--   An operation **runs within $(T,S)$** when it starts, completes within $T$ steps, and at every configuration of its run (from its start to its completion, inclusive) at most $S$ cells are nonzero:
--   $$\mathrm{time}_j\le T\quad\text{and}\quad \max_{0\le s\le \mathrm{time}_j}\ \bigl|\{a : \mathrm{mem}_s(a)\ne0\}\bigr|\le S.$$
--
--   This is the cost model of Theorem 1.1 and Fact 8.3.
--
--   **Formalization Note.** Because `read` blocks, the program cannot see an operation before the previous one has completed: no look-ahead. Space is the memory in use at each step, not the cumulative set of cells ever written (texts shrink, and queries use temporary memory). The plumbing (`stateAt`, `opStart`, `opTime`, `opOutput`) follows the published `DynColorWC_Main_Model`.
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), data-structure model of Theorem 1.1, p. 2 (PDF 4), and Fact 8.3, p. 44 (PDF 46)

import Mathlib
import Definitions.Def_DynBrooks_Machine

namespace DynApproxIdx.Main

open DynBrooks

/-! # An online run of a word-RAM program, operation by operation

Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*, STOC 2027 submission
(manuscript sha256 7f902057…): the data-structure model of Theorem 1.1, p. 2 (PDF 4), and of
Fact 8.3, p. 44 (PDF 46); the paper names no machine model.

**Formalization Note.** The machine is the published word RAM `DynBrooks` (memory `ℕ → BitVec w`,
all zero at the start; unit-cost uniform random words from the coin tape `ω`; a `read` that blocks
when no input is pending, so no look-ahead; a write-only output; every instruction one step).
* Operation `0` (the initialization/preprocessing) starts at the all-zero configuration with the
  words `inp` pending. Operation `j ≥ 1` is the `j`-th entry of `ops` (each operation given by its
  words): its words are delivered to the completed state reached after operations `0, …, j − 1`.
* The **time** of an operation is the number of steps from its start to the next completed state
  (`⊤` if there is none, or if an earlier operation never completes).
* The **output** of an operation is the list of words written from its start until it completes.
* The **space** of a configuration is the number of memory cells holding a nonzero word; an
  operation's space is bounded at every configuration of its run, from its start to its completion
  (not only at completed states, and not the cumulative set of cells ever written). -/

/-- The starting configuration: program counter `0`, all memory zero, coin cursor `0`, nothing
written, the words `inp` pending. -/
def initConfig (w : ℕ) (inp : List ℕ) : Config w :=
  ⟨0, fun _ => 0, inp, 0, [], ∅⟩

/-- From an optional completed state, deliver the operations in order, each run to the next
completed state (`none` once some operation never completes). -/
noncomputable def stateFrom (P : Program) {w : ℕ} (ω : ℕ → BitVec w) :
    Option (Config w) → List (List ℕ) → Option (Config w)
  | none, _ => none
  | some c, [] => some c
  | some c, op :: ops => stateFrom P ω (complete P ω (feed c op)) ops

/-- The completed state after operation `0` (on the words `inp`) and the first `j` entries of
`ops`. -/
noncomputable def stateAt (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) (j : ℕ) : Option (Config w) :=
  stateFrom P ω (complete P ω (initConfig w inp)) (ops.take j)

/-- The configuration at which operation `j` starts: the initial configuration for `j = 0`; for
`j ≥ 1`, the completed state after operations `0, …, j − 1` with the words of `ops[j − 1]`
delivered (`none` if that state is not reached or `ops` has no such entry). -/
noncomputable def opStart (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) : ℕ → Option (Config w)
  | 0 => some (initConfig w inp)
  | j + 1 =>
      match stateAt P ω inp ops j, ops[j]? with
      | some s, some op => some (feed s op)
      | _, _ => none

/-- The time of operation `j`: the number of steps from its start to the next completed state,
`⊤` if it never completes or does not start. -/
noncomputable def opTime (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) (j : ℕ) : ℕ∞ :=
  match opStart P ω inp ops j with
  | some c => time P ω c
  | none => ⊤

/-- The words written by operation `j`, from its start to its completion (`none` if it does not
complete). -/
noncomputable def opOutput (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) (j : ℕ) : Option (List ℕ) :=
  match opStart P ω inp ops j with
  | some c => (complete P ω c).map fun c' => c'.output.drop c.output.length
  | none => none

/-- The space in use at a configuration: the number of memory cells holding a nonzero word. -/
noncomputable def usedCells {w : ℕ} (c : Config w) : ℕ∞ :=
  {a : ℕ | c.mem a ≠ 0}.encard

/-- `LeReal x b`: the (possibly infinite) count `x` is finite and at most the real `b`. -/
def LeReal (x : ℕ∞) (b : ℝ) : Prop :=
  ∃ m : ℕ, x = (m : ℕ∞) ∧ (m : ℝ) ≤ b

/-- Operation `j` starts, completes within `T` steps, and at every configuration of its run (from
its start to its completion) at most `S` memory cells are nonzero. -/
def WithinBounds (P : Program) {w : ℕ} (ω : ℕ → BitVec w) (inp : List ℕ)
    (ops : List (List ℕ)) (j : ℕ) (T S : ℝ) : Prop :=
  ∃ c, opStart P ω inp ops j = some c ∧ LeReal (time P ω c) T ∧
    ∀ t : ℕ, (t : ℕ∞) ≤ time P ω c → LeReal (usedCells (run P ω c t)) S

end DynApproxIdx.Main


