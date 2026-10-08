-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
-- name    : APSPSource_ThreeSumApsp_Lang_Compiler_Cells
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:28:41.959974+00:00
-- url     : https://prove2.me/theorems/e9bf84e1-f510-469c-9f5b-6b4952cbb7fc
-- title:
--   Memory representation and writable regions of the compiler
-- statement:
--   A compiler-size record extends the code layout with execution limits and stack capacity. For word width $W$, its fit conditions require the signed representation to contain the needed value differences, memory addresses, stack addresses, and constant-pool entries:
--
--   $$2(2\,\mathrm{word}+2)<2^W,\quad2\,\mathrm{space}<2^W,\quad4Q<2^W,\quad2N<2^W.$$
--
--   The state-representation relation says that machine memory contains the constants one, zero, and minus one, the integer constant pool, the frame pointer, the local variables in their stack cells, and the structured memory at nonnegative addresses below the memory limit. The framed relation additionally places the frame between stack cell one and capacity $Q$.
--
--   Named address sets specify temporary registers, stack intervals, the outermost frame, the constant pool, fixed constants, and scratch storage. For a statement running in frame $q$, the writable region is the union of scratch registers, the frame-pointer cell, stack cells from $q$ to $Q$, and valid nonnegative memory addresses. These data and predicates define the memory interface used by compiler simulation proofs.
--
--   References:
--
--   1. [Source formalization, lines 56–63](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L56-L63).
--   2. [Source formalization, lines 70–81](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L70-L81).
--   3. [Source formalization, lines 85–109](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L85-L109).
--   4. [Source formalization, lines 214–222](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L214-L222).
--   5. [Source formalization, lines 290–295](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L290-L295).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L56-L63; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L70-L81; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L85-L109; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L214-L222; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/Cells.lean#L290-L295

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The cells of the compiled code, and the memories that represent a state

The memory of the machine is one array indexed by the integers, and the compiled code keeps its
registers, temporaries, pool, stack and the memory of the light language in different parts of it.
Every proof about compiled code has to know that a write to one cell leaves the others alone.  This
file settles that once.

* Sets of cells: `Temps k F` (what evaluating an expression into T_k may change), `Scratch F` (what
  any compiled code uses freely), `Constants N` (what no compiled statement changes), `Writable Z q`
  (what a statement that runs in the frame q may change), and two parts of the memory, `Stack q Q`
  and `Pool N`.  "The memories m and m' differ only inside s" is `AgreeOutside s m m'`.
* The tactic `cells` proves that two cells are different, that a cell is or is not in one of these
  sets, or that one of these sets lies in another.  The tactic `cell_read` reads a cell of a memory
  that is given by writes.
* `Sizes W` collects the numbers that never change, with the assumptions on them: the layout of the
  code, the limits, the number of stack cells, and a word size W that fits them (`Fits`).
* `Rel Z σ q m`: the memory m represents the state σ in the frame q.  The relation survives changes
  of scratch cells (`Rel.same`) and of the stack beyond the frame (`Rel.beyond`); a write to the
  cell of a local variable or to a memory cell is the same write in the state (`Rel.setLoc`,
  `Rel.setMem`).  All four come from `Rel.of_agreeOutside`.  `Framed` adds that the frame lies
  within the stack.
* Two pieces of code that occur everywhere: the jump (`steps_jump`) and the two instructions that
  store a cell in a local variable (`steps_setVar`).

**Letters**, in this file and in the files on expressions, tests, calls and the simulation.
Numbers: W is the word size, F the number of local variables of a frame, N the largest number in the
pool, Q the number of stack cells, q a frame, pos a position in the code.  The temporaries are
written T₀, T₁, …, T_j; there are 2 F + 1 of them.
Facts: m, m₁, m₂, … are memories in the order in which they arise.  Z is a `Sizes`.  R says that a
memory represents a state (`Rel`), I the same with the frame inside the stack (`Framed`).  A says
that two memories agree outside a set of cells (`AgreeOutside`); A₂ speaks of m₂.  run is a run of
the machine (`Steps`).  val, va, vb say which number a cell holds.  hcode and names that end in Code
say where a piece of code is (`CodeAt`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The numbers that never change -/

/-- The word size is large enough for the limits: words hold 2 · word + 2 (so the difference of two
values, and one less, is in range), all addresses of the memory, all addresses of a stack of Q
cells, and all numbers 0, …, N of the pool. -/
structure Fits (W : ℕ) (lim : Limits) (N Q : ℕ) : Prop where
  word : 2 * (2 * lim.word + 2) < (2 : ℤ) ^ W
  space : 2 * (lim.space : ℤ) < (2 : ℤ) ^ W
  stack : 2 * (2 * (Q : ℤ)) < (2 : ℤ) ^ W
  pool_lt : 2 * (N : ℤ) < (2 : ℤ) ^ W






/-- The numbers on which the proofs about compiled code depend: the layout of the code, the limits
on the runs of the light program, and the number of stack cells.  The pool holds the numbers from 0
to the position of the dispatcher. -/
structure Sizes (W : ℕ) extends CodeLayout where
  /-- The limits on the runs of the light program. -/
  lim : Limits
  /-- The number of stack cells. -/
  Q : ℕ
  /-- The word size fits the limits, the pool and the stack. -/
  fits : Fits W lim disp Q
  /-- The pool holds the numbers up to 2 (F + 1), which are the offsets in a frame. -/
  offsets_le : 2 * (F + 1) ≤ disp

/-! ## Sets of cells -/

/-- What the evaluation of an expression into T_k may change: ADDR and the temporaries T_j with
k ≤ j ≤ 2 F. -/
def Temps (k F : ℕ) : Set ℤ := {a | a = cADDR ∨ ∃ j, k ≤ j ∧ j ≤ 2 * F ∧ a = cT j}

/-- The stack cells j with q ≤ j < Q. -/
def Stack (q Q : ℕ) : Set ℤ := {a | ∃ j, q ≤ j ∧ j < Q ∧ a = cStack j}

/-- The cells of the local variables of the outermost frame. -/
def MainFrame (F : ℕ) : Set ℤ := Stack mainFrame (mainFrame + F)

/-- The cells of the pool that hold the numbers 0, …, N. -/
def Pool (N : ℕ) : Set ℤ := {a | ∃ n, n ≤ N ∧ a = cPool n}

/-- The cells that the start-up code fills and no compiled statement changes: the registers for 1,
0, -1 and the pool. -/
def Constants (N : ℕ) : Set ℤ := {cONE, cZERO, cNEG} ∪ Pool N

/-- The cells that compiled code uses freely: the registers D, RET, RR, NFP, ADDR and the
temporaries. -/
def Scratch (F : ℕ) : Set ℤ := {cD, cRET, cRR, cNFP} ∪ Temps 0 F

/-- What the code of a statement that runs in the frame q may change: scratch cells, FP, the stack
cells from q on, and the memory cells within the limits. -/
def Writable {W : ℕ} (Z : Sizes W) (q : ℕ) : Set ℤ :=
  Scratch Z.F ∪ {cFP} ∪ Stack q Z.Q ∪ {a | 0 ≤ a ∧ a < Z.lim.space}

/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/















































variable {W : ℕ} {Z : Sizes W} {F : ℕ}




















/-! ## Addresses, and numbers that fit in a word -/































/-! ## The relation between a state of the light language and a memory of the machine -/

/-- The memory m of the machine represents the state σ of a procedure whose frame is at q. -/
structure Rel (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  one : m cONE = wd W 1
  zero : m cZERO = wd W 0
  neg : m cNEG = wd W (-1)
  pool : ∀ n ≤ Z.disp, m (cPool n) = wd W n
  fp : m cFP = wd W (cStack q)
  loc : ∀ x < Z.F, m (cStack (q + x)) = wd W (σ.loc x)
  mem : ∀ a < Z.lim.space, m (a : ℤ) = wd W (σ.mem a)

section Rel

variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}





























































end Rel

/-- The memory m represents the state σ in the frame q, and the frame lies within the stack: after
stack cell 0 and before stack cell Q. -/
structure Framed (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  rel : Rel Z σ q m
  low : 1 ≤ q
  high : q + Z.F ≤ Z.Q

/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}































end code

end Light.Compiler


