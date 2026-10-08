-- Prove2me | Definitions.Def_APSPSource_RemainingDefinitions
-- name    : APSPSource_RemainingDefinitions
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T08:52:00.13619+00:00
-- url     : https://prove2.me/theorems/a16e61f2-aa99-445d-b978-7015482793ae
-- title:
--   Algorithm and machine interfaces for the APSP reductions
-- statement:
--   This library specifies the concrete algorithms and machine interfaces used to reduce Exact Triangle, min-plus matrix multiplication, and all-pairs shortest paths to fast matrix-entry computations.
--
--   For integer matrices $X\in\mathbb Z^{n\times D}$ and $Y\in\mathbb Z^{D\times n}$, the basic query specification is
--
--   $$\operatorname{query}(I,J)=(XY)_{I,J}=\sum_{k=0}^{D-1}X_{I,k}Y_{k,J}.$$
--
--   The definitions describe band encodings, preprocessing tables, pruned recursive computations, and data structures for answering these queries. They give concrete array procedures, memory layouts, loop invariants, input bounds, and cost functions. Further constructions specify modular triangle counting, prime selection, witness searches, the Exact Triangle host, min-plus search, and APSP repeated squaring. Parameter records express the dimension, weight, word-size, and memory conditions under which each procedure is used.
--
--   The library also supplies structured-program execution predicates and their word-RAM compilation interfaces. With dispatcher position $d$, frame width $F$, and structured execution cost $c$, the defined machine-step budget is
--
--   $$T_{\mathrm{RAM}}=d+F+13+2dc.$$
--
--   State-representation and preservation predicates connect these programs to arrays in machine memory. Solver specifications require the appropriate output together with execution, resource, and running-time bounds. These definitions provide the common mathematical objects for the subsequent correctness and complexity proofs.
--
--   The constructions include auxiliary identities and existence witnesses used to form finite choices, encodings, layouts, and proof-bearing records. Each such witness is supplied by its source proof. The compiler simulation and final running-time conclusions are stated through their own proof obligations.
--
--   References:
--
--   1. [Structured execution and program specifications](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Rules.lean).
--   2. [Compilation resources and machine representation](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/WholeProgram.lean).
--   3. [Band encoding and wanted-entry computation](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Contracts.lean).
--   4. [Triangle-reduction procedures](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Host/Program.lean).
--   5. [Min-plus and APSP reduction programs](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Host.lean).
--   6. [Matrix-entry data structure and its contracts](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean).
--   7. [Parameter choices and the wanted-entry bound](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Corollary26.lean).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Rules.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Lang/Compiler/WholeProgram.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec2/Theorem5/Contracts.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Host/Program.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21b/Apsp/Host.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean; https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Corollary26.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Places
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Levels
import Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Tiling_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem21b_PathsAndWalks
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_ParameterSteps
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Table2_LogBounds
import Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Theorem30
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Alphabets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Arrays
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Counters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Layout
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_PrunedList
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_SortedSets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_SubsetTable
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Chunks
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Hashing
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Instances
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Parameters
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_ZOrder
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_AllPairs
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_BitSearch
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_FindNegativeTriangle
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_NegativeTriangle
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem21b_RepeatedSquaring
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Cubes
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineScan
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_Trie
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Scale
import Definitions.Def_APSPSource_ThreeSumApsp_Util_BinaryPrefixes
import Definitions.Def_APSPSource_ThreeSumApsp_Util_CountingSort
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Digits
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_APSPSource_ThreeSumApsp_Util_PrimesInWindow
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Weave
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Init
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Iterate
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.Common
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Rules


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Blocks -/

instance Cond.decidableHolds (σ : State) : (c : Cond) → Decidable (c.Holds σ)
  | .lt a b => inferInstanceAs (Decidable (a.val σ < b.val σ))
  | .eq a b => inferInstanceAs (Decidable (a.val σ = b.val σ))

/-- The state after a block (σ itself for a loop or a call, which are not blocks). -/
@[simp] def Stmt.after : Stmt → State → State
  | .set x e, σ => { σ with loc := Function.update σ.loc x (e.val σ) }
  | .store a e, σ => { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
  | .seq s t, σ => t.after (s.after σ)
  | .ite c s t, σ => if c.Holds σ then s.after σ else t.after σ
  | _, σ => σ

/-- A bound on the number of steps of a block: the longer side of each branch counts (0 for a loop
or a call). -/
@[simp] def Stmt.blockCost : Stmt → ℕ
  | .set _ e => e.cost + 1
  | .store a e => a.cost + e.cost + 1
  | .seq s t => s.blockCost + t.blockCost
  | .ite c s t => c.cost + 1 + max s.blockCost t.blockCost
  | _ => 0

/-- The statement is a block, and its run from σ stays within the limits. -/
@[simp] def Stmt.BlockSafe (lim : Limits) : Stmt → State → Prop
  | .skip, _ => True
  | .set _ e, σ => e.Safe lim σ
  | .store a e, σ => a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ)
  | .seq s t, σ => s.BlockSafe lim σ ∧ t.BlockSafe lim (s.after σ)
  | .ite c s t, σ =>
    c.Safe lim σ ∧ (c.Holds σ → s.BlockSafe lim σ) ∧ (¬ c.Holds σ → t.BlockSafe lim σ)
  | _, _ => False

/-- The block s, started in σ, stays within the limits and ends in a state that satisfies R. -/
abbrev Stmt.Runs (lim : Limits) (s : Stmt) (σ : State) (R : State → Prop) : Prop :=
  s.BlockSafe lim σ ∧ R (s.after σ)

/-! ## The default proofs -/



































/-! ## Rules for blocks -/















































/-! ## Sequencing: what is left of the time goes to the rest of the program -/















































































































/-! ## Loops whose body is a block -/














/-! ## Counting loops -/

/-- for i = 0, …, hi - 1 do body. -/
abbrev Stmt.for (i : ℕ) (hi : Expr) (body : Stmt) : Stmt :=
  (Light.Stmt.seq (.set i (k 0))
    (.while (Light.Cond.lt (v i) hi) (Light.Stmt.seq body (.set i ((Light.Expr.op Light.Op.add) (v i) (k 1))))))







































































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Calls


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Specifications of procedures -/

/-- Procedure number p of the program P, run at depth d on the arguments vals in the memory μ, ends
within T steps with a result r and a memory μ' that satisfy R r μ'. -/
def Meets (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ Ends lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem

section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}






























end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : State → Prop} {s : Stmt}











































end

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Conditions


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The compiler is correct on tests

The code of a test goes on to the next position if the test holds and jumps to a given position if
it does not, in at most as many steps as it has instructions, and it changes scratch cells only.
This behaviour is called `Decides`, and `decides_compileCond` proves it.

Both tests first evaluate a into T₀ and b into T₁ (`steps_pair`, which also serves the statement
that stores into the memory).  For a < b the code forms D = b - a - 1 and leaves if D < 0
(`decides_lt`).  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative (`decides_eq`).  No difference overflows, because words hold twice the largest value and
one more (`inRange_sub`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : Expr}

/-! ## Two expressions -/






















/-! ## Tests -/

/-- What the code of a test does, if it has size instructions, begins at pos, and tests p: in at
most size steps the machine reaches the position after the code if p holds, and the position l if
not.  Only scratch cells change. -/
def Decides (code : List Instr) (F pos size l : ℕ) (m : ℤ → BitVec W) (p : Prop) : Prop :=
  ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ AgreeOutside (Scratch F) m m' ∧
    (p → Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩) ∧ (¬ p → Steps code n ⟨pos, m⟩ ⟨l, m'⟩)

















































































end Light.Compiler

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_ProgramCode


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The code of a whole program

`compileProgram P p0 dec` is the program of the word RAM that runs procedure p0 of the light
program P.  With dec = false it accepts at the end of the run; with dec = true it accepts if the
result of the procedure is positive and rejects if not.  It has five parts:

| position | part |
|---|---|
| 0 | `headCode`: the numbers 1, 0, -1, and a jump to the start-up code |
| `mainPos` | `mainCode`: the outermost statement `mainStmt p0`, then the verdict (`tailCode`) |
| `firstBody` | `bodiesCode`: the bodies of the procedures, each with its return sequence |
| `dispPos` | the dispatcher for the positions below `dispPos` |
| `3 * dispPos` | `startCode`: the pool, the outermost frame, and a jump back to `mainPos` |

The start-up code comes last so that no position in the rest of the code depends on its length.

The number `frameSize` of local variables of every frame is read off the text of P: it is the width
of the text.  The pool holds the numbers up to `dispPos`: every position to return to, and with them
the smaller numbers that the code needs (`two_mul_frameSize_add_le_dispPos`).

The facts proved here are about positions only: each part is where the table says
(`codeAt_headCode`, …, `codeAt_startCode`), and every body is at its entry (`codeAt_bodies`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## The number read off the text -/

/-- The number of local variables of every frame: the width of the text, and at least 3 for the
outermost frame. -/
def frameSize (P : Program) : ℕ := max 3 (maxOf Stmt.width P)




/-- Every body fits into a frame. -/
theorem width_le_frameSize {P : Program} {b : Stmt} (hb : b ∈ P) : b.width ≤ frameSize P :=
  (maxOf_le_iff.1 le_rfl b hb).trans (le_max_right _ _)

/-! ## The parts of the code -/

/-- The outermost statement: procedure p0 is called on the local variables 1 and 2 of the outermost
frame, and its result goes to local variable 0. -/
def _root_.Light.mainStmt (p0 : ℕ) : Stmt := .call p0 [.var 1, .var 2] 0

/-- What follows the outermost statement, from position pos on: the result, which is local
variable 0 of the outermost frame, goes to the cell `cRESULT`; then the machine accepts, or, if dec
is set, it accepts if the result is positive and rejects if not. -/
def tailCode (dec : Bool) (pos : ℕ) : List Instr :=
  .add cRESULT (cStack mainFrame) cZERO ::
    (if dec then [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept]
      else [.accept])

/-- The position of the outermost statement: after the four instructions of `headCode`. -/
def mainPos : ℕ := 4

/-- The position of the code that follows the outermost statement. -/
def tailPos (F : ℕ) : ℕ := mainPos + (mainStmt 0).size F

/-- The position of the first body: after the outermost statement and what follows it. -/
def firstBody (F : ℕ) (dec : Bool) : ℕ := tailPos F + (tailCode dec 0).length

/-- The positions of the bodies, the first of them at pos.  A body is followed by the return
sequence. -/
def entries (F : ℕ) : List Stmt → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: entries F bs (pos + b.size F + epilogueSize)

/-- The position after the bodies, the first of them at pos. -/
def endPos (F : ℕ) : List Stmt → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => endPos F bs (pos + b.size F + epilogueSize)

/-- The position after the last body, which is the position of the dispatcher.  It is also the
largest number in the pool. -/
def dispPos (P : Program) (dec : Bool) : ℕ := endPos (frameSize P) P (firstBody (frameSize P) dec)

/-- What the code of the statements of P needs to know about the whole code. -/
def codeLayout (P : Program) (dec : Bool) : CodeLayout :=
  ⟨frameSize P, entries (frameSize P) P (firstBody (frameSize P) dec), dispPos P dec⟩

/-- The bodies with their return sequences, the first of them at pos. -/
def bodiesCode (G : CodeLayout) : List Stmt → ℕ → List Instr
  | [], _ => []
  | b :: bs, pos =>
    (compileStmt G b pos ++ epilogue G) ++ bodiesCode G bs (pos + b.size G.F + epilogueSize)

/-- The first three instructions: the numbers 1, 0, -1. -/
def headStraight : List Instr := [.one cONE, .sub cZERO cONE cONE, .sub cNEG cZERO cONE]

/-- The code that fills the pool with the numbers 0, …, N. -/
def poolCode (N : ℕ) : List Instr :=
  .sub (cPool 0) cONE cONE :: (List.range N).map fun n => .add (cPool (n + 1)) (cPool n) cONE

/-- The code that puts zeros into the local variables of the outermost frame. -/
def zeroCode (F : ℕ) : List Instr :=
  (List.range F).map fun x => .sub (cStack (mainFrame + x)) cONE cONE

/-- The code that sets up the outermost frame: FP, zeros in its local variables, and then the two
arguments in its local variables 1 and 2. -/
def frameCode (F : ℕ) : List Instr :=
  .sub cFP cZERO (cPool (2 * mainFrame)) ::
    (zeroCode F ++
      [.add (cStack (mainFrame + 1)) cARG1 cZERO, .add (cStack (mainFrame + 2)) cARG2 cZERO])

/-- The start-up code without its last jump. -/
def startStraight (F N : ℕ) : List Instr := poolCode N ++ frameCode F

/-- The first part: the numbers 1, 0, -1, and the jump to the start-up code. -/
def headCode (P : Program) (dec : Bool) : List Instr :=
  headStraight ++ [.bltz cNEG (3 * dispPos P dec)]

/-- The second part: the outermost statement and the verdict. -/
def mainCode (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  compileStmt (codeLayout P dec) (mainStmt p0) mainPos ++ tailCode dec (tailPos (frameSize P))

/-- The last part: the start-up code and the jump back to the outermost statement. -/
def startCode (P : Program) (dec : Bool) : List Instr :=
  startStraight (frameSize P) (dispPos P dec) ++ [.bltz cNEG mainPos]

/-- **The code of a program.**  With dec = false the machine accepts at the end of the run; with
dec = true it accepts if the result of procedure p0 is positive and rejects if not. -/
def _root_.Light.compileProgram (P : Program) (p0 : ℕ) (dec : Bool) : List Instr :=
  headCode P dec ++ mainCode P p0 dec ++ bodiesCode (codeLayout P dec) P
      (firstBody (frameSize P) dec) ++
    dispatcher (dispPos P dec) ++ startCode P dec

/-! ## Lengths and positions -/

 theorem le_endPos (F : ℕ) : ∀ (bs : List Stmt) (pos : ℕ), pos ≤ endPos F bs pos
  | [], _ => le_rfl
  | b :: bs, pos => le_trans (by omega) (le_endPos F bs (pos + b.size F + epilogueSize))

/-- The length of the outermost statement. -/
theorem size_mainStmt (p0 F : ℕ) : (mainStmt p0).size F = 2 * F + 11 := by
  simp +arith [mainStmt, Stmt.size, callSize, argsSize, Expr.size]




 theorem length_tailCode (dec : Bool) (pos : ℕ) :
    (tailCode dec pos).length = if dec then 5 else 2 := by
  cases dec <;> rfl

/-- The dispatcher comes after four instructions, the 2 F + 11 instructions of the outermost
statement and at least two for the verdict.  So the pool also holds the distance 2 (F + 1) between
two frames and the number 2 · `mainFrame` from which the start-up code forms the first frame
pointer, and it reaches further down than the 2 F + 1 temporaries. -/
theorem two_mul_frameSize_add_le_dispPos (P : Program) (dec : Bool) :
    2 * frameSize P + 17 ≤ dispPos P dec := by
  have : firstBody (frameSize P) dec ≤ dispPos P dec := le_endPos _ _ _
  have htail : 2 ≤ if dec then 5 else 2 := by split_ifs <;> omega
  simp only [firstBody, tailPos, mainPos, size_mainStmt, length_tailCode] at this
  omega

 theorem length_bodiesCode (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), pos + (bodiesCode G bs pos).length = endPos G.F bs pos
  | [], _ => rfl
  | b :: bs, pos => by
    have ih := length_bodiesCode G bs (pos + b.size G.F + epilogueSize)
    simp only [bodiesCode, endPos, List.length_append, length_compileStmt, length_epilogue]
    omega

section parts

variable (P : Program) (p0 : ℕ) (dec : Bool)

 theorem length_through_mainCode :
    (headCode P dec ++ mainCode P p0 dec).length = firstBody (frameSize P) dec := by
  simp only [headCode, headStraight, mainCode, List.length_append, length_compileStmt,
    size_mainStmt, length_tailCode, firstBody, tailPos, mainPos, codeLayout, List.length_cons,
    List.length_nil]
  omega

 theorem length_through_bodiesCode :
    (headCode P dec ++ mainCode P p0 dec ++
      bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)).length = dispPos P dec := by
  rw [List.length_append, length_through_mainCode]
  exact length_bodiesCode (codeLayout P dec) P _




























/-- The bodies begin at `firstBody`. -/
theorem codeAt_bodiesCode :
    CodeAt (compileProgram P p0 dec) (firstBody (frameSize P) dec)
      (bodiesCode (codeLayout P dec) P (firstBody (frameSize P) dec)) :=
  (codeAt_self _).left.left.right.cast_pos (by rw [length_through_mainCode, Nat.zero_add])

/-- The dispatcher is at `dispPos`. -/
theorem codeAt_dispatcher_dispPos :
    CodeAt (compileProgram P p0 dec) (dispPos P dec) (dispatcher (dispPos P dec)) :=
  (codeAt_self _).left.right.cast_pos (by rw [length_through_bodiesCode, Nat.zero_add])






end parts

/-- Every body is at its entry, followed by the return sequence, and ends at or before the position
after the bodies. -/
theorem codeAt_bodies {code : List Instr} (G : CodeLayout) :
    ∀ (bs : List Stmt) (pos : ℕ), CodeAt code pos (bodiesCode G bs pos) →
      ∀ (p : ℕ) (b : Stmt), bs[p]? = some b → ∃ e, (entries G.F bs pos)[p]? = some e ∧
        CodeAt code e (compileStmt G b e ++ epilogue G) ∧
        e + b.size G.F + epilogueSize ≤ endPos G.F bs pos
  | [], _, _, p, b, h => by simp at h
  | b₀ :: bs, pos, hc, 0, b, h => by
    obtain rfl : b₀ = b := by simpa using h
    exact ⟨pos, rfl, hc.left, le_endPos _ _ _⟩
  | b₀ :: bs, pos, hc, p + 1, b, h =>
    codeAt_bodies G bs _
      (hc.right.cast_pos (by
        rw [List.length_append, length_compileStmt, length_epilogue, Nat.add_assoc])) p b
      (by simpa using h)

end Light.Compiler

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Simulation


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The compiler is correct on statements: the simulation theorem

A run of a statement of the light language in c steps is matched by a run of its code in at most
stepsPerStep · c steps of the machine (`sim`).

What never changes (the program, its code, the numbers of `Sizes`, and the facts that the code is in
place and that a frame is wide enough for the text) forms the structure `Setting`.  The situation
before the code of a statement runs is `Start`: the code is at pos, and the memory represents the
state in the frame q, with room on the stack for the calls still allowed.  The situation afterwards
is `Finished`: the machine has reached the position after the code, the memory represents the new
state in the same frame, and only cells that the statement may write have changed.  `Simulates` says
that `Start` leads to `Finished`.

The theorem is an induction on the run, with one lemma for each rule of the semantics: `sim_skip`,
`sim_set`, `sim_store`, `sim_seq`, `sim_iteTrue`, `sim_iteFalse`, `sim_whileFalse`,
`sim_whileTrue`, `sim_call`.  Each of them first takes the code of the statement apart (`codeAt_ite`
and its like say where the parts are) and then runs the parts in turn.  A call has four parts.
Enter (`steps_callEnter`): arguments, new frame, position to return to, jump.  The body: the
induction hypothesis.  Leave (`steps_callLeave`): return sequence and dispatcher.  Store the result
in the caller's variable (`steps_setVar`).

In the proofs S is the setting and B the situation at the start; the other letters are as in the
file on the cells.
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr)

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt}
  {args : List Expr}













































end layout

/-! ## The setting -/

/-- What the simulation assumes once and for all: the numbers are large enough (`Sizes`), and the
program and its code fit them. -/
structure Setting (W : ℕ) extends Sizes W where
  /-- The light program. -/
  P : Program
  /-- The code of the whole program. -/
  code : List Instr
  /-- Every procedure body is at its entry, followed by the return sequence, all before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : Stmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    CodeAt code e (compileStmt toCodeLayout b e ++ epilogue toCodeLayout) ∧
    e + b.size F + epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : CodeAt code disp (dispatcher disp)
  /-- Every body has width at most F. -/
  width : ∀ b ∈ P, b.width ≤ F

/-- An upper bound for the number of machine steps that match one step of the light language, if the
code before the dispatcher has n instructions.  Each rule of the semantics counts at least one step
and, calls apart, runs a piece of code once, which takes at most n machine steps.  A call counts two
steps, so it has 2 stepsPerStep = 4 n: at most n for its own code, n for the return sequence, 2 n
for the dispatcher. -/
def stepsPerStep (n : ℕ) : ℕ := 2 * n























variable {W : ℕ} (S : Setting W)

/-- The situation before the code of the statement s runs, at nesting depth d of calls: the memory m
represents the state σ in the frame q, and the following holds. -/
structure Start (d : ℕ) (s : Stmt) (σ : State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends Framed S.toSizes σ q m where
  /-- The code of s is at pos. -/
  codeAt : CodeAt S.code pos (compileStmt S.toCodeLayout s pos)
  /-- It ends at or before the dispatcher. -/
  below : pos + s.size S.F ≤ S.disp
  /-- F local variables and 2 F + 1 temporaries are enough for s. -/
  width : s.width ≤ S.F
  /-- The state holds words. -/
  bounded : σ.Bounded S.lim
  /-- The stack has room for this frame and for F + 1 cells for each further level of calls. -/
  room : q + S.F + (S.F + 1) * (S.lim.depth - d) ≤ S.Q

/-- The code of s, started as in `Start`, has matched a run of c steps that ends in σ': it has
taken n machine steps and left the memory m'. -/
structure Finished (s : Stmt) (σ' : State) (c pos q : ℕ) (m m' : ℤ → BitVec W) (n : ℕ) : Prop where
  /-- The machine has reached the position after the code. -/
  run : Steps S.code n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩
  /-- It took at most stepsPerStep machine steps for each step of the language. -/
  le : n ≤ stepsPerStep S.disp * c
  /-- The memory represents σ' in the same frame. -/
  rel : Rel S.toSizes σ' q m'
  /-- Only cells that a statement in the frame q may write have changed. -/
  agree : AgreeOutside (Writable S.toSizes q) m m'

/-- The code of s matches the run of s from σ to σ' in c steps. -/
def Simulates (d : ℕ) (s : Stmt) (σ σ' : State) (c : ℕ) : Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W), Start S d s σ pos q m →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), Finished S s σ' c pos q m m' n

variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}






















/-! ## Statements without calls -/















































































































































/-! ## Calls -/

section call

variable {p x : ℕ} {args : List Expr}













































































































end call

/-! ## The theorem -/















end Light.Compiler

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StartUp


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The start-up code

A compiled program may start on any memory: nothing is assumed about the cells below -2.  Its first
three instructions and its start-up code write everything that the compiled statements rely on.
`startMem F N m` is the memory in which the outermost statement starts, if the run starts in m.

* `rel_startMem`: it represents the state in which the local variables 1 and 2 hold the two
  arguments (the contents of the cells -1 and -2) and all other local variables hold 0.
* `agreeOutside_startMem`: it differs from m only in the registers for 1, 0, -1, in the pool, in FP
  and in the outermost frame.
* `steps_start`: the machine gets from position 0 to the outermost statement in N + F + 9 steps.

The code has three pieces: the numbers 1, 0, -1 (`headStraight`), the pool (`poolCode`), the
outermost frame (`frameCode`).  There is no store among them, so the cells that a piece may change
are read off its text (`agreeOutside_effects`).  What a piece writes is found by running it: the two
loops unrolled in the code are inductions (`effects_poolCode`, `effects_zeroCode`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}

/-! ## The numbers 1, 0, -1 -/

















/-! ## The pool -/



































/-- The memory after the first three instructions and the code for the pool. -/
 def poolMem (N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (poolCode N) (effects headStraight m)


















/-! ## The outermost frame -/

































































/-! ## The memory in which the outermost statement starts -/

/-- The memory after the first three instructions and the start-up code. -/
def startMem (F N : ℕ) (m : ℤ → BitVec W) : ℤ → BitVec W :=
  effects (startStraight F N) (effects headStraight m)










































/-! ## The run from the first instruction to the outermost statement -/





























end Light.Compiler

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_WholeProgram


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The compiler is correct on whole programs

`compileProgram_correct`: if the call of procedure p0 of the light program P ends after c
steps, the compiled program gives its verdict within `ramSteps P dec c` = c₀ + K c steps, where c₀
and K depend on the text of P (and on dec) only.  If the memory of the machine held the memory of
the light program and the two arguments before (`Input`), it holds the final memory afterwards, with
the result in the cell -3 (`Outcome`).

The run of the machine has three parts.

1. The start-up code (`steps_start`) leads to a memory that represents the first state
   (`rel_startMem`).
2. The outermost statement is the call of p0.  The compiled program satisfies what the simulation
   theorem assumes (`setting`, `start_mainStmt`), so `sim` gives a run of at most K c steps to a
   memory that represents the last state.
3. The code that follows copies the result to the cell -3 and gives the verdict (`steps_tail`).

Each part comes with the set of cells that it may change.  The cells below `-lowCell` and the cells
from `lim.space` on are in none of the three sets (`not_mem_of_far`), and neither are the cells -1
and -2.

The notions of the compiler and of its proof are in the namespace `Light.Compiler`.  The statements
about programs name four of them, which are in `Light`: `compileProgram`, `mainStmt`, `verdictOf`,
`ramSteps`.  The passage to the notions of the word RAM also uses `compileProgram_correct` with
`Fits`, `Holds`, `Input` and `Outcome`, the cells `cARG1`, `cARG2`, `cRESULT`, and the numbers
`startCost`, `stepsPerStep`, `dispPos`, `frameSize`, `stackCells`, `lowCell`.
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light.Compiler

open EndStatement (Instr exec)

variable {W : ℕ}

/-! ## The verdict -/

/-- The verdict: accept, or, if dec is set, accept exactly if the result is positive. -/
def _root_.Light.verdictOf (dec : Bool) (r : ℤ) : Bool := !dec || decide (0 < r)

/-- What the code that follows the outermost statement leaves, if it starts in the memory m and the
result is r: the machine is about to give the verdict, the cell `cRESULT` holds the result, and only
that cell and the register D have changed. -/
 structure Verdict (code : List Instr) (dec : Bool) (r : ℤ) (m : ℤ → BitVec W)
    (cfg : Cfg W) : Prop where
  verdict : step code cfg = .inr (verdictOf dec r)
  result : cfg.mem cRESULT = wd W r
  agree : AgreeOutside {cRESULT, cD} m cfg.mem




































/-! ## Time and space of the compiled program -/

/-- A bound for the number of steps of the compiled program outside the outermost statement:
`dispPos` + `frameSize` + 9 before it (`steps_start`), at most three after it (`steps_tail`), and
the verdict. -/
def startCost (P : Program) (dec : Bool) : ℕ := dispPos P dec + frameSize P + 13

/-- A bound for the number of steps of the compiled program, for c steps of the light program. -/
def _root_.Light.ramSteps (P : Program) (dec : Bool) (c : ℕ) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) * c

/-- The number of cells of the stack that a run within the limits needs. -/
def stackCells (P : Program) (lim : Limits) : ℕ :=
  mainFrame + (frameSize P + 1) * (lim.depth + 1)

/-- A bound for the extent of the negative cells that the compiled program uses: the stack ends
before the cell -2 · stackCells, and the pool, which reaches further down than the temporaries, ends
at the cell -(25 + 4 · dispPos). -/
def lowCell (P : Program) (dec : Bool) (lim : Limits) : ℕ :=
  max (2 * stackCells P lim) (25 + 4 * dispPos P dec)







/-! ## The setting of the simulation theorem -/

section setting

variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}

/-- The compiled program, with its numbers, satisfies what the simulation theorem assumes once and
for all. -/
 def setting (P : Program) (p0 : ℕ) (dec : Bool)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) : Setting W where
  toCodeLayout := codeLayout P dec
  lim := lim
  Q := stackCells P lim
  fits := hfit
  offsets_le := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [codeLayout]
    omega
  P := P
  code := compileProgram P p0 dec
  bodyAt := codeAt_bodies (codeLayout P dec) P _ (codeAt_bodiesCode P p0 dec)
  dispatcherAt := codeAt_dispatcher_dispPos P p0 dec
  width _ hb := width_le_frameSize hb

variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))
































end setting

/-! ## The theorem -/

/-- The cells 0, 1, 2, … of the memory m of the machine hold the memory μ of the light language,
and μ holds words. -/
structure Holds (W : ℕ) (lim : Limits) (μ : ℕ → ℤ) (m : ℤ → BitVec W) : Prop where
  rep : ∀ a : ℕ, m (a : ℤ) = wd W (μ a)
  bounded : ∀ a, |μ a| ≤ lim.word

/-- What a run of a compiled program needs in the memory m: the memory μ of the light language, and
the arguments i and j, which are words, in their two cells. -/
structure Input (lim : Limits) (μ : ℕ → ℤ) (i j : ℤ) (m : ℤ → BitVec W) : Prop
    extends Holds W lim μ m where
  arg1 : m cARG1 = wd W i
  arg2 : m cARG2 = wd W j
  arg1_le : |i| ≤ lim.word
  arg2_le : |j| ≤ lim.word

/-- What a run of a compiled program from the memory m leaves in the memory m', if the light run
ends in σ'. -/
structure Outcome (lim : Limits) (P : Program) (dec : Bool) (m : ℤ → BitVec W) (σ' : State)
    (m' : ℤ → BitVec W) : Prop where
  /-- The cells 0, 1, 2, … hold the final memory. -/
  holds : Holds W lim σ'.mem m'
  /-- The cell for the result holds the result. -/
  result : (m' cRESULT).toInt = σ'.loc 0
  /-- The first argument is still there. -/
  arg1 : m' cARG1 = m cARG1
  /-- The second argument is still there. -/
  arg2 : m' cARG2 = m cARG2
  /-- The cells far below 0 and the cells from lim.space on are unchanged. -/
  far : ∀ a : ℤ, a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a → m' a = m a

















































end Light.Compiler

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Frames


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/

/-- The list of the locals after an assignment of z to local x.  A list that is too short is filled
up with zeros. -/
@[simp] def setLocal : List ℤ → ℕ → ℤ → List ℤ
  | [], 0, z => [z]
  | [], x + 1, z => 0 :: setLocal [] x z
  | _ :: l, 0, z => z :: l
  | a :: l, x + 1, z => a :: setLocal l x z





























/-! ## The value of an expression -/

/-- The evaluation of e in σ stays within the limits and gives z. -/
@[simp] def Expr.Gives (lim : Limits) (σ : State) (e : Expr) (z : ℤ) : Prop :=
  e.Safe lim σ ∧ e.val σ = z

/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}


















































































































end rules

/-! ## Locals by name, and locals whose values do not matter -/




































































section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

























/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}































/-! ## Counting loops with scratch variables -/













































end

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_Seg


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The list held by the n cells from address a. -/
def readSeg (μ : ℕ → ℤ) (a n : ℕ) : List ℤ := (List.range n).map fun i => μ (a + i)

variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

















/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]




































































































/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))





































/-- The cells from a on hold the matrix A, row by row. -/
def MatAt {n k : ℕ} (μ : ℕ → ℤ) (a : ℕ) (A : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), μ (a + i * k + j) = A i j

































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_ArrayAt


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Arrays in the memory

A routine assumes the same facts about each of its arrays: which list it holds, how long the list
is, and that it lies below some address `top`, from which on the routine writes: the free pointer,
the place of the result, the scratch space.  `ListAt μ a l N top` is the record of these three
facts, and `ArrayAt μ a l N U top` adds a bound `U` on the entries.  `IndexAt μ a l N p top` is the
record for a list of natural numbers below `p`.  What a routine assumes is then a record with one
field for each array.

* `ListAt.keep`, `ArrayAt.keep`: an array stays in place when its cells do not change.
* `ListAt.mono`, `ArrayAt.mono`: `top` and `U` may grow.
* `ListAt.read`, `ArrayAt.read`, `ArrayAt.abs_read_le`: what a cell holds, and how large it is.
* `ListAt.drop_take`, `ArrayAt.drop_take`: a piece of an array is an array.
* `IndexAt.keep`, `IndexAt.read`, `IndexAt.getD_lt`: the same for natural numbers.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}

/-- The list `l` stands at address `a`: it has `N` entries, and its cells lie below `top`. -/
structure ListAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  below : a + N ≤ top := by first
                              | omega
                              | ( (try have := Light.Std.space_le (by assumption))
                                  (try have := Light.Std.const_le (by assumption))
                                  simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

/-- The list `l` stands at address `a`: it has `N` entries, each of absolute value at most `U`, and
its cells lie below `top`. -/
structure ArrayAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) (N : ℕ) (U : ℤ) (top : ℕ) : Prop where
  len : l.length = N
  seg : Seg μ a l
  bound : AbsLe l U
  below : a + N ≤ top := by first
                              | omega
                              | ( (try have := Light.Std.space_le (by assumption))
                                  (try have := Light.Std.const_le (by assumption))
                                  simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

namespace ListAt






















end ListAt

namespace ArrayAt





























end ArrayAt

/-- The list `l` of natural numbers stands at address `a`: it has `N` entries, each below `p`, and
its cells lie below `top`. -/
structure IndexAt (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) (N p top : ℕ) : Prop where
  len : l.length = N
  seg : SegN μ a l
  lt : ∀ x ∈ l, x < p
  below : a + N ≤ top := by first
                              | omega
                              | ( (try have := Light.Std.space_le (by assumption))
                                  (try have := Light.Std.const_le (by assumption))
                                  simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

namespace IndexAt

variable {l : List ℕ} {p : ℕ}






















end IndexAt

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_Pass


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- for c < len: dst[c] := e.  The local c is the counter. -/
abbrev pass (c : ℕ) (len dst e : Expr) : Stmt := Stmt.for c len (.store (((Light.Expr.op Light.Op.add) dst (v c))) e)

variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}








































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_Copy


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## copy -/

namespace Copy

/-- The local variables of copy: the arguments src, dst and n, and the counter. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Idx : ℕ := 3

end Copy

open Copy in
/-- copy(src, dst, n): for i < n, dst[i] := src[i]. -/
def copyBody : Stmt := pass Idx (v Len) (v Dst) (M (((Light.Expr.op Light.Op.add) (v Src) (v Idx))))

/-- The time of copy. -/
@[simp] def copyTime (n : ℕ) : ℕ := 16 * n + 6















/-! ## fill -/

namespace Fill

/-- The local variables of fill: the arguments dst, n and x, and the counter. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Len : ℕ := 1
@[inherit_doc Dst] abbrev Val : ℕ := 2
@[inherit_doc Dst] abbrev Idx : ℕ := 3

end Fill

open Fill in
/-- fill(dst, n, x): for i < n, dst[i] := x. -/
def fillBody : Stmt := pass Idx (v Len) (v Dst) (v Val)

/-- The time of fill. -/
@[simp] def fillTime (n : ℕ) : ℕ := 13 * n + 6










end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_CountSort


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Counting sort of a list of items by a key that is read through the item

countSort(n, src, dst, key, stride, off, nb, cnt) sorts the n items at src stably by their keys and
writes them to dst.  The key of the item x is the number in the cell key + x · stride + off, a
natural number below nb.  cnt is a scratch area of nb + 1 cells, of arbitrary content on entry; on
exit cnt[t] is the number of items with a key below t, which is where bucket t starts.

The routine has five phases, each of them one loop:
* `csZero` sets the cells of cnt to 0 (`csZero_ends`);
* `csCount` counts the items with key t in cnt[t + 1] (`csCount_ends`);
* `csPrefix` adds up, so that cnt[t] is the start of bucket t (`csPrefix_ends`);
* `csPlace` writes each item to the next free place of its bucket, which it reads from cnt and moves
  on by one (`csPlace_ends`);
* `csShift` moves the contents of cnt up by one cell, so that cnt[t] is again the start of bucket t
  (`csShift_ends`).

Each phase has an invariant, a structure about the memory, with two lemmas: `start` says that it
holds before the first round, and `succ` says what a round does to the memory.  Three numbers
describe the memory, where kf j is the key of item number j: `cntLt kf t n` is the number of items
with a key below t, the start of bucket t; `cntEq kf t i` is the number of items before item number
i with key t; and `sortPos kf n j`, their sum at t = kf j and i = j, is the place of item number j.
What is assumed is `CountSort.Pre`, what is achieved is `CountSort.Post`, and the result is
`countSort_meets`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace CountSort

/-- The local variables of countSort: the arguments n (Len), src, dst, key (Keys), stride, off
(Offset), nb (Buckets), cnt; the counter of the loops (Idx); the address of a cell of cnt (Cell); a
place in dst (Place). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Dst : ℕ := 2
@[inherit_doc Len] abbrev Keys : ℕ := 3
@[inherit_doc Len] abbrev Stride : ℕ := 4
@[inherit_doc Len] abbrev Offset : ℕ := 5
@[inherit_doc Len] abbrev Buckets : ℕ := 6
@[inherit_doc Len] abbrev Cnt : ℕ := 7
@[inherit_doc Len] abbrev Idx : ℕ := 8
@[inherit_doc Len] abbrev Cell : ℕ := 9
@[inherit_doc Len] abbrev Place : ℕ := 10

end CountSort

open CountSort in
/-- The key of item number i, where i is the value of the counter:
mem[key + src[i] · stride + off]. -/
def csKey : Expr := M (((Light.Expr.op Light.Op.add)
                         ((Light.Expr.op Light.Op.add) (v Keys)
                           ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v Src) (v Idx))) (v Stride)))
                         (v Offset)))



open CountSort in
/-- cnt[t] := 0 for t ≤ nb. -/
def csZero : Stmt := .for Idx (((Light.Expr.op Light.Op.add) (v Buckets) (k 1))) (.store (((Light.Expr.op Light.Op.add) (v Cnt) (v Idx))) (k 0))

open CountSort in
/-- cnt[(key of item i) + 1] += 1 for i < n. -/
def csCount : Stmt :=
  .for Idx (v Len) ((Light.Stmt.seq (.set Cell ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Cnt) csKey) (k 1)))
                      (.store (v Cell) ((Light.Expr.op Light.Op.add) (M (v Cell)) (k 1)))))

open CountSort in
/-- cnt[t + 1] += cnt[t] for t < nb. -/
def csPrefix : Stmt :=
  .for Idx (v Buckets)
    (.store (((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Cnt) (v Idx)) (k 1))) (((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Cnt) (v Idx)) (k 1)))
                                       (M ((Light.Expr.op Light.Op.add) (v Cnt) (v Idx))))))

open CountSort in
/-- dst[cnt[key of item i]] := item i, cnt[key of item i] += 1, for i < n. -/
def csPlace : Stmt :=
  .for Idx (v Len) (
    (Light.Stmt.seq (.set Cell ((Light.Expr.op Light.Op.add) (v Cnt) csKey))
      (Light.Stmt.seq (.set Place (M (v Cell)))
        (Light.Stmt.seq
          (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Place)) (M ((Light.Expr.op Light.Op.add) (v Src) (v Idx))))
          (.store (v Cell) ((Light.Expr.op Light.Op.add) (v Place) (k 1)))))))

open CountSort in
/-- cnt[t] := cnt[t - 1] for t = nb, …, 1, and cnt[0] := 0. -/
def csShift : Stmt :=
  (Light.Stmt.seq (.set Idx (v Buckets))
    (Light.Stmt.seq
      (.while (Light.Cond.lt (k 0) (v Idx))
        (Light.Stmt.seq
          (.store ((Light.Expr.op Light.Op.add) (v Cnt) (v Idx))
            (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v Cnt) (v Idx)) (k 1))))
          (.set Idx ((Light.Expr.op Light.Op.sub) (v Idx) (k 1)))))
      (.store (v Cnt) (k 0))))

/-- countSort(n, src, dst, key, stride, off, nb, cnt). -/
def countSortBody : Stmt := (Light.Stmt.seq csZero (Light.Stmt.seq csCount (Light.Stmt.seq csPrefix (Light.Stmt.seq csPlace csShift))))

/-! ## What is assumed, and the state between the phases -/

namespace CountSort

/-- The arguments of countSort. -/
structure Args where
  /-- the number of items -/
  n : ℕ
  /-- where the items stand -/
  src : ℕ
  /-- where the sorted items go -/
  dst : ℕ
  /-- the key of the item x is in the cell key + x · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells of scratch space -/
  cnt : ℕ












end CountSort

open CountSort

























variable {μ μ' : ℕ → ℤ} {A : Args} {it kf : ℕ → ℕ} {σ : State}

























































/-! ## The first phase: the counters are set to 0 -/


























/-! ## The second phase: the sizes of the buckets -/











































/-! ## The third phase: the starts of the buckets -/









































/-! ## The fourth phase: the items go to their places -/





























































/-! ## The fifth phase: the contents of cnt move up by one cell -/









































































/-! ## The routine -/




















end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_Logs


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Logs

/-- The local variables of the routines: the argument, which the result replaces, the candidate,
and a power of two. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1


end Logs

open Logs

/-! ## The logarithm, rounded down -/















































/-! ## The logarithm, rounded up -/










































/-! ## The cube root, rounded up -/

/-- Some cube is at least n. -/
theorem exists_le_cube (n : ℕ) : ∃ s, n ≤ s ^ 3 := ⟨n, Nat.le_self_pow (by norm_num) n⟩

/-- The least s with s³ ≥ n. -/
def cbrtLeast (n : ℕ) : ℕ := Nat.find (exists_le_cube n)



















































/-- cbrtCeil(n): the candidate is s. -/
def cbrtCeilBody : Stmt :=
  (Light.Stmt.seq (.set Cand (k 0))
    (Light.Stmt.seq
      (.while
        (Light.Cond.lt ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (v Cand) (v Cand)) (v Cand)) (v Arg))
        (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1))))
      (.set Arg (v Cand))))

/-- The time of cbrtCeil. -/
@[simp] def cbrtCeilTime (n : ℕ) : ℕ := 12 * cbrtLeast n + 12

































/-! ## Halves, rounded up -/

































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_NextPair


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# From a pair to the next pair

A loop that runs through the pairs (a, b) with a, b < n in the order of their numbers t = a n + b
keeps a = t / n and b = t % n in two local variables, so that no division is needed.
`nextPair A B N` is the step from one pair to the next, and `Ends.nextPair` is its rule.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- b := b + 1; if b = n then b := 0; a := a + 1.  The locals A, B and N hold a, b and n. -/
def nextPair (A B N : ℕ) : Stmt :=
  (Light.Stmt.seq (.set B ((Light.Expr.op Light.Op.add) (v B) (k 1)))
    (.ite (Light.Cond.eq (v B) (v N)) (Light.Stmt.seq (.set B (k 0)) (.set A ((Light.Expr.op Light.Op.add) (v A) (k 1))))
      .skip))













































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_PowTable


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The pure model: the powers 1, b, …, b^(L-1). -/
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)







namespace PowTable

/-- The local variables of powTable: the arguments dst, L and b, the exponent j, and the power b^j.
-/
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Len : ℕ := 1
@[inherit_doc Dest] abbrev Base : ℕ := 2
@[inherit_doc Dest] abbrev Expo : ℕ := 3
@[inherit_doc Dest] abbrev Power : ℕ := 4

end PowTable

open PowTable

/-- One round: dst[j] := p; p := p * b. -/
def powTableRound : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Expo)) (v Power))
    (.set Power ((Light.Expr.op Light.Op.mul) (v Power) (v Base))))

/-- powTable(dst, L, b): p := 1; for j < L: dst[j] := p; p := p * b. -/
def powTableBody : Stmt :=
  (Light.Stmt.seq (.set Power (k 1)) (.for Expo (v Len) powTableRound))

/-- The time of powTable. -/
def powTableTime (L : ℕ) : ℕ := 17 * L + 8

/-- The state before round j: p = b^j, the first j cells hold the powers up to b^(j-1), and no cell
outside the L cells from dst has changed.  The list t holds the local variables after the five of
powTable. -/
def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst L
















































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_RadixPass


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# One pass of a radix sort on a list of indices

The pass sorts the list of indices at perm stably by a key that is read through the index: countSort
writes the sorted list into the w cells after the list, and copy brings it back.  What countSort
leaves is the result of a stable pass on lists (`exists_stablePass`), and `radixPass_ends` puts the
two calls together.  The pass is used with different expressions for the place of the keys, so these
are parameters.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}













namespace RadixPass

/-- The local variables that the pass uses: w, perm, and a local that takes the results of the two
calls, which are not used. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Perm : ℕ := 5
@[inherit_doc Num] abbrev Unused : ℕ := 7

/-- The pass: procedure pc is countSort, procedure pp is copy. -/
def _root_.Light.radixPass (pc pp : ℕ) (ekey estride eoff enb ecnt : Expr) : Stmt :=
  (Light.Stmt.seq
    (.call pc [v Num, v Perm, (Light.Expr.op Light.Op.add) (v Perm) (v Num), ekey, estride, eoff, enb, ecnt] Unused)
    (.call pp [(Light.Expr.op Light.Op.add) (v Perm) (v Num), v Perm, v Num] Unused))

/-- Where the data of a pass lie. -/
structure Args where
  /-- the number of indices -/
  w : ℕ
  /-- where the list of indices stands; the w cells after it are scratch space -/
  perm : ℕ
  /-- the key of the index i is in the cell key + i · stride + off -/
  key : ℕ
  /-- see key -/
  stride : ℕ
  /-- see key -/
  off : ℕ
  /-- all keys are below nb -/
  nb : ℕ
  /-- nb + 1 cells for the counters -/
  cnt : ℕ
  /-- only the R cells from perm on may change -/
  R : ℕ





end RadixPass
























variable {μ : ℕ → ℤ} {A : RadixPass.Args} {π : List ℕ} {kd : ℕ → ℕ}












































































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_Sieve


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The sieve of Eratosthenes

sieve(m, out, fr) writes the primes up to m in ascending order to the cells from out and returns
their number (`sieve_meets`).  It uses a table of m + 1 cells at the free pointer fr, about which
nothing is assumed.

* The table is cleared (`clear_ends`).
* The candidates i = 2, …, m are tried in turn (`round_ends`).  Before the round for i, cell fr + j
  holds 0 unless j is a proper multiple of a prime below i (`Sieved`, `Marked`); so i is a prime if
  and only if cell fr + i holds 0 (`prime_iff_not_marked`).
* A prime is appended to the list, and its proper multiples are marked (`take_ends`, `mark_ends`).

The number of steps, `sieveTime m`, is of the order m log m: a prime i costs m / i rounds of
marking, and the sum of m / i over all i ≤ m is at most m (⌊log₂ m⌋ + 1) (`sum_div_le`, `time_le`).

Everything but `sieveBody`, `sieveTime` and `sieve_meets` is in the namespace `Sieve`.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sieve

/-! ## The pure side -/

/-- The primes below c in ascending order. -/
def primesBelow (c : ℕ) : List ℕ := (List.range c).filter fun q => q.Prime



































/-- The number j is a proper multiple of a prime below c. -/
def Marked (c j : ℕ) : Prop := ∃ p, p.Prime ∧ p < c ∧ p ∣ j ∧ p < j












































































/-! ## The program -/

/-- The local variables of sieve: the arguments m, out and fr, the candidate i, a multiple J of i,
and the number cnt of primes found. -/
abbrev Bound : ℕ := 0
@[inherit_doc Bound] abbrev Dest : ℕ := 1
@[inherit_doc Bound] abbrev Table : ℕ := 2
@[inherit_doc Bound] abbrev Cand : ℕ := 3
@[inherit_doc Bound] abbrev Mult : ℕ := 4
@[inherit_doc Bound] abbrev Count : ℕ := 5

/-- Clearing the table: the cells fr, …, fr + m become 0. -/
def clear : Stmt :=
  (Light.Stmt.seq (.set Cand (k 0))
    (.while (Light.Cond.le (v Cand) (v Bound))
      (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Table) (v Cand)) (k 0))
        (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1))))))

/-- Marking the proper multiples 2 i, 3 i, … of i. -/
def mark : Stmt :=
  .while ((Light.Cond.le (v Mult) (v Bound))) (
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Table) (v Mult)) (k 1))
      (.set Mult ((Light.Expr.op Light.Op.add) (v Mult) (v Cand)))))

/-- The candidate i is a prime: it is appended to the list, and its proper multiples are marked. -/
def take : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Count)) (v Cand))
    (Light.Stmt.seq (.set Count ((Light.Expr.op Light.Op.add) (v Count) (k 1)))
      (Light.Stmt.seq (.set Mult ((Light.Expr.op Light.Op.add) (v Cand) (v Cand))) mark)))

/-- The round for the candidate i, which is a prime if its cell of the table holds 0. -/
def round : Stmt :=
  (Light.Stmt.seq (.ite (Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v Table) (v Cand))) (k 0)) take .skip)
    (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1))))

/-- sieve(m, out, fr). -/
def _root_.Light.sieveBody : Stmt :=
  (Light.Stmt.seq clear
    (Light.Stmt.seq (.set Cand (k 2))
      (Light.Stmt.seq (.set Count (k 0))
        (Light.Stmt.seq (.while (Light.Cond.le (v Cand) (v Bound)) round) (.set Bound (v Count))))))

/-- The time of sieve. -/
def _root_.Light.sieveTime (m : ℕ) : ℕ := 15 * m * (Nat.log 2 m + 5) + 35

variable {μ : ℕ → ℤ} {m out fr : ℕ}

/-- What sieve asks of the limits and of its arguments: an address fits in a word, and so does
2 m + 2; the m cells from out lie before the table; the table lies within the memory. -/
structure Pre (lim : Limits) (m out fr : ℕ) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  word : ((2 * m + 2 : ℕ) : ℤ) ≤ lim.word
  out : out + m ≤ fr
  free : fr + (m + 1) ≤ lim.space

/-- The number of steps of the main loop: 6 for each test, 15 (m / i) + 30 for the candidate i. -/
def loopTime (m : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (m - 1), (5 + 1 + (15 * (m / (r + 2)) + 30)) + (5 + 1)









/-- The first j cells of the table have been cleared, and no cell outside the table has changed. -/
def Cleared (μ : ℕ → ℤ) (m out fr j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [m, out, fr, j], μ'⟩ ∧ (∀ i < j, μ' (fr + i) = 0) ∧
    SameOutside μ μ' fr (m + 1)





























/-- The proper multiples of i below J have been marked, J is the next one, and no other cell has
changed. -/
def Marking (μ : ℕ → ℤ) (m out fr i cnt J : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [m, out, fr, i, J, cnt], μ'⟩ ∧
    (∀ j ≤ m, μ' (fr + j) = if i ∣ j ∧ i < j ∧ j < J then 1 else μ (fr + j)) ∧
    SameOutside μ μ' fr (m + 1)



















































/-- The candidate is i, and the numbers below c have been dealt with: the primes below c stand at
out, and their number is in the local Count; a cell of the table holds 0 unless its index is a
proper multiple of a prime below c; no cell outside the m cells from out and the table has
changed. -/
def Sieved (μ : ℕ → ℤ) (m out fr i c : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (J : ℕ), σ = ⟨frame [m, out, fr, i, J, (primesBelow c).length], μ'⟩ ∧
    SegN μ' out (primesBelow c) ∧ (∀ j ≤ m, μ' (fr + j) = 0 ↔ ¬ Marked c j) ∧
    SameOutside2 μ μ' out m fr (m + 1)

































































































end Sieve

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Lib_Sqrt


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Sqrt

/-- The local variables of sqrt: the argument K, which the result replaces, the candidate k, and the
square (k + 1)². -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Cand : ℕ := 1
@[inherit_doc Arg] abbrev Square : ℕ := 2

end Sqrt

open Sqrt in
/-- sqrt(K). -/
def sqrtBody : Stmt :=
  (Light.Stmt.seq (.set Cand (k 0))
    (Light.Stmt.seq (.set Square (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.le (v Square) (v Arg))
          (Light.Stmt.seq
            (.set Square
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v Square) ((Light.Expr.op Light.Op.mul) (k 2) (v Cand))) (k 3)))
            (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1)))))
        (.set Arg (v Cand)))))

/-- The time of sqrt. -/
@[simp] def sqrtTime (K : ℕ) : ℕ := 18 * Nat.sqrt K + 12

































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Tasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Problems, solvers, and the interpretation of "is solved in time T" in the light language

A *task* is a problem together with a calling convention: which arguments a procedure gets, what the
memory holds when it is called, and what the result and the memory have to be when it returns.
`Solves task P p T need` says that procedure number `p` of the program `P` solves the task within
`T` steps, if the limits of the run allow for `need`.  A reduction of the paper is a *host*: a
procedure that calls an arbitrary solver of another task.

Conventions.

* A solver gets sizes, a bound `U` on the absolute values of the numbers, the addresses of its
  arrays, and as last argument the free pointer `fr`.  All inputs and outputs lie below `fr`.  The
  solver may write its output segments and any cell from `fr` on, and no other cell.  Nothing is
  assumed about the cells from `fr` on, so a solver can be called again and again.
* A solver has to be correct for every valid bound `U` that it is given.
* A solver is a pair of a program and a procedure number.  What is proved about it holds for every
  program that begins with this program, so a host appends its own procedures.

A `Task` is a problem whose time and need depend on a size and a bound.  `TaskN` and `SolvesN` are
the same notions with a list of parameters.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Limits -/

/-- What a run needs: the largest absolute value it forms, the number of cells it uses from the free
pointer on, and the number of levels of calls below the procedure. -/
structure Need : Type where
  word : ℕ
  cells : ℕ
  depth : ℕ

/-- The limits allow for the need of a procedure that is called at depth `d` with the free pointer
`fr`.  An address always fits in a word. -/
structure Need.Ok (r : Need) (lim : Limits) (fr d : ℕ) : Prop where
  word : (r.word : ℤ) ≤ lim.word
  cells : fr + r.cells ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + r.depth ≤ lim.depth








/-- A need that depends on a size and a bound is polynomially bounded in the two: by
`2^s ((n + 1) (U + 1))^k`. -/
def PolyNeed (need : ℕ → ℕ → Need) : Prop :=
  ∃ s k : ℕ, ∀ n U : ℕ, (need n U).word ≤ polyBound s k [n, U] ∧ (need n U).cells ≤
    polyBound s k [n, U] ∧
    (need n U).depth ≤ polyBound s k [n, U]

/-! ## Specifications of single routines -/






/-! ## Tasks and solvers -/

/-- A problem with a calling convention. -/
structure Task : Type 1 where
  /-- The instances, as they lie in the memory: sizes, bound, addresses, contents. -/
  Inst : Type
  /-- The size of an instance. -/
  size : Inst → ℕ
  /-- The bound on the absolute values of its numbers that is handed to the solver. -/
  bound : Inst → ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right.  (That the cells below the free pointer are
  otherwise unchanged is part of this.) -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

/-- **Procedure `p` of the program `P` solves the task** within `T (size) (bound)` steps, whenever
the limits allow for `need (size) (bound)`; and so it does in every program that begins with `P`. -/
def Solves (task : Task) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.size x) (task.bound x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩
        (T (task.size x) (task.bound x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem



















/-- "The task is solved in time `T`", for a real-valued `T` whose second argument is an upper bound
on the numbers: some solver with a polynomially bounded need takes at most `T n u` steps on every
instance of size `n ≥ 1` with a bound `1 ≤ U ≤ u`. -/
def SolvedIn (task : Task) (T : ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → Need), PolyNeed need ∧
    Solves task P p Tn need ∧
    ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u








/-- The largest time `Tn n U` for a bound `U ≤ u`.  A program has a natural number as the bound on
its numbers, and a claim on running times a real number. -/
noncomputable def timeUpTo (Tn : ℕ → ℕ → ℕ) (n : ℕ) (u : ℝ) : ℝ :=
  ((Finset.range (⌊u⌋₊ + 1)).sup (Tn n) : ℕ)
























/-! ## Hosts -/

/-- A host from the task `lower` to the task `upper`: from every solver of `lower` it makes a solver
of `upper`, by appending procedures, whose time and need are given functions of those of the solver,
and whose need stays polynomially bounded. -/
def IsHost (lower upper : Task) (time : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ)
    (need : (ℕ → ℕ → Need) → ℕ → ℕ → Need) : Prop :=
  (∀ (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need), Solves lower P p T r →
    ∃ (R : Program) (p' : ℕ), Solves upper (P ++ R) p' (time T) (need r)) ∧
  ∀ r : ℕ → ℕ → Need, PolyNeed r → PolyNeed (need r)













/-! ## Tasks with a list of parameters -/

/-- A problem with a calling convention and a list of parameters. -/
structure TaskN : Type 1 where
  /-- The instances, as they lie in the memory. -/
  Inst : Type
  /-- The parameters on which time and need depend. -/
  pars : Inst → List ℕ
  /-- The arguments of the call, without the free pointer, which comes last. -/
  args : Inst → List ℤ
  /-- The instance is valid, and it lies in the memory below the free pointer. -/
  Pre : Inst → (ℕ → ℤ) → ℕ → Prop
  /-- The result and the final memory are right. -/
  Post : Inst → (ℕ → ℤ) → ℕ → ℤ → (ℕ → ℤ) → Prop

/-- Procedure `p` of the program `P` solves the task within `T pars` steps, whenever the limits
allow for `need pars`; and so it does in every program that begins with `P`. -/
def SolvesN (task : TaskN) (P : Program) (p : ℕ) (T : List ℕ → ℕ) (need : List ℕ → Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : Program) (lim : Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.pars x)).Ok lim fr d →
      Ends lim (P ++ R) d body ⟨frame (task.args x ++ [(fr : ℤ)]), μ⟩ (T (task.pars x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem



















/-- A need that is polynomially bounded in the parameters. -/
def PolyNeedN (need : List ℕ → Need) : Prop :=
  ∃ s k : ℕ, ∀ ps : List ℕ, (need ps).word ≤ polyBound s k ps ∧ (need ps).cells ≤ polyBound s k ps ∧
    (need ps).depth ≤ polyBound s k ps

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_PolyBounded


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Polynomially bounded needs

The need of a program is given by explicit expressions in the size n of the input and the bound U on
its numbers.  `PolyBounded F` says that F(n, U) is at most a polynomial in (n + 1)(U + 1).  It is
the calculus `ThreeSumApsp.Scale.SoftO` on the scale `polyScale`, and the tactic `growth_poly`
proves it by following the expression.

Three such functions make a polynomially bounded need (`PolyBounded.polyNeed`), and the need of a
solver that a host calls has three such parts (`PolyNeed.word`, `PolyNeed.cells`, `PolyNeed.depth`).
So the need of a host is polynomially bounded if the need of its solver is; the tactic `poly_need`
proves this from the definition of the need of the host.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

/-! ## Upper bounds that are polynomial in (n + 1)(U + 1) -/

/-- The scale of the polynomial bounds in a size `n` and a bound `U`: powers of `(n + 1)(U + 1)` are
not counted, and there is no other quantity. -/
noncomputable def polyScale : Scale (ℕ × ℕ) (Fin 0) where
  dom _ := True
  hidden p := ((p.1 + 1) * (p.2 + 1) : ℕ)
  base i := i.elim0
  one_le_hidden p _ := Nat.one_le_cast.2 (Nat.mul_pos p.1.succ_pos p.2.succ_pos)
  one_le_base i := i.elim0

/-- `F(n, U) ≤ K ((n + 1)(U + 1))^e` for some `K` and `e`. -/
abbrev PolyBounded (F : ℕ → ℕ → ℕ) : Prop := polyScale.SoftO (fun p => F p.1 p.2) ![]

namespace PolyBounded

variable {F : ℕ → ℕ → ℕ}

























end PolyBounded






namespace PolyBounded




















end PolyBounded

/-! ## The need of a solver that a host calls

A polynomially bounded need, at a size `A(n, U)` and a bound `B(n, U)` that are polynomially
bounded, has polynomially bounded parts. -/

namespace PolyNeed

variable {need : ℕ → ℕ → Need} {A B : ℕ × ℕ → ℕ} {a b : Fin 0 → ℕ}


























end PolyNeed








end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_Renumber


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The statement with n added to the number of every procedure that it calls. -/
def Stmt.shift (n : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift n) (t.shift n)
  | .ite c s t => .ite c (s.shift n) (t.shift n)
  | .while c s => .while c (s.shift n)
  | .call p args x => .call (p + n) args x

/-- The program P placed behind the program Q. -/
def Program.behind (Q P : Program) : Program := Q ++ P.map (Stmt.shift Q.length)




































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_RowMajor


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Reading the trusted layout

Matrices are written row by row (`rowMajor`), and an input is a concatenation of lists.  This file
says which number is in which cell (`getD_rowMajor`, `seg_memOf`, `matAt_of_seg`).
-/

public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam

 theorem rowMajor_succ {n m : ℕ} (A : Fin (n + 1) → Fin m → ℤ) :
    rowMajor A = (List.finRange m).map (A 0) ++ rowMajor fun i : Fin n => A i.succ := by
  simp [rowMajor, List.finRange_succ, List.flatMap_map]

theorem length_rowMajor : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ), (rowMajor A).length = n * m
  | 0, m, A => by simp [rowMajor]
  | n + 1, m, A => by
    rw [rowMajor_succ, List.length_append, length_rowMajor, List.length_map, List.length_finRange]
    ring

/-- The entry `(i, j)` of an `n × m` matrix is at place `i m + j`. -/
theorem getD_rowMajor : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m),
    (rowMajor A).getD ((i : ℕ) * m + (j : ℕ)) 0 = A i j
  | 0, _, _, i, _ => i.elim0
  | n + 1, m, A, i, j => by
    rw [rowMajor_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_append_right _ _ _ _ (by simp [Fin.val_succ, Nat.add_mul]; omega)]
      have : ((i'.succ : Fin (n + 1)) : ℕ) * m + (j : ℕ) - ((List.finRange m).map (A 0)).length =
          (i' : ℕ) * m + (j : ℕ) := by
        simp [Fin.val_succ, Nat.add_mul]
        omega
      rw [this]
      exact getD_rowMajor (fun i : Fin n => A i.succ) i' j

theorem mem_rowMajor {n m : ℕ} {A : Fin n → Fin m → ℤ} {x : ℤ} (h : x ∈ rowMajor A) :
    ∃ i j, A i j = x := by
  simp only [rowMajor, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at h
  exact h







/-- A cell in the first part of a concatenation. -/
theorem memOf_append_left {l₁ : List ℤ} (l₂ : List ℤ) {a : ℕ} (h : a < l₁.length) :
    memOf (l₁ ++ l₂) a = memOf l₁ a := by
  unfold memOf
  rw [List.getD_append _ _ _ _ h]

/-- A cell after the first part of a concatenation. -/
theorem memOf_append_right (l₁ l₂ : List ℤ) (a : ℕ) :
    memOf (l₁ ++ l₂) (l₁.length + a) = memOf l₂ a := by
  unfold memOf
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- A part of a concatenation is a segment of the memory. -/
theorem seg_memOf (l₁ l l₂ : List ℤ) : Seg (memOf (l₁ ++ l ++ l₂)) l₁.length l := by
  intro i hi
  rw [List.append_assoc, memOf_append_right, memOf_append_left _ hi]
  exact List.getD_eq_getElem _ _ hi

/-- The first of two lists after the size. -/
theorem seg_first (n : ℤ) (l₁ l₂ : List ℤ) : Seg (memOf (n :: (l₁ ++ l₂))) 1 l₁ := by
  simpa using seg_memOf [n] l₁ l₂

/-- The second of two lists after the size. -/
theorem seg_second (n : ℤ) (l₁ l₂ : List ℤ) :
    Seg (memOf (n :: (l₁ ++ l₂))) (1 + l₁.length) l₂ := by
  have := seg_memOf (n :: l₁) l₂ []
  simpa [Nat.add_comm] using this










/-- A square matrix written row by row: the two definitions agree. -/
theorem rowByRow_eq {n : ℕ} (w : Fin n → Fin n → ℤ) : EndStatement.rowByRow w = rowMajor w := by
  simp [EndStatement.rowByRow, rowMajor, List.ofFn_eq_map, List.flatMap_def]

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_ToMachine


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace EndStatement
end EndStatement
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# From runs of light programs to the running-time notions of the word RAM

`Solves` says what it means that a program of the word RAM solves a problem within a time bound, and
`IsDataStructure` that two programs form a data structure.  This file gives the corresponding
notions for light programs (`ProgramSolves`, `ProgramIsDataStructure`; what they ask on one instance
are the structures `ProgramSolvesAt` and `ProgramIsDataStructureAt`), which speak only about `Exec`,
and proves that the compiled programs satisfy the notions of the word RAM with time C · T + C, where
C depends on the compiled program only (`solves_of_programSolves`, `isDataStructure_of_program`).

1. **Word size.**  The limits of the run are polynomial in the parameters of the instance (`Small`),
   so they fit every admissible word size of slope `slopeOf` (`fits_of_small`).
2. **Time and space.**  c steps become at most C · c + C steps (`ramSteps_le`); calls nested d deep
   reach at most C · d + C cells below 0 (`lowCell_le`).
3. **Runs.**  Each run is one use of `compileProgram_correct`.  A solver is one run from the initial
   memory (`input_loadWords`).  A data structure is one such run for the preprocessing and then an
   induction on the list of queries, each of them one run (`serves_of_program`).
4. **From specifications.**  The runs that the two notions ask for come from specifications of the
   procedures (`Meets.main`, `AnswersQueries.of_meets`).
5. **The additive constant.**  If T ≥ 1, the bound C · (A · T) + C is at most C (A + 1) · T
   (`solves_of_programSolves_scaled`, `isDataStructure_of_program_scaled`).
-/

@[expose] public section

open ThreeSumApsp.WordRam

namespace Light

open ThreeSumApsp Compiler
open EndStatement (exec loadWords)

/-! ## The notion for light programs -/

/-- The limits are at most 2^s ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of the instance. -/
structure Small (s k : ℕ) (params : List ℕ) (lim : Limits) : Prop where
  nonneg : 0 ≤ lim.word
  word : lim.word ≤ (polyBound s k params : ℤ)
  space : lim.space ≤ polyBound s k params
  depth : lim.depth ≤ polyBound s k params

/-- What is asked of the run of procedure p0 on the instance x: within the limits lim it ends in the
state σ' after c steps. -/
structure ProgramSolvesAt (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (x : prob.Inst) (T : ℝ) (lim : Limits) (σ' : State) (c : ℕ) : Prop where
  /-- The run starts on the memory that holds the input of the problem. -/
  run : Exec lim P 0 (mainStmt p0) ⟨frame [0, 0, 0], memOf (prob.input x)⟩ σ' c
  /-- It ends within the time bound. -/
  time : (c : ℝ) ≤ T
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ prob.input x, |v| ≤ lim.word
  /-- The limits are polynomial in the parameters of the instance. -/
  small : Small s k (prob.params x) lim
  /-- The result gives the verdict, and the cells after the input hold the output. -/
  answer : prob.IsAnswer x (verdictOf dec (σ'.loc 0)) fun i => σ'.mem ((prob.input x).length + i)

/-- **A light program solves a problem.**  Procedure p0 of P, called on the memory that holds the
input of the problem, ends within T x steps and within limits that are polynomial in the
parameters; its result gives the verdict (if dec: accept exactly if the result is positive;
otherwise accept), and the cells after the input hold the output. -/
def ProgramSolves (prob : Problem) (P : Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : Limits) (σ' : State) (c : ℕ),
    ProgramSolvesAt prob P p0 dec s k x (T x) lim σ' c













/-! ## The word size -/

/-- A number that depends on the compiled program only: times the polynomial bound on the limits,
it exceeds all four numbers that have to fit in a word (`Fits`). -/
def textBound (P : Program) (dec : Bool) : ℕ := 32 + 8 * (frameSize P + 1) + 2 * dispPos P dec

/-- The number of binary digits of that number. -/
def textBoundBits (P : Program) (dec : Bool) : ℕ := Nat.size (textBound P dec)

/-- The slope of the word size for a compiled program: the exponents s and k of the bound
2^s ((p₁ + 1) ⋯ (p_r + 1))^k on the limits, and the bits for the numbers that the compiled code
itself forms (offsets in a frame, positions in the code). -/
def slopeOf (P : Program) (dec : Bool) (s k r : ℕ) : ℕ := textBoundBits P dec + s + k * r + k












































/-! ## Time and space -/

/-- The constant of the time and space bounds of a compiled program: the two constants of the time,
and the extent of the negative cells that are in use before any call. -/
def timeConst (P : Program) (dec : Bool) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) + lowCell P dec ⟨0, 0, 0⟩






















































/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}

















end run

/-! ## Solvers -/


















/-! ## The two-stage data structure -/








































































































/-! ## Absorbing the additive constant -/



































end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Lang_TopProcedure


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# From a solver of a task to a program for the layout of the end statement

A solver gets its size, the bound on the numbers and its addresses as arguments.  A problem of the
end statement has a fixed layout: cell 0 holds the size n, then comes the input, then the output;
the bound U = n^κ is not in the memory.  For every κ one more procedure, `topBody`, is appended to
the program of the solver.  It reads n.  At size 0 it answers at once.  Otherwise it forms U = n^κ
by κ multiplications and n², computes the addresses, calls the solver, and returns the result of
the solver (for a decision problem) or 1.

`Wrap` collects what has to be said about a problem and a task for this to work.  `Wrap.body_ends`
and `Wrap.body_ends_zero` follow the procedure through its text, `Wrap.small` bounds the word size,
the memory and the depth that the run needs by a polynomial in n, and `Wrap.realized` is the
conclusion: if the task is solved in time T, then the problem is solved on the word RAM within a
constant times T.
-/

@[expose] public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Local 2 is multiplied κ times by local 1. -/
def powStmt : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => (Light.Stmt.seq (powStmt κ) (.set 2 ((Light.Expr.op Light.Op.mul) (v 2) (v 1))))

/-- The outermost procedure.  Local 1 is n, the content of cell 0.  At size 0 the result is 0 for a
decision problem and 1 for a problem with an output.  Otherwise local 2 is U = n^κ, local 3 is n²,
and the arguments of the solver are expressions in these three; for a problem with an output the
result of the solver is replaced by 1. -/
def topBody (κ p : ℕ) (args : List Expr) (dec : Bool) : Stmt :=
  (Light.Stmt.seq (.set 1 (M (k 0)))
    (Stmt.iteNe (v 1) (k 0)
      (Light.Stmt.seq (.set 2 (k 1))
        (Light.Stmt.seq (powStmt κ)
          (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.mul) (v 1) (v 1)))
            (Light.Stmt.seq (.call p args 0) (if dec then .skip else .set 0 (k 1))))))
      (.set 0 (k (if dec then 0 else 1)))))






















/-- The arguments n, U and four addresses 1, 1 + n², 1 + 2n², 1 + c n² are safe. -/
theorem safe_fourAddresses {c : ℕ} (hc : c ≤ 4) {n : ℕ} {lim : Limits} {σ : State}
    (h3 : σ.loc 3 = ((n * n : ℕ) : ℤ)) (hw : ((8 * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ [v 1, v 2, k 1, ((Light.Expr.op Light.Op.add) (k 1) (v 3)), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 2) (v 3))), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k c) (v 3)))], e.Safe lim σ := by
  have hnn : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have hcn : (c : ℤ) * ((n : ℤ) * n) ≤ 4 * ((n : ℤ) * n) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hnn
  have hcn0 : (0 : ℤ) ≤ (c : ℤ) * ((n : ℤ) * n) := by positivity
  have hc' : (c : ℤ) ≤ 4 := by exact_mod_cast hc
  push_cast at hw h3
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  simp only [Expr.Safe, Expr.val, Op.eval, h3, true_and, Nat.cast_ofNat, Nat.cast_one]
  refine ⟨by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩,
    ⟨by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩, abs_le.2 ⟨by omega, by omega⟩⟩,
    by omega, ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩, abs_le.2 ⟨by omega, by omega⟩⟩

/-- The verdict that belongs to the result of a decision procedure. -/
theorem verdictOf_flag (p : Prop) : verdictOf true (ThreeSumApsp.flag p) = true ↔ p := by
  by_cases h : p
  · rw [ThreeSumApsp.flag_of h]
    simp [verdictOf, h]
  · rw [ThreeSumApsp.flag_of_not h]
    simp [verdictOf, h]

/-! ## The problems of `EndStatement` -/

section OfEnd

variable {Q : EndStatement.Problem} (x : Bounded Q)






















end OfEnd

/-! ## Polynomials in the size -/




















/-- What connects a problem in the layout of the end statement with a task. -/
structure Wrap (Q : EndStatement.Problem) (task : Task) (dec : Bool) where
  /-- The input and the output take at most cst (n² + 1) cells. -/
  cst : ℕ := 8
  cst_pos : 1 ≤ cst := by omega
  /-- The arguments of the solver, the free pointer last, as expressions in the locals 1 (n), 2 (U)
  and 3 (n²). -/
  args : List Expr
  /-- The instance of the task. -/
  inst : Bounded Q → task.Inst
  /-- The free pointer: the first cell after the output. -/
  fr : Bounded Q → ℕ
  size_eq : ∀ x : Bounded Q, task.size (inst x) = x.n
  bound_eq : ∀ x : Bounded Q, task.bound (inst x) = x.U
  fr_pos : ∀ x : Bounded Q, 1 ≤ fr x
  fr_le : ∀ x : Bounded Q, fr x ≤ cst * (x.n * x.n + 1)
  /-- The expressions have the values that the solver expects. -/
  vals : ∀ (x : Bounded Q) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → args.map (·.val σ) = task.args (inst x) ++ [(fr x : ℤ)]
  /-- They may be evaluated as soon as the addresses of the input and the output fit in a word. -/
  safe : ∀ (x : Bounded Q) (lim : Limits) (σ : State), σ.loc 1 = x.n → σ.loc 2 = x.U →
    σ.loc 3 = ((x.n * x.n : ℕ) : ℤ) → ((cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ e ∈ args, e.Safe lim σ
  /-- At size 0 it is right to reject, for a decision problem, and to accept, whatever the output
  cells hold, for a problem with an output. -/
  zero : ∀ x : Bounded Q, x.n = 0 → ∀ out, (ofEnd Q).IsAnswer x (!dec) out
  /-- The input meets the precondition of the task. -/
  pre : ∀ x : Bounded Q, 1 ≤ x.n → 1 ≤ x.U →
    task.Pre (inst x) (memOf ((ofEnd Q).input x)) (fr x)
  /-- What the task promises is a right answer. -/
  post : ∀ (x : Bounded Q) r μ', 1 ≤ x.n →
    task.Post (inst x) (memOf ((ofEnd Q).input x)) (fr x) r μ' →
    (ofEnd Q).IsAnswer x (verdictOf dec (if dec then r else 1)) fun i =>
      μ' (((ofEnd Q).input x).length + i)

namespace Wrap

variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}

/-- The steps of the outermost procedure, beside those of the solver. -/
def bodySteps (w : Wrap Q task dec) (κ : ℕ) : ℕ := 4 * κ + (w.args.map Expr.cost).sum + 20

/-- The steps of the outermost procedure and of its call, beside those of the solver. -/
def extra (w : Wrap Q task dec) (κ : ℕ) : ℕ := w.bodySteps κ + 4

/-- The limits of the run on an instance. -/
def limits (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) : Limits :=
  { word := ((need x.n x.U).word + (w.fr x + (need x.n x.U).cells) + w.cst * (x.n * x.n + 1) +
      x.U + x.n + 1 : ℕ)
    space := w.fr x + (need x.n x.U).cells
    depth := (need x.n x.U).depth + 2 }

/-- What the run asks of the limits. -/
structure Room (w : Wrap Q task dec) (need : ℕ → ℕ → Need) (x : Bounded Q) (lim : Limits) :
    Prop where
  /-- The addresses of the input and the output fit in a word. -/
  cells : ((w.cst * (x.n * x.n + 1) : ℕ) : ℤ) ≤ lim.word
  /-- The bound on the numbers, and 1, fit in a word. -/
  bound : ((x.U + 1 : ℕ) : ℤ) ≤ lim.word
  space : 1 ≤ lim.space
  depth : 2 ≤ lim.depth
  /-- The solver, called at depth 2 with the free pointer behind the output, has what it needs. -/
  solver : (need x.n x.U).Ok lim (w.fr x) 2







/-- The final state holds a right answer to the instance. -/
abbrev Answered (x : Bounded Q) (dec : Bool) (σ : State) : Prop :=
  (ofEnd Q).IsAnswer x (verdictOf dec (σ.loc 0)) fun i => σ.mem (((ofEnd Q).input x).length + i)











































































































































end Wrap

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Tasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The problems of the paper as tasks

* The problems for Section 3.4 have a size and a bound (`Task`).
* The problems of Theorem 5 and of Section 3.1 have the parameters `N`, `D`, `w` and `U` (`TaskN`).
  The calling convention is the same: sizes, the bound, the addresses of the arrays, the address of
  the output, and the free pointer last.  The three tasks: the wanted entries of a thin matrix
  product (`thinTask`; Theorem 5 and Corollary 26), #Lop-AE-SparseTri (`lopCountTask`;
  Definition 14) and Lop-AE-SparseTri (`lopDetectTask`; Definition 13).  All three have the same
  instances (`ThinInst`).
* What "solved in time `T`" means for them: `ThinSolvedIn`, `LopSolvedIn`.
-/

@[expose] public section

open ThreeSumApsp

namespace Light

open ThreeSumApsp.Spec

/-! ## The problems for Section 3.4 -/

/-- Three `n × n` matrices of weights in the memory. -/
structure TriInst : Type where
  n : ℕ
  U : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  AB : List ℤ
  BC : List ℤ
  AC : List ℤ

/-- The three matrices lie below the free pointer, and their entries are bounded by `U`. -/
structure TriInst.Pre (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenAB : x.AB.length = x.n * x.n
  lenBC : x.BC.length = x.n * x.n
  lenAC : x.AC.length = x.n * x.n
  segAB : Seg μ x.ab x.AB
  segBC : Seg μ x.bc x.BC
  segAC : Seg μ x.ac x.AC
  leAB : AbsLe x.AB x.U
  leBC : AbsLe x.BC x.U
  leAC : AbsLe x.AC x.U
  belowAB : x.ab + x.n * x.n ≤ fr
  belowBC : x.bc + x.n * x.n ≤ fr
  belowAC : x.ac + x.n * x.n ≤ fr















/-- Three matrices one after the other, with the free pointer behind them, are an instance. -/
theorem triPre_of_arrays {n U base : ℕ} {AB BC AC : List ℤ} {μ : ℕ → ℤ} (hn : 1 ≤ n) (hU : 1 ≤ U)
    (hAB : ArrayAt μ base AB (n * n) U (base + 3 * (n * n)))
    (hBC : ArrayAt μ (base + n * n) BC (n * n) U (base + 3 * (n * n)))
    (hAC : ArrayAt μ (base + 2 * (n * n)) AC (n * n) U (base + 3 * (n * n))) :
    (⟨n, U, base, base + n * n, base + 2 * (n * n), AB, BC, AC⟩ : TriInst).Pre μ
      (base + 3 * (n * n)) :=
  ⟨hn, hU, hAB.len, hBC.len, hAC.len, hAB.seg, hBC.seg, hAC.seg, hAB.bound, hBC.bound, hAC.bound,
    hAB.below, hBC.below, hAC.below⟩

/-- **Exact Triangle**: et(n, U, ab, bc, ac, fr) returns 1 if there is a zero triangle and 0 if not.
-/
noncomputable def etTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ Kept μ μ' fr

/-- **Negative Triangle**: nt(n, U, ab, bc, ac, fr) returns 1 if there is a negative triangle and 0
if not. -/
noncomputable def ntTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ μ' fr

/-- A list of `N` numbers in the memory. -/
structure VecInst : Type where
  N : ℕ
  U : ℕ
  a : ℕ
  X : List ℤ

/-- The list lies below the free pointer, and its entries are bounded by `U`. -/
structure VecInst.Pre (x : VecInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  U_pos : 1 ≤ x.U
  len : x.X.length = x.N
  seg : Seg μ x.a x.X
  le : AbsLe x.X x.U
  below : x.a + x.N ≤ fr

/-- **Convolution-3SUM**: c3(N, U, x, fr) returns 1 if `x_i + x_j = x_{i+j}` for some `i`, `j`, and
0 if not. -/
noncomputable def c3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- **3SUM**: s3(n, U, x, fr) returns 1 if three of the numbers, at different positions, sum to 0,
and 0 if not. -/
noncomputable def s3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ μ' fr

/-- Two `n × n` matrices in the memory, and the place for a third. -/
structure MatInst : Type where
  n : ℕ
  U : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  A : List ℤ
  B : List ℤ

/-- The two matrices and the place for the product lie below the free pointer; the place for the
product does not meet the two matrices. -/
structure MatInst.Pre (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenA : x.A.length = x.n * x.n
  lenB : x.B.length = x.n * x.n
  segA : Seg μ x.a x.A
  segB : Seg μ x.b x.B
  leA : AbsLe x.A x.U
  leB : AbsLe x.B x.U
  belowA : x.a + x.n * x.n ≤ fr
  belowB : x.b + x.n * x.n ≤ fr
  belowC : x.c + x.n * x.n ≤ fr
  apartA : Apart x.a (x.n * x.n) x.c (x.n * x.n)
  apartB : Apart x.b (x.n * x.n) x.c (x.n * x.n)

/-- **The (min,+)-product**: mp(n, U, a, b, c, fr) writes the product of the matrices at `a` and `b`
to `c`. -/
def mpTask : Task where
  Inst := MatInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.a, x.b, x.c]
  Pre := MatInst.Pre
  Post x μ fr _ μ' := Seg μ' x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ μ' fr x.c (x.n * x.n)

/-- A directed graph in the memory: adjacency matrix and weights, and the place for the `2n²` cells
of the answer. -/
structure GraphInst : Type where
  n : ℕ
  U : ℕ
  adj : ℕ
  w : ℕ
  out : ℕ
  ADJ : List ℤ
  W : List ℤ

/-- The graph and the place for the answer lie below the free pointer; the graph has no negative
cycle. -/
structure GraphInst.Pre (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenADJ : x.ADJ.length = x.n * x.n
  lenW : x.W.length = x.n * x.n
  segADJ : Seg μ x.adj x.ADJ
  segW : Seg μ x.w x.W
  zeroOne : ∀ e ∈ x.ADJ, e = 0 ∨ e = 1
  leW : AbsLe x.W x.U
  belowADJ : x.adj + x.n * x.n ≤ fr
  belowW : x.w + x.n * x.n ≤ fr
  belowOut : x.out + 2 * (x.n * x.n) ≤ fr
  apartADJ : Apart x.adj (x.n * x.n) x.out (2 * (x.n * x.n))
  apartW : Apart x.w (x.n * x.n) x.out (2 * (x.n * x.n))
  noNegativeCycle : NoNegativeCycle (graphOf x.n x.ADJ x.W)

/-- **APSP**: ap(n, U, adj, w, out, fr) writes two cells for each pair `(i, j)`, at
`out + 2 (i n + j)`: 1 and the distance from `i` to `j` if `j` can be reached from `i`, and 0 in the
first cell if not. -/
def apTask : Task where
  Inst := GraphInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.adj, x.w, x.out]
  Pre := GraphInst.Pre
  Post x μ fr _ μ' :=
    (∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
    ∀ i j : Fin x.n,
      (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z) ∧
    KeptBut μ μ' fr x.out (2 * (x.n * x.n))

/-! ## The thin matrix product and the lopsided triangle problems -/

/-- Matrices `X` (`N × D`) and `Y` (`D × N`), row by row, `w` wanted positions (rows in `WI`,
columns in `WJ`), and the place for `w` answers. -/
structure ThinInst : Type where
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ
  /-- The number of columns of `X` and of rows of `Y`. -/
  D : ℕ
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The address of `X`. -/
  x : ℕ
  /-- The address of `Y`. -/
  y : ℕ
  /-- The address of `WI`. -/
  wi : ℕ
  /-- The address of `WJ`. -/
  wj : ℕ
  /-- The address of the answers. -/
  out : ℕ
  /-- The first matrix, row by row. -/
  X : List ℤ
  /-- The second matrix, row by row. -/
  Y : List ℤ
  /-- The rows of the wanted positions. -/
  WI : List ℕ
  /-- The columns of the wanted positions. -/
  WJ : List ℕ

/-- Everything lies below the free pointer, the entries are bounded by `U`, the positions are
distinct positions of an `N × N` matrix, and the place for the answers meets none of the inputs. -/
structure ThinInst.Pre (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  D_pos : 1 ≤ x.D
  U_pos : 1 ≤ x.U
  lenX : x.X.length = x.N * x.D
  lenY : x.Y.length = x.D * x.N
  lenWI : x.WI.length = x.w
  lenWJ : x.WJ.length = x.w
  segX : Seg μ x.x x.X
  segY : Seg μ x.y x.Y
  segWI : SegN μ x.wi x.WI
  segWJ : SegN μ x.wj x.WJ
  leX : AbsLe x.X x.U
  leY : AbsLe x.Y x.U
  ltWI : ∀ i ∈ x.WI, i < x.N
  ltWJ : ∀ j ∈ x.WJ, j < x.N
  nodup : (x.WI.zip x.WJ).Nodup
  belowX : x.x + x.N * x.D ≤ fr
  belowY : x.y + x.D * x.N ≤ fr
  belowWI : x.wi + x.w ≤ fr
  belowWJ : x.wj + x.w ≤ fr
  belowOut : x.out + x.w ≤ fr
  apartX : Apart x.out x.w x.x (x.N * x.D)
  apartY : Apart x.out x.w x.y (x.D * x.N)
  apartWI : Apart x.out x.w x.wi x.w
  apartWJ : Apart x.out x.w x.wj x.w

/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg

/-- N. -/
abbrev Rows : ℕ := 0
/-- D. -/
abbrev Cols : ℕ := 1
/-- The number w of wanted positions. -/
abbrev Wanted : ℕ := 2
/-- The bound U on the entries. -/
abbrev Bound : ℕ := 3
/-- The address of X. -/
abbrev AdrX : ℕ := 4
/-- The address of Y. -/
abbrev AdrY : ℕ := 5
/-- The address of the rows of the wanted positions. -/
abbrev AdrWI : ℕ := 6
/-- The address of their columns. -/
abbrev AdrWJ : ℕ := 7
/-- The address of the output. -/
abbrev AdrOut : ℕ := 8
/-- The free pointer. -/
abbrev Free : ℕ := 9

end ThinArg

/-- The entries of both matrices are 0 or 1. -/
def ThinInst.ZeroOne (x : ThinInst) : Prop := (∀ v ∈ x.X, v = 0 ∨ v = 1) ∧ ∀ v ∈ x.Y, v = 0 ∨ v = 1

/-- The entry `(XY)[I, J]`. -/
def thinEntry (N D : ℕ) (X Y : List ℤ) (I J : ℕ) : ℤ :=
  ((List.range D).map fun k => X.getD (I * D + k) 0 * Y.getD (k * N + J) 0).sum

/-- The wanted entries, in the order of the positions. -/
def thinOut (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) : List ℤ :=
  (WI.zip WJ).map fun q => thinEntry N D X Y q.1 q.2

/-- **The wanted entries of a thin matrix product** (Theorem 5, Corollary 26):
`thin(N, D, w, U, x, y, wi, wj, out, fr)`. -/
def thinTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w, x.U]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre := ThinInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **#Lop-AE-SparseTri** (Definition 14), the graph given by its two biadjacency matrices: the same
call with `U = 1` on matrices of zeros and ones; the answers are the numbers of common
neighbours. -/
def lopCountTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w

/-- **Lop-AE-SparseTri** (Definition 13): the answer is 1 if the pair has a common neighbour and 0
if not. -/
def lopDetectTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' :=
    Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).map fun v => if v = 0 then 0 else 1) ∧
      KeptBut μ μ' fr x.out x.w

/-- "The thin matrix product is solved in time `T N D w' u`", where `w'` is an upper bound on the
number `w` of wanted positions and `u` one on the bound `U`. -/
def ThinSolvedIn (T : ℕ → ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN thinTask P p Tn need ∧
    ∀ (N D w w' U : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → 1 ≤ U → w ≤ w' → (U : ℝ) ≤ u →
      (Tn [N, D, w, U] : ℝ) ≤ T N D w' u

/-- "The task (one of the two lopsided triangle problems) is solved in time `T n D w'`", where `w'`
is an upper bound on the number `w` of query pairs. -/
def LopSolvedIn (task : TaskN) (T : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN task P p Tn need ∧
    ∀ (n D w w' : ℕ), 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w'

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_LightModel


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# "Is solved in time T", read as a statement about programs of the light language

The light language (`Light.Stmt`, `Light.Program`) is a small language with assignments to numbered
locals, loads and stores, `if`, `while` and calls of numbered procedures; a compiler turns its
programs into programs of the word RAM.

The deductions between running-time claims are made for an arbitrary reading `M : DetTimeModel` of
the sentence "is solved by a deterministic algorithm in time T".  Here the sentence is read as: some
procedure of some program of the light language solves the task within that many steps, and its need
(`Light.Need`: the largest number that it forms, the cells that it uses, the depth of its calls) is
polynomially bounded.
-/

@[expose] public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The reading of "is solved in time T" by programs of the light language. -/
noncomputable def lightModel : DetTimeModel where
  thinProduct := ThinSolvedIn
  lopCount := LopSolvedIn lopCountTask
  lopDetect := LopSolvedIn lopDetectTask
  exactTriangle := SolvedIn etTask
  negativeTriangle := SolvedIn ntTask
  convolution3SUM := SolvedIn c3Task
  threeSum := SolvedIn s3Task
  minPlusProduct := SolvedIn mpTask
  apsp := SolvedIn apTask

end Light

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Instance


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5: an instance of the task, in the terms of Section 2

An instance of the thin matrix product is given by lists in the memory. This file reads them as the
matrices X and Y and the set W of Section 2, and has the facts that link the two descriptions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp
































/-- The row of the wanted position number i. -/
def thinI (x : ThinInst) (i : ℕ) : ℕ := x.WI.getD i 0

/-- The column of the wanted position number i. -/
def thinJ (x : ThinInst) (i : ℕ) : ℕ := x.WJ.getD i 0

variable {x : ThinInst} {m : ℕ} {μ : ℕ → ℤ} {fr : ℕ}































section positions

variable {i : ℕ}






































end positions












































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_AllInstances_BruteForce


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The wanted entries of a thin matrix product, as inner products

X is an N × D matrix at the address x and Y a D × N matrix at y, both row by row, with entries of
absolute value at most U; the cells from wi and from wj on hold the rows and the columns of w wanted
positions.  thinBrute(N, D, w, U, x, y, wi, wj, out, fr) computes every wanted entry (XY)[I, J] as
the inner product of row I of X and column J of Y, and writes it to the cells from out on.  It is
right on every instance for which D U² fits in a word, so that no partial sum overflows; it is what
the solver of Theorem 5 falls back to outside the regime of the theorem.  At most
40 (w + 1) (D + 1) steps.

bruteInner_spec treats the inner product: after t rounds the sum holds the first t terms
(brutePartial), which stay within a word (abs_brutePartial_le).  bruteRound_spec treats one wanted
position, and thinBrute_spec the loop over the positions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

/-- Local 10 of thinBrute: the number of the position. -/
abbrev Pos : ℕ := 10
/-- Local 11 of thinBrute: the index t of the inner product. -/
abbrev Idx : ℕ := 11
/-- Local 12 of thinBrute: the address of X[I, t]. -/
abbrev CellX : ℕ := 12
/-- Local 13 of thinBrute: the address of Y[t, J]. -/
abbrev CellY : ℕ := 13
/-- Local 14 of thinBrute: the sum. -/
abbrev Sum : ℕ := 14

end Brute

open ThinArg Brute

/-- The inner product. -/
def bruteInner : Stmt :=
  .while ((Light.Cond.lt (v Idx) (v Cols))) (
    (Light.Stmt.seq
      (.set Sum ((Light.Expr.op Light.Op.add) (v Sum) ((Light.Expr.op Light.Op.mul) (M (v CellX)) (M (v CellY)))))
      (Light.Stmt.seq (.set CellX ((Light.Expr.op Light.Op.add) (v CellX) (k 1)))
        (Light.Stmt.seq (.set CellY ((Light.Expr.op Light.Op.add) (v CellY) (v Rows)))
          (.set Idx ((Light.Expr.op Light.Op.add) (v Idx) (k 1)))))))

/-- One wanted position: the inner product, the store, and the step to the next position. -/
def bruteRound : Stmt :=
  (Light.Stmt.seq (.set Idx (k 0))
    (Light.Stmt.seq
      (.set CellX
        ((Light.Expr.op Light.Op.add) (v AdrX)
          ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v AdrWI) (v Pos))) (v Cols))))
      (Light.Stmt.seq
        (.set CellY ((Light.Expr.op Light.Op.add) (v AdrY) (M ((Light.Expr.op Light.Op.add) (v AdrWJ) (v Pos)))))
        (Light.Stmt.seq (.set Sum (k 0))
          (Light.Stmt.seq bruteInner
            (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v AdrOut) (v Pos)) (v Sum))
              (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 1)))))))))

/-- thinBrute(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBruteBody : Stmt :=
  .while ((Light.Cond.lt (v Pos) (v Wanted))) bruteRound

/-- The locals of thinBrute: the arguments, the number i of the position, the index t, the two
addresses px and py, and the sum s.  In the place of U stands whatever number u has been passed: the
program never reads it. -/
def bruteLocs (x : ThinInst) (u : ℤ) (fr i t px py : ℕ) (s : ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ),
    (fr : ℤ), (i : ℤ), (t : ℤ), (px : ℤ), (py : ℤ), s]

/-! ## The partial sums -/

/-- The first n terms of the inner product. -/
def brutePartial (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) : ℤ :=
  ((List.range n).map fun t => X.getD (I * D + t) 0 * Y.getD (t * N + J) 0).sum




























/-! ## The program -/














































/-- Before position i: the locals are as in bruteLocs, with anything in the scratch locals, the
entries of the positions before i are in the output, and nothing else has changed. -/
def BruteInv (x : ThinInst) (μ : ℕ → ℤ) (u : ℤ) (fr i : ℕ) (σ : State) : Prop :=
  ∃ (t px py : ℕ) (s : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (bruteLocs x u fr i t px py s), μ'⟩
    ∧ (∀ j < i, μ' (x.out + j) = thinEntry x.N x.D x.X x.Y (thinI x j) (thinJ x j))
    ∧ SameOutside μ μ' x.out x.w
















































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_AllInstances_RegimeTest


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The regime of Theorem 5

"Let D ≥ 4 be a power of four and N ≥ D^18 … a set W of at most N²/√D positions".  The procedure
regime(N, D, w), where w is the number of positions in W, tests whether the sizes of an instance are
in this regime.  It returns the exponent m with D = 4^m if they are, and 0 if they are not.  With
√D = 2^m, the condition on W reads w 2^m ≤ N².

The program has these parts, each with its own lemma.  regimeExp multiplies by four until D is
reached, which gives the only candidate m = ⌈log₄ D⌉ together with 4^m and 2^m = √D.  regimePow
compares D^18 with N by at most eighteen multiplications, none of which exceeds N D (but for the
first product, which is D).  regimeTests combines the four tests, the last two of which are
regimeSizes.  That the candidate is the only one is RegimeAnswer.zero.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}












/-! ## The local variables -/

namespace RegimeLocal

/-- The argument N. -/
abbrev Rows : ℕ := 0
/-- The argument D. -/
abbrev Cols : ℕ := 1
/-- The argument w. -/
abbrev Wanted : ℕ := 2
/-- The power 4^m. -/
abbrev PowFour : ℕ := 3
/-- The power 2^m. -/
abbrev PowTwo : ℕ := 4
/-- The exponent m. -/
abbrev Expo : ℕ := 5
/-- The result. -/
abbrev Result : ℕ := 6
/-- A power of D. -/
abbrev Power : ℕ := 7
/-- The exponent of that power. -/
abbrev Count : ℕ := 8
/-- 1 as long as no power of D has exceeded N, then 0. -/
abbrev Fits : ℕ := 9

end RegimeLocal

open RegimeLocal

/-! ## The text -/

/-- The search for the exponent m, with 4^m and 2^m. -/
def regimeExp : Stmt :=
  .while ((Light.Cond.lt (v PowFour) (v Cols))) (
    (Light.Stmt.seq (.set PowFour ((Light.Expr.op Light.Op.mul) (v PowFour) (k 4)))
      (Light.Stmt.seq (.set PowTwo ((Light.Expr.op Light.Op.mul) (v PowTwo) (k 2)))
        (.set Expo ((Light.Expr.op Light.Op.add) (v Expo) (k 1))))))

/-- One round of regimePow: if the next power of D exceeds N, give up; if not, go on to it. -/
def regimePowRound : Stmt :=
  .ite ((Light.Cond.lt (v Rows) ((Light.Expr.op Light.Op.mul) (v Power) (v Cols))))
    ((Light.Stmt.seq (.set Fits (k 0)) (.set Count (k 18))))
    ((Light.Stmt.seq (.set Power ((Light.Expr.op Light.Op.mul) (v Power) (v Cols)))
       (.set Count ((Light.Expr.op Light.Op.add) (v Count) (k 1)))))

/-- The test D^18 ≤ N: the power of D is at most N unless it is D^0. -/
def regimePow : Stmt :=
  (Light.Stmt.seq (.set Power (k 1))
    (Light.Stmt.seq (.set Count (k 0))
      (Light.Stmt.seq (.set Fits (k 1)) (.while (Light.Cond.lt (v Count) (k 18)) regimePowRound))))

/-- The last two tests, after regimePow: D^18 ≤ N and w 2^m ≤ N².  If both hold, the result becomes
m. -/
def regimeSizes : Stmt :=
  .ite ((Light.Cond.eq (v Fits) (k 1)))
    (.ite ((Light.Cond.lt ((Light.Expr.op Light.Op.mul) (v Rows) (v Rows)) ((Light.Expr.op Light.Op.mul) (v Wanted) (v PowTwo)))) .skip (.set Result (v Expo)))
    .skip

/-- The four tests: 4^m = D, m ≥ 1, D^18 ≤ N and w 2^m ≤ N².  If all hold, the result becomes m. -/
def regimeTests : Stmt :=
  .ite ((Light.Cond.eq (v PowFour) (v Cols)))
    (.ite ((Light.Cond.lt (k 0) (v Expo))) ((Light.Stmt.seq regimePow regimeSizes)) .skip)
    .skip

/-- regime(N, D, w). -/
def regimeBody : Stmt :=
  (Light.Stmt.seq (.set PowFour (k 1))
    (Light.Stmt.seq (.set PowTwo (k 1))
      (Light.Stmt.seq (.set Expo (k 0))
        (Light.Stmt.seq regimeExp
          (Light.Stmt.seq (.set Result (k 0)) (Light.Stmt.seq regimeTests (.set Rows (v Result))))))))




/-! ## What the procedure returns -/










/-! ## The exponent -/


























/-! ## The eighteenth power -/

/-- The states of the loop of regimePow.  The memory and the locals below 7 are as at the start.
Either the loop is still counting: local 8 is an exponent j ≤ 18, local 7 is D^j, which is at most N
unless j = 0, and local 9 is 1.  Or it has stopped because a power exceeded N: local 8 is 18 and
local 9 is 0. -/
def PowInv (N D : ℕ) (loc μ : ℕ → ℤ) (σ : State) : Prop :=
  σ.mem = μ ∧ (∀ x < 7, σ.loc x = loc x) ∧
    ((∃ j : ℕ, j ≤ 18 ∧ σ.loc 8 = j ∧ σ.loc 9 = 1 ∧ σ.loc 7 = ((D ^ j : ℕ) : ℤ) ∧
        (j = 0 ∨ D ^ j ≤ N)) ∨
      (σ.loc 8 = 18 ∧ σ.loc 9 = 0 ∧ N < D ^ 18))

















































































/-! ## The four tests -/














































































/-! ## The whole procedure -/




























end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Contracts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5 in the light language: the map

One file that fixes everything on which two routines have to agree, besides the sizes and the places
of the arrays: the numbers of the procedures, and for every procedure its arguments, what it needs,
what it leaves behind, which cells it may change, and the shape of its running time. A routine is
proved against its own entry; a caller assumes the entries of the routines it calls. So the proof of
a routine does not depend on the proofs of the routines that it calls.

* Routines never contain an address.  They receive scalars and base addresses as arguments.  Only
  the two main routines (Theorem 5 here, the data structure of Section 4) know the places.
* The stages up to the encodings of all bands are shared with Section 4: procedure pShared fills the
  shared block, which starts at an address b0 above the input and the output of the program that
  calls it (the free pointer).
* An entry XSpec lim P c says: in the program P, within the limits lim, procedure number pX does its
  job within c times the shape of its running time (Meets).  The theorem on a routine proves its
  entry for every c from the constant of the routine on, so a caller can assume several entries at
  one constant.
* The entries of encStep, encodeBands, countSort, copy, runTiles and report stand with these
  routines.
* Strings are numbers: a string over an alphabet of b symbols is its code in base b, level 1 most
  significant (namespace Spec).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Vocabulary -/

/-- The cells from a on hold a list of bits, as 1 and 0. -/
def SegB (μ : ℕ → ℤ) (a : ℕ) (l : List Bool) : Prop :=
  Seg μ a (l.map fun b : Bool => if b then (1 : ℤ) else 0)






/-! ## The numbers of the procedures

Number 0 is empty.  1 to 25: the shared routines and those of Theorem 5.  26 to 28: the test of the
regime, the brute force, and the solver for all instances.  29 to 39 are not used.  From 40 on:
Section 4. -/

/-- The number of shared. -/
def pShared : ℕ := 1
/-- The number of pow. -/
def pPow : ℕ := 2
/-- The number of binom. -/
def pBinom : ℕ := 3
/-- The number of sqrt. -/
def pSqrt : ℕ := 4
/-- The number of subsets. -/
def pSubsets : ℕ := 5
/-- The number of counters. -/
def pCounters : ℕ := 6
/-- The number of digits. -/
def pDigits : ℕ := 7
/-- The number of coef. -/
def pCoef : ℕ := 8
/-- The number of bandArray. -/
def pBandArray : ℕ := 9
/-- The number of encStep. -/
def pEncStep : ℕ := 10
/-- The number of encode. -/
def pEncode : ℕ := 11
/-- The number of encodeBands. -/
def pEncodeBands : ℕ := 12
/-- The number of wanted. -/
def pWanted : ℕ := 13
/-- The number of countSort. -/
def pCountSort : ℕ := 14
/-- The number of sortWanted. -/
def pSortWanted : ℕ := 15
/-- The number of segBounds. -/
def pSegBounds : ℕ := 16
/-- The number of union. -/
def pUnion : ℕ := 17
/-- The number of pick. -/
def pPick : ℕ := 18
/-- The number of pruned. -/
def pPruned : ℕ := 19
/-- The number of runTiles. -/
def pRunTiles : ℕ := 20
/-- The number of report. -/
def pReport : ℕ := 21
/-- The number of fill. -/
def pFill : ℕ := 22
/-- The number of copy. -/
def pCopy : ℕ := 23
/-- The number of gather. -/
def pGather : ℕ := 24
/-- The number of the solver of Theorem 5. -/
def pThm5 : ℕ := 25
/-- The number of the test of the regime. -/
def pRegime : ℕ := 26
/-- The number of the brute force. -/
def pThinBrute : ℕ := 27



/-! ## The entries of the shared routines -/

section Entries

variable (lim : Limits) (P : Program) (c : ℕ)

/-- pow(b, n, dst): writes b^0, …, b^n to dst. -/
def PowSpec : Prop :=
  ∀ (b n dst : ℕ) (μ : ℕ → ℤ),
    1 ≤ dst → dst + (n + 1) ≤ lim.space → 1 ≤ b →
    ((b ^ (n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, n, dst] μ (c * (n + 1)) fun _ μ' =>
      Seg μ' dst (powList b (n + 1)) ∧ SameOutside μ μ' dst (n + 1)

/-- binom(L, m, pas): returns binom(L, m), by Pascal's triangle in the L + 2 cells from pas. -/
def BinomSpec : Prop :=
  ∀ (L m pas : ℕ) (μ : ℕ → ℤ),
    pas + (L + 2) ≤ lim.space → m ≤ L → ((2 ^ L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pBinom d [L, m, pas] μ (c * (L + 1) ^ 2) fun r μ' =>
      r = (L.choose m : ℕ) ∧ SameOutside μ μ' pas (L + 2)

/-- sqrt(K): returns ⌊√K⌋, by counting up.  Changes no cell. -/
def SqrtSpec : Prop :=
  ∀ (K : ℕ) (μ : ℕ → ℤ),
    ((4 * K + 4 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pSqrt d [K] μ (c * (Nat.sqrt K + 1)) fun r μ' =>
      r = (Nat.sqrt K : ℕ) ∧ μ' = μ

/-- subsets(L, m, KK, mask): writes the first KK subsets of size m of the L levels, as rows of L
bits, in the order of Spec.unrank. -/
def SubsetsSpec : Prop :=
  ∀ (L m KK mask : ℕ) (μ : ℕ → ℤ),
    mask + KK * L ≤ lim.space → m ≤ L → KK ≤ L.choose m →
    ((KK + L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pSubsets d [L, m, KK, mask] μ (c * ((KK + 1) * (L + 1))) fun _ μ' =>
      (∀ s < KK, SegB μ' (mask + s * L) (Spec.unrank L m s)) ∧ SameOutside μ μ' mask (KK * L)

/-- counters(N, K0, N0, band): for every row I < N writes its band I / (K0 N0) to band + I and its
block I / N0 % K0 to band + N + I, by counting. -/
def CountersSpec : Prop :=
  ∀ (N K0 N0 band : ℕ) (μ : ℕ → ℤ),
    band + 2 * N ≤ lim.space → 0 < K0 → 0 < N0 →
    ((K0 + N0 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pCounters d [N, K0, N0, band] μ (c * (N + 1)) fun _ μ' =>
      (∀ I < N, μ' (band + I) = (I / (K0 * N0) : ℕ) ∧ μ' (band + N + I) = (I / N0 % K0 : ℕ))
      ∧ SameOutside μ μ' band (2 * N)

/-- digits(n, b, len, dst): for every x < n writes the len digits of x % b^len in base b, most
significant first, to dst + x len, by an odometer. -/
def DigitsSpec : Prop :=
  ∀ (n b len dst : ℕ) (μ : ℕ → ℤ),
    dst + n * len ≤ lim.space → 2 ≤ b → (b : ℤ) ≤ lim.word →
    (n : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pDigits d [n, b, len, dst] μ (c * ((n + 1) * (len + 1))) fun _ μ' =>
      (∀ x < n, SegN μ' (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len)))
      ∧ SameOutside μ μ' dst (n * len)

/-- coef(phi): writes the 70 coefficients φ_λ(s) to phi and the 70 coefficients ψ_λ(t) to phi + 70.
-/
def CoefSpec : Prop :=
  ∀ (phi : ℕ) (μ : ℕ → ℤ),
    phi + 140 ≤ lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pCoef d [phi] μ c fun _ μ' =>
      Seg μ' phi Spec.phiFlat ∧ Seg μ' (phi + 70) Spec.psiFlat
      ∧ SameOutside μ μ' phi 140

/-- What bandArray reads, apart from the matrix: the table of subsets and the two tables of digits,
all below the array it writes. -/
structure BandTables (p : Par) (μ : ℕ → ℤ) (mask dig3 dig4 arr : ℕ) : Prop where
  hmask : ∀ s < p.KK, SegB μ (mask + s * p.L) (Spec.unrank p.L p.m s)
  hdig3 : ∀ I < p.N, SegN μ (dig3 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  hdig4 : ∀ x < p.D, SegN μ (dig4 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)
  mask_le : mask + p.KK * p.L ≤ arr
  dig3_le : dig3 + p.N * p.Lo ≤ arr
  dig4_le : dig4 + p.D * p.m ≤ arr

/-- The shape of the running time of bandArray: clear 7^L cells, then one entry in O(L) steps for
each subset of the table, each row of a block and each column. -/
def bandArrayShape (p : Par) : ℕ := p.S7 + (p.KK * p.N0 * p.D + 1) * (p.L + 1)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr), for the left
side: side = 0, aA the address of X, sI = D, sK = 1 (sI and sK are the strides of the index I of the
band and of the inner index k: the entry is at aA + I sI + k sK).  Writes the input array of the row
band β (Section 2.3.4), in the order of the codes, to arr. -/
def BandArrayLSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aX mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aX X → aX + p.N * p.D ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 0, aX, p.D, 1, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β)) ∧ SameOutside μ μ' arr p.S7

/-- The same procedure for the right side: side = 1, aA the address of Y, sI = 1, sK = N. Writes the
input array of the column band β. -/
def BandArrayRSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aY mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aY Y → aY + p.D * p.N ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 1, aY, 1, p.N, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β)) ∧ SameOutside μ μ' arr p.S7

/-- Where encode finds its tables and its areas: the tables lie below dst, the 10^n cells of dst
below src, the 7^n cells of src below scr, and scr has 7^n cells. -/
structure EncodePlaces (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) : Prop where
  n_le : n ≤ Lmax
  hp7 : Seg μ p7 (powList 7 (Lmax + 1))
  hp10 : Seg μ p10 (powList 10 (Lmax + 1))
  tab_le : tab + 70 ≤ dst
  p7_le : p7 + (Lmax + 1) ≤ dst
  p10_le : p10 + (Lmax + 1) ≤ dst
  dst_le : dst + 10 ^ n ≤ src
  src_le : src + 7 ^ n ≤ scr
  scr_le : scr + 7 ^ n ≤ lim.space

/-- encode(n, src, dst, scr, tab, p7, p10), the procedure of Section 2.4.1, recursive as
printed, with the coefficients φ: from the array a at src it computes the encoding of a at dst. -/
def EncodeLSpec : Prop :=
  ∀ (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) (a : LeftStr n → ℤ) (V : ℤ),
    EncodePlaces lim n Lmax src dst scr tab p7 p10 μ →
    Seg μ tab Spec.phiFlat → Seg μ src (Spec.arrL a) → (∀ u, |a u| ≤ V) →
    7 ^ (n + 1) * V ≤ lim.word →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pEncode d [n, src, dst, scr, tab, p7, p10] μ (c * 10 ^ n) fun _ μ' =>
      Seg μ' dst (Spec.arrT (encodingL a)) ∧ SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n)

/-- The same procedure with the coefficients ψ. -/
def EncodeRSpec : Prop :=
  ∀ (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) (b : RightStr n → ℤ) (V : ℤ),
    EncodePlaces lim n Lmax src dst scr tab p7 p10 μ →
    Seg μ tab Spec.psiFlat → Seg μ src (Spec.arrR b) → (∀ v, |b v| ≤ V) →
    7 ^ (n + 1) * V ≤ lim.word →
    ∀ d, d + (n + 1) ≤ lim.depth →
    Meets lim P pEncode d [n, src, dst, scr, tab, p7, p10] μ (c * 10 ^ n) fun _ μ' =>
      Seg μ' dst (Spec.arrT (encodingR b)) ∧ SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n)

/-! ## The shared stage -/

/-- The tables of the powers of 3, 4, 7 and 10 in the shared block. -/
structure PowTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  p3 : Seg μ (p.aP3 b0) (powList 3 (p.L + 1))
  p4 : Seg μ (p.aP4 b0) (powList 4 (p.L + 1))
  p7 : Seg μ (p.aP7 b0) (powList 7 (p.L + 1))
  p10 : Seg μ (p.aP10 b0) (powList 10 (p.L + 1))

/-- The other tables of the shared block: the coefficients, the subsets, the band and the block of
every row, and the digits of the offsets and of the inner indices. -/
structure RowTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  phi : Seg μ (p.aPHI b0) Spec.phiFlat
  psi : Seg μ (p.aPSI b0) Spec.psiFlat
  mask : ∀ s < p.KK, SegB μ (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s)
  band : ∀ I < p.N, μ (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
  block : ∀ I < p.N, μ (p.aBLOCK b0 + I) = (I / p.N0 % p.K0 : ℕ)
  dig3 : ∀ I < p.N, SegN μ (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  dig4 : ∀ x < p.D, SegN μ (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)

/-- The tables of the shared block, all in one memory. -/
structure SharedTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop
  extends PowTables p b0 μ, RowTables p b0 μ

/-- What the shared stage leaves behind: the tables, the directory, and the encodings of all bands.
(Cell 31 of the directory is not used by it.) -/
structure SharedReady (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop
  extends SharedTables p b0 μ where
  dir : SegN μ (p.aDIR b0) (dirList p aX aY b0)
  encA : ∀ β < p.nB, Seg μ (p.aENCA b0 + β * p.T)
    (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))
  encB : ∀ β < p.nB, Seg μ (p.aENCB b0 + β * p.T)
    (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))

/-- The shape of the running time of the shared stage. -/
def sharedShape (p : Par) : ℕ :=
  (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1)
    + p.nB * (p.T + bandArrayShape p)

/-- What the shared stage assumes: the shared block fits in the memory, X and Y stand below it, V
bounds their entries, and the encoded numbers and the powers of ten fit in a word. -/
structure SharedPre (p : Par) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ) (μ : ℕ → ℤ) : Prop where
  space : p.sharedEnd b0 ≤ lim.space
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  belowX : aX + p.N * p.D ≤ b0
  belowY : aY + p.D * p.N ≤ b0
  absX : ∀ i j, |X i j| ≤ V
  absY : ∀ i j, |Y i j| ≤ V
  seven : 7 ^ (p.L + 1) * V ≤ lim.word
  ten : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word

/-- shared(L, m, N, D, aX, aY, b0): fills the shared block. -/
def SharedSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    SharedPre lim p aX aY b0 X Y V μ →
    ∀ d, d + (p.L + 3) ≤ lim.depth →
    Meets lim P pShared d [p.L, p.m, p.N, p.D, aX, aY, b0] μ (c * sharedShape p) fun _ μ' =>
      SharedReady p hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (p.sharedEnd b0 - b0)

/-! ## Theorem 5 -/

/-- What wanted reads, apart from the positions: all of it lies below the area it writes. -/
structure WantedTables (p : Par) (μ : ℕ → ℤ) (band dig3 mask tid : ℕ) : Prop where
  hband : ∀ I < p.N, μ (band + I) = (I / (p.K0 * p.N0) : ℕ)
  hblock : ∀ I < p.N, μ (band + p.N + I) = (I / p.N0 % p.K0 : ℕ)
  hdig3 : ∀ I < p.N, SegN μ (dig3 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  hmask : ∀ s < p.KK, SegB μ (mask + s * p.L) (Spec.unrank p.L p.m s)
  band_le : band + 2 * p.N ≤ tid
  dig3_le : dig3 + p.N * p.Lo ≤ tid
  mask_le : mask + p.KK * p.L ≤ tid

/-- What wanted assumes. -/
structure Wanted.WantedPre (p : Par) (w aWI aWJ band dig3 mask tid : ℕ) (I J : ℕ → ℕ)
    (μ : ℕ → ℤ) : Prop where
  hmL : p.m ≤ p.L
  tab : WantedTables p μ band dig3 mask tid
  hI : ∀ i < w, μ (aWI + i) = I i ∧ I i < p.N
  hJ : ∀ i < w, μ (aWJ + i) = J i ∧ J i < p.N
  hpow : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word
  hnB : (((p.nB + 1) * (p.nB + 1) : ℕ) : ℤ) ≤ lim.word
  room : tid + (2 * w + w * p.L) ≤ lim.space := by first
                                                     | omega
                                                     | ( (try have := Light.Std.space_le (by assumption))
                                                         (try have := Light.Std.const_le (by assumption))
                                                         simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  hWI : aWI + w ≤ tid := by first
                              | omega
                              | ( (try have := Light.Std.space_le (by assumption))
                                  (try have := Light.Std.const_le (by assumption))
                                  simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  hWJ : aWJ + w ≤ tid := by first
                              | omega
                              | ( (try have := Light.Std.space_le (by assumption))
                                  (try have := Light.Std.const_le (by assumption))
                                  simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
















namespace SortWanted

/-- The arguments of sortWanted. -/
structure Args where
  /-- the number of positions -/
  w : ℕ
  /-- the number of digits of a code -/
  L : ℕ
  /-- the number of tiles -/
  nT : ℕ
  /-- where the numbers of the tiles stand -/
  tid : ℕ
  /-- where the digits of the codes stand -/
  dgt : ℕ
  /-- where the sorted list goes -/
  perm : ℕ







end SortWanted

































































/-- The arguments of pick but for the mode, with the data behind them: the list small stands at
pSub, the list big at pU, the list values at pVal, and pDst is the destination. -/
structure PickArgs : Type where
  (pSub pU pVal pDst : ℕ)
  (small big : List ℕ) (values : List ℤ)










































/-- The arguments of pruned but for the number n of levels that are left, with the data behind them.
The two encodings are the lists EA at aEA and EB at aEB, and the parts of them below the current
vertex begin at the position base.  The list codes stands at l, the values are written to out, the
stack begins at sp, and the powers of ten up to 10^Lmax stand at p10.  A and B bound the numbers in
the two encodings. -/
structure PrunedArgs : Type where
  (aEA aEB base l out sp p10 : ℕ)
  (Lmax : ℕ) (EA EB : List ℤ) (codes : List ℕ) (A B : ℤ)

























































end Entries

end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_AllInstances_Solver


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The thin matrix product, on all instances

The task thinTask: given an N × D matrix X and a D × N matrix Y with entries of absolute value at
most U, and w positions (rows at wi, columns at wj), write the entries of XY at these positions to
the cells from out on. Theorem 5 is about instances with D ≥ 4 a power of four, N ≥ D^18
and at most N²/√D wanted positions. A solver that other procedures call has to be right on every
instance. thin(N, D, w, U, x, y, wi, wj, out, fr) tests the regime, calls the solver of Theorem 5 in
the regime and the brute force outside it.

The file proves that thin solves the task thinTask (thin_solves), within a need that is polynomial
in the parameters (thinNeed_poly) and covers what the solver of Theorem 5 asks of the limits
(thin_limits5, "Word size" in Section 2.4.4), and within the time of Theorem 5 in the regime
(thin_shape_le, thinTimeBound_le). Together these are the running-time claim "Theorem 5" for the
light model (thin_claim).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- Local 10 of thin: the result of the test of the regime. -/
abbrev Thin.Expo : ℕ := 10

open ThinArg Thin in
/-- thin(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBody : Stmt :=
  (Light.Stmt.seq (.call pRegime [v Rows, v Cols, v Wanted] Expo)
    (.ite (Light.Cond.lt (k 0) (v Expo))
      (.call pThm5 [v Rows, v Cols, v Wanted, v Bound, v AdrX, v AdrY, v AdrWI, v AdrWJ, v AdrOut, v Free] 0)
      (.call pThinBrute [v Rows, v Cols, v Wanted, v Bound, v AdrX, v AdrY, v AdrWI, v AdrWJ, v AdrOut, v Free] 0)))


































/-! ## The need -/





















































/-! ## The regime -/


























/-! ## The time -/





















































/-! ## The solver of Theorem 5 may be called -/


























































































































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Encode_AllBands


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The encodings of all bands of one matrix (Section 2.4.1)

Section 2.4.1: "We compute the encodings of the input arrays of all row bands and all column bands
[...], and every tile reads its two encodings from these."  encodeBands does this for one of the two
matrices: for each band β it calls bandArray, which forms the input array of the band at arr, and
encode, which leaves its encoding in the T = 10^L cells from enc + β T.

The loop is treated once, for callees that are described by what they do here (`encodeBands_proc`).
The two entries, for the row bands of X and for the column bands of Y, put in the specifications of
bandArray and encode for their side.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace Bands

/-- The local variables of `encodeBands`.  The arguments: `Levels` = L, `Size` = m, `Rows` = N,
`Cols` = D, `NumBlocks` = K0, `Width` = N0, `Cells` = S7 = 7^L, `Leaves` = T = 10^L and `NumBands` =
nB are the sizes of the layout; `Side` says which of the two matrices stands at `Source`, with the
steps `StepRow` and `StepCol`; `MaskTable`, `Digits3` and `Digits4` are the tables that
`bandArray` reads, `Table`, `Pow7` and `Pow10` those that `encode` reads; `Arr` and `Scratch` are
scratch areas, and the encodings are written from `Enc` on.  Then `BandNo` = β, and `Res` takes the
results of the calls. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Cols : ℕ := 3
@[inherit_doc Levels] abbrev NumBlocks : ℕ := 4
@[inherit_doc Levels] abbrev Width : ℕ := 5
@[inherit_doc Levels] abbrev Cells : ℕ := 6
@[inherit_doc Levels] abbrev Leaves : ℕ := 7
@[inherit_doc Levels] abbrev NumBands : ℕ := 8
@[inherit_doc Levels] abbrev Side : ℕ := 9
@[inherit_doc Levels] abbrev Source : ℕ := 10
@[inherit_doc Levels] abbrev StepRow : ℕ := 11
@[inherit_doc Levels] abbrev StepCol : ℕ := 12
@[inherit_doc Levels] abbrev MaskTable : ℕ := 13
@[inherit_doc Levels] abbrev Digits3 : ℕ := 14
@[inherit_doc Levels] abbrev Digits4 : ℕ := 15
@[inherit_doc Levels] abbrev Arr : ℕ := 16
@[inherit_doc Levels] abbrev Scratch : ℕ := 17
@[inherit_doc Levels] abbrev Table : ℕ := 18
@[inherit_doc Levels] abbrev Pow7 : ℕ := 19
@[inherit_doc Levels] abbrev Pow10 : ℕ := 20
@[inherit_doc Levels] abbrev Enc : ℕ := 21
@[inherit_doc Levels] abbrev BandNo : ℕ := 22
@[inherit_doc Levels] abbrev Res : ℕ := 23

end Bands

open Bands in
/-- encodeBands(L, m, N, D, K0, N0, S7, T, nB, side, aA, sI, sK, mask, dig3, dig4, arr, zs, tab, p7,
p10, enc): for each band, the input array is formed at arr and encoded into the T cells from
enc + β T. -/
def encodeBandsBody : Stmt :=
  .for BandNo (v NumBands) (
    (Light.Stmt.seq
      (.call pBandArray
        [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo, v Side, v Source, v StepRow, v StepCol,
          v MaskTable, v Digits3, v Digits4, v Arr]
        Res)
      (.call pEncode
        [v Levels, v Arr, (Light.Expr.op Light.Op.add) (v Enc) ((Light.Expr.op Light.Op.mul) (v BandNo) (v Leaves)),
          v Scratch, v Table, v Pow7, v Pow10]
        Res)))














/-! ## The arguments, and what is assumed about them -/

/-- The addresses that encodeBands gets besides that of the matrix.  mask, dig3 and dig4 are the
tables that bandArray reads, tab, p7 and p10 those that encode reads.  arr and zs are scratch, and
the encodings are written from enc on. -/
structure BandsArgs where
  (mask dig3 dig4 arr zs tab p7 p10 enc : ℕ)

/-- The arguments of encodeBands at the sizes of p, for the matrix at aA with the strides sI and
sK. -/
@[simp] def BandsArgs.vals (x : BandsArgs) (p : Par) (side aA sI sK : ℕ) : List ℤ :=
  [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK, x.mask, x.dig3, x.dig4,
    x.arr, x.zs, x.tab, x.p7, x.p10, x.enc]

/-- What encodeBands assumes besides the matrix.  Everything that is read lies below enc: the tables
of bandArray, the 70 coefficients coefs of the side, and the powers of 7 and of 10.  From enc on
follow the encodings and the two scratch areas.  V bounds the entries of the matrix. -/
structure BandsPre (lim : Limits) (p : Par) (μ : ℕ → ℤ) (x : BandsArgs) (coefs : List ℤ) (V : ℤ) :
    Prop where
  tables : BandTables p μ x.mask x.dig3 x.dig4 x.enc
  coef : Seg μ x.tab coefs
  coef_le : x.tab + 70 ≤ x.enc
  p7 : Seg μ x.p7 (powList 7 (p.L + 1))
  p7_le : x.p7 + (p.L + 1) ≤ x.enc
  p10 : Seg μ x.p10 (powList 10 (p.L + 1))
  p10_le : x.p10 + (p.L + 1) ≤ x.enc
  enc_le : x.enc + p.nB * p.T ≤ x.arr
  arr_le : x.arr + p.S7 ≤ x.zs
  zs_le : x.zs + p.S7 ≤ lim.space
  V_nonneg : 0 ≤ V
  word : 7 ^ (p.L + 1) * V ≤ lim.word

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : ℕ → ℤ}


















































/-! ## What is read does not change -/



















































/-! ## The two entries -/

/-- encodeBands for the row bands of X: side = 0, the coefficients φ at tab. -/
def EncodeBandsLSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aX : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.phiFlat V → MatAt μ aX X → aX + p.N * p.D ≤ x.enc →
    (∀ i j, |X i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBands d (x.vals p 0 aX p.D 1) μ
      (c * (p.nB * (p.T + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, Seg μ' (x.enc + β * p.T)
          (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)





















/-- encodeBands for the column bands of Y: side = 1, the coefficients ψ at tab. -/
def EncodeBandsRSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aY : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.psiFlat V → MatAt μ aY Y → aY + p.D * p.N ≤ x.enc →
    (∀ i j, |Y i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBands d (x.vals p 1 aY 1 p.N) μ
      (c * (p.nB * (p.T + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, Seg μ' (x.enc + β * p.T)
          (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)





















end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Encode_BandArrayFacts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The input array of a band: what the loops compute

The input array of a band (Sections 2.3.3 and 2.3.4) holds entries of the matrix at the codes of
certain strings and 0 elsewhere.  The table of subsets lists subsets of size m of the L levels:
`Spec.unrank L m s` is the mask of subset number s, and the block product (g, h) of a tile uses
subset number g K₀ + h.  No program text occurs here.  `BandArgs` collects the arguments of
bandArray: the number of a row, the address of a mask and the code of a string are functions of
them.

* The code of a left or right string is computed level by level: `codeUpTo` is the code of the first
  l levels.  One more level appends the next outer digit, or 3 plus the next inner digit
  (`codeUpTo_succ`), and after all levels the code is `Spec.gluedCode` (`codeUpTo_unrank`).
* The numbers that occur are small (`BandArgs.rowNo_lt`, `subsetIndex_lt`, `BandArgs.code_lt`).
* The array is filled in the order of the tuples (g, h, r, k), not of the codes.  `OverwrittenWith`
  says of two memories that cells of the array were overwritten only with the entries of the target
  list, so that a cell that is right stays right.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The code of a string, level by level -/

section code
variable {bs : List Bool} {o i : List ℕ} {l : ℕ}

/-- The code of the first l levels: Horner's rule in base 7 on the outer digits o and 3 plus the
inner digits i, interleaved along the mask bs. -/
def codeUpTo (bs : List Bool) (o i : List ℕ) (l : ℕ) : ℕ :=
  ThreeSumApsp.ofDigitList 7 ((Spec.gluedDigits bs o i).take l)

















end code









/-! ## Sizes -/









/-- The arguments of bandArray. -/
structure BandArgs where
  /-- The parameters L, m, N. -/
  p : Par
  /-- The number of the band. -/
  β : ℕ
  /-- 0 for a row band of X, 1 for a column band of Y. -/
  side : ℕ
  /-- The address of the matrix. -/
  aA : ℕ
  /-- The step from a row (of X, or column of Y) to the next. -/
  sI : ℕ
  /-- The step from a column of X (or row of Y) to the next. -/
  sK : ℕ
  /-- The address of the table of subsets. -/
  mask : ℕ
  /-- The address of the table of digits in base 3. -/
  dig3 : ℕ
  /-- The address of the table of digits in base 4. -/
  dig4 : ℕ
  /-- The address of the array. -/
  arr : ℕ

namespace BandArgs
variable (A : BandArgs)

/-- The number of the block of rows of the matrix `X` (`side = 0`), or of columns of the matrix `Y`
(any other side), for the block product `(g, h)`. -/
def blockNo (g h : ℕ) : ℕ := A.β * A.p.K0 + if A.side = 0 then g else h

/-- The number of the row of `X` (or column of `Y`) for the block product `(g, h)` and the row `r`
of the block. -/
def rowNo (g h r : ℕ) : ℕ := A.blockNo g h * A.p.N0 + r

/-- The address of the mask of the subset of the block product `(g, h)`. -/
def maskRow (g h : ℕ) : ℕ := A.mask + (g * A.p.K0 + h) * A.p.L

/-- The code of the string for the block product `(g, h)`, the row `r` and the column `k`. -/
def code (g h r k : ℕ) : ℕ :=
  Spec.gluedCode A.p.L A.p.m (Spec.unrank A.p.L A.p.m (g * A.p.K0 + h)) r k





variable {A}






























end BandArgs


















/-! ## Overwriting with the entries of a target list -/

section ext
variable {T : List ℤ} {arr n : ℕ} {μ μ' μ'' : ℕ → ℤ}

/-- The memory μ' agrees with μ outside the n cells from arr, and each of these cells holds what it
held in μ or the entry of the target T. -/
def OverwrittenWith (T : List ℤ) (arr n : ℕ) (μ μ' : ℕ → ℤ) : Prop :=
  SameOutside μ μ' arr n ∧ ∀ c < n, μ' (arr + c) = μ (arr + c) ∨ μ' (arr + c) = T.getD c 0


























end ext

end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Encode_BandArray


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The input array of a band (Section 2.3.4)

Section 2.3.3: "a[u] := X_Q[u], b[v] := Y_Q[v] for all the left strings u and the right strings v
whose inner set Q has exactly m elements, and a[u] := 0, b[v] := 0 at every other string"; in
Section 2.3.4, X_Q and Y_Q are the row block and the column block of the block product with subset
Q.  bandArray writes this input array for a row band of X or a column band of Y.  The array is
laid out by the codes of the left (right) strings and filled in the order of the tuples: the
procedure clears the array, and then, for every block product (g, h) of a tile, every row r of the
block and every column k, it computes the code of the string digit by digit and copies one entry of
the matrix.

The proof goes from the inside to the outside, one lemma for the body of each loop and one for the
loop: a level of the code (`bandLevel_spec`, `bandCodeLoop_spec`), an entry (`bandCell_spec`,
`bandColLoop_spec`), a row of a block (`bandRow_spec`, `bandRowLoop_spec`), a block product
(`bandRows_spec`, `bandBlock_spec`, `bandHLoop_spec`, `bandGLoop_spec`), and the whole procedure
(`bandArray_spec`, within the time `bandArray_time`).  The four outer loops keep the same fact about
the memory: cells of the array are overwritten only with entries of the target list
(`OverwrittenWith`), and the cells of the tuples handled so far are right (`Covered`).  So they are
four cases of one lemma, `coverLoop`.  `bandArrayL_entry` and `bandArrayR_entry`, the cases of X and
of Y, are the specifications that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

/-! ## The program -/

namespace Band

/-- The local variables of bandArray.  The arguments: `Levels` = L, `Size` = m, `Rows` = N, `Cols` =
D, `NumBlocks` = K0, `Width` = N0, `Cells` = S7, `BandNo` = β, `Side` = side; `Source` is the
address of the matrix, `StepRow` and `StepCol` the steps from row to row and from column to column;
`MaskTable`, `Digits3`, `Digits4` and `Dest` are the addresses of the table of subsets, of the two
tables of digits and of the array.  Then, by the depth of the loop that uses them: `PosG` = g (also
the counter of the clearing loop); `PosH` = h, `BlockIdx` the number of the block, `MaskRow` the
address of the mask of the subset; `Offset` = r, `Row` the number of the row of the matrix; `Col` =
k, `CodeAcc` the code, `Outer` and `Inner` the addresses of the next outer and of the next inner
digit, `CurLevel` the level. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Cols : ℕ := 3
@[inherit_doc Levels] abbrev NumBlocks : ℕ := 4
@[inherit_doc Levels] abbrev Width : ℕ := 5
@[inherit_doc Levels] abbrev Cells : ℕ := 6
@[inherit_doc Levels] abbrev BandNo : ℕ := 7
@[inherit_doc Levels] abbrev Side : ℕ := 8
@[inherit_doc Levels] abbrev Source : ℕ := 9
@[inherit_doc Levels] abbrev StepRow : ℕ := 10
@[inherit_doc Levels] abbrev StepCol : ℕ := 11
@[inherit_doc Levels] abbrev MaskTable : ℕ := 12
@[inherit_doc Levels] abbrev Digits3 : ℕ := 13
@[inherit_doc Levels] abbrev Digits4 : ℕ := 14
@[inherit_doc Levels] abbrev Dest : ℕ := 15
@[inherit_doc Levels] abbrev PosG : ℕ := 16
@[inherit_doc Levels] abbrev PosH : ℕ := 17
@[inherit_doc Levels] abbrev BlockIdx : ℕ := 18
@[inherit_doc Levels] abbrev MaskRow : ℕ := 19
@[inherit_doc Levels] abbrev Offset : ℕ := 20
@[inherit_doc Levels] abbrev Row : ℕ := 21
@[inherit_doc Levels] abbrev Col : ℕ := 22
@[inherit_doc Levels] abbrev CodeAcc : ℕ := 23
@[inherit_doc Levels] abbrev Outer : ℕ := 24
@[inherit_doc Levels] abbrev Inner : ℕ := 25
@[inherit_doc Levels] abbrev CurLevel : ℕ := 26

end Band

open Band

/-- One level: Horner's rule in base 7, with the next outer digit, or 3 plus the next inner
digit. -/
def bandLevel : Stmt :=
  .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v MaskRow) (v CurLevel))) (k 0)))
    ((Light.Stmt.seq
       (.set CodeAcc ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v CodeAcc) (k 7)) (M (v Outer))))
       (.set Outer ((Light.Expr.op Light.Op.add) (v Outer) (k 1)))))
    ((Light.Stmt.seq
       (.set CodeAcc
         ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v CodeAcc) (k 7)) (k 3))
           (M (v Inner))))
       (.set Inner ((Light.Expr.op Light.Op.add) (v Inner) (k 1)))))

/-- The loop over the levels. -/
def bandCodeLoop : Stmt := .for CurLevel (v Levels) bandLevel

/-- One entry: the code of the string, and the entry copied. -/
def bandCell : Stmt :=
  (Light.Stmt.seq (.set CodeAcc (k 0))
    (Light.Stmt.seq
      (.set Outer
        ((Light.Expr.op Light.Op.add) (v Digits3)
          ((Light.Expr.op Light.Op.mul) (v Row) ((Light.Expr.op Light.Op.sub) (v Levels) (v Size)))))
      (Light.Stmt.seq
        (.set Inner ((Light.Expr.op Light.Op.add) (v Digits4) ((Light.Expr.op Light.Op.mul) (v Col) (v Size))))
        (Light.Stmt.seq bandCodeLoop
          (.store ((Light.Expr.op Light.Op.add) (v Dest) (v CodeAcc))
            (M
              ((Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) (v Source) ((Light.Expr.op Light.Op.mul) (v Row) (v StepRow)))
                ((Light.Expr.op Light.Op.mul) (v Col) (v StepCol)))))))))

/-- The loop over the columns k. -/
def bandColLoop : Stmt := .for Col (v Cols) bandCell

/-- One row r of a block; rows beyond the matrix are skipped. -/
def bandRow : Stmt :=
  (Light.Stmt.seq
    (.set Row ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v BlockIdx) (v Width)) (v Offset)))
    (.ite (Light.Cond.lt (v Row) (v Rows)) bandColLoop .skip))

/-- The loop over the rows r of a block. -/
def bandRowLoop : Stmt := .for Offset (v Width) bandRow

/-- The address of the mask of the subset of the block product (g, h), and the rows of the block. -/
def bandRows : Stmt :=
  (Light.Stmt.seq
    (.set MaskRow
      ((Light.Expr.op Light.Op.add) (v MaskTable)
        ((Light.Expr.op Light.Op.mul)
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v PosG) (v NumBlocks)) (v PosH)) (v Levels))))
    bandRowLoop)

/-- One block product (g, h): the number of the block, which depends on the side, and the rest. -/
def bandBlock : Stmt :=
  (Light.Stmt.seq
    (.ite (Light.Cond.eq (v Side) (k 0))
      (.set BlockIdx ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v BandNo) (v NumBlocks)) (v PosG)))
      (.set BlockIdx ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v BandNo) (v NumBlocks)) (v PosH))))
    bandRows)

/-- The loop over h. -/
def bandHLoop : Stmt := .for PosH (v NumBlocks) bandBlock

/-- The loop over g. -/
def bandGLoop : Stmt := .for PosG (v NumBlocks) bandHLoop

/-- The clearing loop. -/
def bandZeroLoop : Stmt := pass PosG (v Cells) (v Dest) (k 0)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr). -/
def bandArrayBody : Stmt := (Light.Stmt.seq bandZeroLoop bandGLoop)

/-- The constant of the running time. -/
def cBandArray : ℕ := 120

/-! ## The local variables as a list -/

/-- The local variables of the loop over h. -/
structure BlockTmp where
  /-- h. -/
  h : ℤ
  /-- The number of the block. -/
  blk : ℤ
  /-- The address of the mask of the subset. -/
  mrow : ℤ

/-- The local variables of the loop over the rows of a block. -/
structure RowTmp where
  /-- r. -/
  r : ℤ
  /-- The number of the row of the matrix. -/
  row : ℤ

/-- The local variables of the loop over the columns. -/
structure CellTmp where
  /-- k. -/
  k : ℤ
  /-- The code. -/
  code : ℤ
  /-- The address of the next outer digit. -/
  outer : ℤ
  /-- The address of the next inner digit. -/
  inner : ℤ
  /-- The level. -/
  lev : ℤ

/-- The local variables of the three inner loops together. -/
structure InnerTmp where
  /-- Those of the loop over `h`. -/
  block : BlockTmp
  /-- Those of the loop over the rows of a block. -/
  row : RowTmp
  /-- Those of the loop over the columns. -/
  cell : CellTmp

/-- The list of the local variables. -/
abbrev Band.locals (A : BandArgs) (g : ℤ) (H : BlockTmp) (R : RowTmp) (c : CellTmp) : List ℤ :=
  [A.p.L, A.p.m, A.p.N, A.p.D, A.p.K0, A.p.N0, A.p.S7, A.β, A.side, A.aA, A.sI, A.sK, A.mask,
    A.dig3, A.dig4, A.arr, g, H.h, H.blk, H.mrow, R.r, R.row, c.k, c.code, c.outer, c.inner, c.lev]

/-- The local variables of the loop over `h` for the block product `(g, h)`. -/
abbrev Band.blockTmp (A : BandArgs) (g h : ℕ) : BlockTmp :=
  ⟨h, (A.blockNo g h : ℕ), (A.maskRow g h : ℕ)⟩

/-- The local variables of the loop over the rows for the row `r` of the block product `(g, h)`. -/
abbrev Band.rowTmp (A : BandArgs) (g h r : ℕ) : RowTmp := ⟨r, (A.rowNo g h r : ℕ)⟩

variable {lim : Limits} {P : Program} {d : ℕ} {A : BandArgs} {μ₀ μ : ℕ → ℤ} {T : List ℤ}

/-! ## The loop over the levels -/

/-- What the loop over the levels reads: the mask bs at mrow, the outer digits o at d3 and the inner
digits i at d4. -/
structure CodeCtx (lim : Limits) (μ : ℕ → ℤ) (L mrow d3 d4 : ℕ) (bs : List Bool) (o i : List ℕ) :
    Prop where
  std : Std lim
  length : bs.length = L
  outer : bs.count false = o.length
  inner : bs.count true = i.length
  outer_lt : ∀ x ∈ o, x < 3
  inner_lt : ∀ x ∈ i, x < 4
  segB : SegB μ mrow bs
  segO : SegN μ d3 o
  segI : SegN μ d4 i
  spaceB : mrow + L ≤ lim.space
  spaceO : d3 + o.length ≤ lim.space
  spaceI : d4 + i.length ≤ lim.space
  space7 : 7 ^ L ≤ lim.space

/-- The local variables of the loop over the columns after l levels. -/
abbrev Band.codeTmp (k : ℤ) (bs : List Bool) (o i : List ℕ) (d3 d4 l : ℕ) (lev : ℤ) : CellTmp :=
  ⟨k, (codeUpTo bs o i l : ℕ), (d3 + (bs.take l).count false : ℕ),
    (d4 + (bs.take l).count true : ℕ), lev⟩

section levels
variable {mrow d3 d4 : ℕ} {bs : List Bool} {o i : List ℕ} {g h blk k : ℤ} {R : RowTmp}




































































end levels

/-! ## The surroundings -/

/-- Everything that the loops assume: the limits, the places of the tables and of the matrix in the
memory μ₀ at the start, and what is known about the list T that has to be produced. -/
structure BandCtx (lim : Limits) (A : BandArgs) (μ₀ : ℕ → ℤ) (T : List ℤ) : Prop where
  std : Std lim
  hmL : A.p.m ≤ A.p.L
  space : A.arr + A.p.S7 ≤ lim.space
  aA_le : A.aA + A.p.N * A.p.D ≤ A.arr
  tabs : BandTables A.p μ₀ A.mask A.dig3 A.dig4 A.arr
  β_lt : A.β < A.p.nB
  idx : ∀ row < A.p.N, ∀ k < A.p.D, row * A.sI + k * A.sK < A.p.N * A.p.D
  T_len : T.length = A.p.S7
  entry : ∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D, T.getD (A.code g h r k) 0
    = if A.rowNo g h r < A.p.N
      then μ₀ (A.aA + (A.rowNo g h r * A.sI + k * A.sK)) else 0
  zero : ∀ c : ℕ, (∀ g < A.p.K0, ∀ h < A.p.K0, ∀ r < A.p.N0, ∀ k < A.p.D,
    c ≠ A.code g h r k) → T.getD c 0 = 0

/-- The cell of the tuple (g, h, r, k) is right. -/
def Covered (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r k : ℕ) : Prop :=
  μ (A.arr + A.code g h r k) = T.getD (A.code g h r k) 0






namespace BandCtx
















































end BandCtx

/-! ## A loop that fills cells -/


































/-! ## The loop over the columns -/

/-- The time of one entry. -/
def tBandCell (p : Par) : ℕ := 28 * p.L + 36

section cell
variable {g h r k : ℕ}









































/-- The time of the loop over the columns. -/
def tBandCol (p : Par) : ℕ := p.D * (tBandCell p + 8) + 6






















end cell

/-! ## The loop over the rows of a block -/

/-- The cells of the row r of the block product (g, h) are right, if the row lies in the matrix. -/
def CoveredRow (A : BandArgs) (T : List ℤ) (μ : ℕ → ℤ) (g h r : ℕ) : Prop :=
  A.rowNo g h r < A.p.N → ∀ k < A.p.D, Covered A T μ g h r k

/-- The time of one row of a block. -/
def tBandRow (p : Par) : ℕ := tBandCol p + 10

/-- The time of the loop over the rows of a block. -/
def tBandRows (p : Par) : ℕ := p.N0 * (tBandRow p + 8) + 6

section rows
variable {g h r : ℕ}











































end rows

/-! ## The loops over h and g -/

/-- The time of one block product. -/
def tBandBlock (p : Par) : ℕ := tBandRows p + 20

/-- The time of the loop over h. -/
def tBandH (p : Par) : ℕ := p.K0 * (tBandBlock p + 8) + 6

/-- The time of the loop over g. -/
def tBandG (p : Par) : ℕ := p.K0 * (tBandH p + 8) + 6

section blocks
variable {g h : ℕ}


















































































end blocks

/-! ## The whole procedure -/




















/-- The arguments of bandArray as a list. -/
abbrev Band.args (A : BandArgs) : List ℤ :=
  [A.p.L, A.p.m, A.p.N, A.p.D, A.p.K0, A.p.N0, A.p.S7, A.β, A.side, A.aA, A.sI, A.sK, A.mask,
    A.dig3, A.dig4, A.arr]































/-! ## What the callers assume -/

/-- The arguments of `bandArray` for the row band `β` of `X`, which stands at `aX` row by row. -/
abbrev BandArgs.ofX (p : Par) (β aX mask dig3 dig4 arr : ℕ) : BandArgs :=
  { p := p, β := β, side := 0, aA := aX, sI := p.D, sK := 1, mask := mask, dig3 := dig3,
    dig4 := dig4, arr := arr }

/-- The arguments of `bandArray` for the column band `β` of `Y`, which stands at `aY` row by row. -/
abbrev BandArgs.ofY (p : Par) (β aY mask dig3 dig4 arr : ℕ) : BandArgs :=
  { p := p, β := β, side := 1, aA := aY, sI := 1, sK := p.N, mask := mask, dig3 := dig3,
    dig4 := dig4, arr := arr }






















































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Encode_Step


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# One encoding step (step (2) of Full, Section 2.3.1)

"For each term λ of Schönhage's identity, form A_λ := ∑_s φ_λ(s) a_s and B_λ := ∑_t ψ_λ(t) b_t."
The array a is in 7 n consecutive cells at src, slice after slice; the coefficients of all the forms
are in a table at tab, seven for each term; the array A_λ is written to n cells at dst.  B_λ is
formed by the same procedure, from the array b and the table of the coefficients of the ψ_λ.

`encStepVal` is the sum that belongs in a cell, summand by summand.  Its partial sums are small
(`EncStepPre.val_bounds`), and it does not change while the cells of `dst` are written
(`EncStepPre.val_congr`).  `encStepSum_spec` forms one sum, and `encStep_meets` runs through the
cells.
-/

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp

namespace EncStep

/-- The local variables of encStep: the arguments src, dst, n, lam, tab; the cell j of dst; the sum;
the number s of the summand. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dest : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev TermNo : ℕ := 3
@[inherit_doc Src] abbrev Table : ℕ := 4
@[inherit_doc Src] abbrev Cell : ℕ := 5
@[inherit_doc Src] abbrev Acc : ℕ := 6
@[inherit_doc Src] abbrev Var : ℕ := 7

end EncStep

open EncStep

/-- One summand: Acc := Acc + tab[7 lam + s] · src[s n + j]. -/
def encStepAdd : Stmt :=
  .set Acc
    (((Light.Expr.op Light.Op.add) (v Acc)
       ((Light.Expr.op Light.Op.mul)
         (M
           ((Light.Expr.op Light.Op.add)
             ((Light.Expr.op Light.Op.add) (v Table) ((Light.Expr.op Light.Op.mul) (k 7) (v TermNo))) (v Var)))
         (M
           ((Light.Expr.op Light.Op.add)
             ((Light.Expr.op Light.Op.add) (v Src) ((Light.Expr.op Light.Op.mul) (v Var) (v Len))) (v Cell))))))

/-- The sum over s < 7 of tab[7 lam + s] · src[s n + j]. -/
def encStepSum : Stmt := .for Var (k 7) encStepAdd

/-- One cell of dst. -/
def encStepCell : Stmt := (Light.Stmt.seq (.set Acc (k 0))
                            (Light.Stmt.seq encStepSum (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Cell)) (v Acc))))

/-- encStep(src, dst, n, lam, tab): for j < n, dst[j] := ∑_{s < 7} tab[7 lam + s] · src[s n + j]. -/
def encStepBody : Stmt := .for Cell (v Len) encStepCell

/-! ## The sums -/

/-- The first s summands of what encStep writes at dst + j. -/
def encStepVal (μ : ℕ → ℤ) (src lam tab n j s : ℕ) : ℤ :=
  ∑ i ∈ range s, μ (tab + 7 * lam + i) * μ (src + i * n + j)

/-- What encStep writes at dst + c. -/
abbrev encStepOut (μ : ℕ → ℤ) (src lam tab n : ℕ) : ℕ → ℤ := fun c => encStepVal μ src lam tab n c 7







/-- The hypotheses of `encStep`: the seven coefficients and the array at `src` lie below the `n`
cells at `dst`, which lie in the memory; the coefficients are -1, 0 or 1, the numbers are at most
`V` in absolute value, and `7 V` fits in a word. -/
structure EncStepPre (lim : Limits) (μ : ℕ → ℤ) (src dst n lam tab : ℕ) (V : ℤ) : Prop where
  std : Std lim
  tab_le : tab + 7 * lam + 7 ≤ dst
  src_le : src + 7 * n ≤ dst
  dst_le : dst + n ≤ lim.space
  coef : ∀ i < 7, -1 ≤ μ (tab + 7 * lam + i) ∧ μ (tab + 7 * lam + i) ≤ 1
  vals : ∀ i < 7 * n, -V ≤ μ (src + i) ∧ μ (src + i) ≤ V
  word_bound : 7 * V ≤ lim.word

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' : ℕ → ℤ} {src dst n lam tab j : ℕ} {V : ℤ}


















namespace EncStepPre

































end EncStepPre

/-! ## The program -/

variable {T : ℕ} {Q : State → Prop}




































/-- A bound on the number of steps of `encStep` on `n` cells. -/
def tEncStep (n : ℕ) : ℕ := 217 * n + 6































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Encode_Recursion


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The encoding of an array by the recursion of Section 2.4.1

"To compute it, we run Full with b left out and without step (4)" (Section 2.4.1).  If L = 0 the
leaf stores its number.  Otherwise, for each term λ, step (2) writes A_λ to a scratch area and the
recursive call of step (3) encodes it into the part of the output that belongs to the leaves below
λ.  The language has no division, so the lengths 7^{L-1} and 10^{L-1} of the parts are read from two
tables of powers.

`encIdx` is what `encode` computes, in terms of positions in arrays.  `encode` writes it to the
output within `encTime L = O(10^L)` steps (`encTime_le`), using `scrSize L` scratch cells.  The
proof is by induction on `L`:

* the hypotheses of `encode` at level `L + 1` give those of `encStep` (`EncodePre.toStep`) and,
  after it, those of the recursive call (`EncodePre.toRec`);
* the two calls for the term `λ` fill the part of the output below `λ` (`TermsDone.step`,
  `encodeTerm_spec`);
* `encode_leaf` is the case `L = 0`, `encode_node` the loop over the ten terms, and `encode_spec`
  the induction.
-/

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp

namespace Encode

/-- The local variables of encode: the arguments L, src, out, scr, tab, p7, p10; the lengths 7^{L-1}
and 10^{L-1}; the number of the term; the result of a call, which is not used. -/
abbrev Level : ℕ := 0
@[inherit_doc Level] abbrev Src : ℕ := 1
@[inherit_doc Level] abbrev Out : ℕ := 2
@[inherit_doc Level] abbrev Scr : ℕ := 3
@[inherit_doc Level] abbrev Table : ℕ := 4
@[inherit_doc Level] abbrev Pow7 : ℕ := 5
@[inherit_doc Level] abbrev Pow10 : ℕ := 6
@[inherit_doc Level] abbrev Len7 : ℕ := 7
@[inherit_doc Level] abbrev Len10 : ℕ := 8
@[inherit_doc Level] abbrev TermNo : ℕ := 9
@[inherit_doc Level] abbrev Res : ℕ := 10

end Encode

open Encode

/-- The two calls for one term: step (2) into the scratch area, and step (3) from there into the
part of the output that belongs to the term. -/
def encodeTerm (pS pE : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pS [v Src, v Scr, v Len7, v TermNo, v Table] Res)
    (.call pE
      [(Light.Expr.op Light.Op.sub) (v Level) (k 1), v Scr,
        (Light.Expr.op Light.Op.add) (v Out) ((Light.Expr.op Light.Op.mul) (v TermNo) (v Len10)),
        (Light.Expr.op Light.Op.add) (v Scr) (v Len7), v Table, v Pow7, v Pow10]
      Res))

/-- encode(L, src, out, scr, tab, p7, p10).  pS and pE are the numbers that the procedures encStep
and encode have in the program. -/
def encodeBody (pS pE : ℕ) : Stmt :=
  .ite ((Light.Cond.eq (v Level) (k 0)))
    (.store (v Out) (M (v Src)))
    ((Light.Stmt.seq (.set Len7 (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v Pow7) (v Level)) (k 1))))
       (Light.Stmt.seq
         (.set Len10 (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v Pow10) (v Level)) (k 1))))
         (.for TermNo (k 10) (encodeTerm pS pE)))))

/-! ## What encode computes, how much room and how much time it needs -/

/-- The array A_lam of step (2), in terms of positions in arrays: a is the input array (7^{L+1}
numbers, seven slices of 7^L) and c the table of the coefficients (c (7 lam + s) is the coefficient
of slice number s in the term number lam). -/
def encSlice (c a : ℕ → ℤ) (L lam : ℕ) : ℕ → ℤ :=
  fun j => ∑ s ∈ range 7, c (7 * lam + s) * a (s * 7 ^ L + j)

/-- What encode computes, in terms of positions in arrays: a is the input array (7^L numbers), c the
table of the coefficients, and i < 10^L the position of a leaf. -/
def encIdx (c : ℕ → ℤ) : (L : ℕ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, a, _ => a 0
  | L + 1, a, i => encIdx c L (encSlice c a L (i / 10 ^ L)) (i % 10 ^ L)






/-- The number of scratch cells that encode uses: 7^{L-1} + ⋯ + 7 + 1. -/
def scrSize : ℕ → ℕ
  | 0 => 0
  | L + 1 => 7 ^ L + scrSize L

/-- A bound on the number of steps of `encode`: at level `L + 1`, ten times the two calls for a
term, and 104 steps. -/
def encTime : ℕ → ℕ
  | 0 => 8
  | L + 1 => 104 + 10 * (24 + tEncStep (7 ^ L) + encTime L)

/-- The time of the two calls for one term. -/
def tTerm (L : ℕ) : ℕ := 24 + tEncStep (7 ^ L) + encTime L

/-- The constant of the running time of `encode`. -/
def cEncode : ℕ := 777











/-! ## The hypotheses -/

/-- Where the arrays of `encode` lie: the three tables, then the output, the input and the scratch
area, one behind the other. -/
structure EncodeLayout (lim : Limits) (src out scr tab p7 p10 L : ℕ) : Prop where
  std : Std lim
  tab_le : tab + 70 ≤ out
  p7_le : p7 + L ≤ out
  p10_le : p10 + L ≤ out
  out_le : out + 10 ^ L ≤ src
  src_le : src + 7 ^ L ≤ scr
  scr_le : scr + scrSize L ≤ lim.space

/-- The hypotheses of `encode`: the layout, what the cells hold, and how large the numbers are. -/
structure EncodePre (lim : Limits) (μ : ℕ → ℤ) (src out scr tab p7 p10 : ℕ) (V : ℤ) (L : ℕ)
    (a c : ℕ → ℤ) : Prop where
  lay : EncodeLayout lim src out scr tab p7 p10 L
  srcV : ∀ j < 7 ^ L, μ (src + j) = a j
  src_bound : ∀ j < 7 ^ L, -V ≤ a j ∧ a j ≤ V
  tabV : ∀ i < 70, μ (tab + i) = c i
  coef_bound : ∀ i < 70, -1 ≤ c i ∧ c i ≤ 1
  p7V : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)
  p10V : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ)
  word_bound : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word

/-- What `encode` guarantees: the encoding is in `out`, and only the `10^L` cells of `out` and the
`scrSize L` cells of the scratch area have changed. -/
def EncodePost (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < 10 ^ L, μ' (out + i) = encIdx c L a i) ∧ SameOutside2 μ μ' out (10 ^ L) scr (scrSize L)

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam : ℕ} {V : ℤ} {a c : ℕ → ℤ}


























namespace EncodePre

































































end EncodePre

/-! ## One term -/

/-- The memory before the round of the term number `lam`: the parts of the output below the earlier
terms are filled, and only the output and the scratch area have changed. -/
def TermsDone (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (lam : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < lam * 10 ^ L, μ' (out + i) = encIdx c (L + 1) a i) ∧
    SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))























/-- The list of the local variables at level L + 1. -/
abbrev Encode.locals (L src out scr tab p7 p10 lam : ℕ) (r : ℤ) : List ℤ :=
  [(L + 1 : ℕ), src, out, scr, tab, p7, p10, (7 ^ L : ℕ), (10 ^ L : ℕ), lam, r]

/-- The specification of encode at level L, for a caller at depth d. -/
def EncodeMeets (lim : Limits) (P : Program) (pE d tab p7 p10 L : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (src out scr : ℕ) (V : ℤ) (a : ℕ → ℤ),
    EncodePre lim μ src out scr tab p7 p10 V L a c →
    Meets lim P pE (d + 1) [L, src, out, scr, tab, p7, p10] μ (encTime L) fun _ μ' =>
      EncodePost μ out scr L a c μ'

variable {pS pE : ℕ}






















/-! ## The recursion -/




















































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_LibraryContracts


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Three routines of the library, as their callers see them

The programs for Theorem 5 call their procedures by number, and a caller assumes a specification of
the procedure that does not name its body: PowSpec for the tables of powers, FillSpec for filling a
segment, SqrtSpec for the square root.  Each follows from the specification of the routine in the
library; pow first puts its arguments in the order of the library's routine.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {c : ℕ}

/-! ## The tables of powers -/

/-- pow(b, n, dst): the arguments are put in the order of powTable(dst, n + 1, b), whose body
follows.  Local 5 is a temporary. -/
def powBody : Stmt :=
  (Light.Stmt.seq (.set 5 (v 0))
    (Light.Stmt.seq (.set 0 (v 2))
      (Light.Stmt.seq (.set 2 (v 5)) (Light.Stmt.seq (.set 1 ((Light.Expr.op Light.Op.add) (v 1) (k 1))) powTableBody))))


















/-! ## Filling a segment -/







/-! ## The square root -/






end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Pruned_AllTiles


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5 as a program: the pruned recursion on every tile

Section 2.4.4: "for each tile T with W_T ≠ ∅, we run Pruned(W_T)".

The wanted positions have been sorted by tile and, within a tile, by code.  The codes of the tile
number t = β nB + β' are the cells START[t], …, START[t+1] - 1 of SC.  runTiles walks over all
tiles; for each tile with START[t] < START[t+1] it calls the pruned recursion on the encodings of
the row band β and of the column band β', and the values land in the same cells of SV.

* The memory.  `TilesInv` says which tiles are done.  What the call for a tile assumes holds
  (`TilesPre.tile`), and the call finishes the tile (`TilesInv.of_call`); a tile without wanted
  positions is finished as it is (`TilesInv.of_empty`).
* The program.  `runTile_ends` treats one tile, `runTilesInner_ends` the tiles of a row band,
  `runBand_ends` a row band, and `runTiles_entry` all of them.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## What the callers may assume

`RunTilesSpec` says what a call of procedure `pRunTiles` does, and in how many steps: a constant c
times a shape that depends on the sizes. -/








/-- The arguments of runTiles, with the data behind them.  EA β and EB β' are the encodings of the
bands, which stand at enca and encb, one behind the other; s t = START[t]; codes t are the codes of
tile t; w is the number of wanted positions; A and B bound the numbers in the encodings. -/
structure TilesArgs : Type where
  (nB L enca encb start sc sv sp p10 : ℕ)
  (w : ℕ) (EA EB : ℕ → List ℤ) (s : ℕ → ℕ) (codes : ℕ → List ℕ) (A B : ℤ)





/-- What runTiles assumes.  Everything that is read lies below SV; then come the w cells of SV and,
from sp on, the stack of the pruned recursion. -/
structure TilesPre (lim : Limits) (μ : ℕ → ℤ) (x : TilesArgs) : Prop where
  hp10 : Seg μ x.p10 (powList 10 (x.L + 1))
  hea : ∀ β < x.nB, Seg μ (x.enca + β * 10 ^ x.L) (x.EA β)
  heb : ∀ β < x.nB, Seg μ (x.encb + β * 10 ^ x.L) (x.EB β)
  lea : ∀ β < x.nB, (x.EA β).length = 10 ^ x.L
  leb : ∀ β < x.nB, (x.EB β).length = 10 ^ x.L
  hstart : ∀ t ≤ x.nB * x.nB, μ (x.start + t) = x.s t
  mono : ∀ t < x.nB * x.nB, x.s t ≤ x.s (t + 1)
  s_le : x.s (x.nB * x.nB) ≤ x.w
  hcodes : ∀ t < x.nB * x.nB, SegN μ (x.sc + x.s t) (x.codes t)
  lcodes : ∀ t < x.nB * x.nB, (x.codes t).length = x.s (t + 1) - x.s t
  sorted : ∀ t < x.nB * x.nB, (x.codes t).Pairwise (· < ·)
  small : ∀ t < x.nB * x.nB, ∀ c ∈ x.codes t, c < 10 ^ x.L
  boundA : ∀ β < x.nB, AbsLe (x.EA β) x.A
  boundB : ∀ β < x.nB, AbsLe (x.EB β) x.B
  room : 10 ^ x.L * (x.A * x.B) ≤ lim.word
  ten : ((10 ^ (x.L + 1) : ℕ) : ℤ) ≤ lim.word
  p10_le : x.p10 + (x.L + 1) ≤ x.sc := by first
                                            | omega
                                            | ( (try have := Light.Std.space_le (by assumption))
                                                (try have := Light.Std.const_le (by assumption))
                                                simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  enca_le : x.enca + x.nB * 10 ^ x.L ≤ x.sc := by first
                                                    | omega
                                                    | ( (try have := Light.Std.space_le (by assumption))
                                                        (try have := Light.Std.const_le (by assumption))
                                                        simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  encb_le : x.encb + x.nB * 10 ^ x.L ≤ x.sc := by first
                                                    | omega
                                                    | ( (try have := Light.Std.space_le (by assumption))
                                                        (try have := Light.Std.const_le (by assumption))
                                                        simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  start_le : x.start + (x.nB * x.nB + 1) ≤ x.sc := by first
                                                        | omega
                                                        | ( (try have := Light.Std.space_le (by assumption))
                                                            (try have := Light.Std.const_le (by assumption))
                                                            simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  sc_le : x.sc + x.w ≤ x.sv := by first
                                    | omega
                                    | ( (try have := Light.Std.space_le (by assumption))
                                        (try have := Light.Std.const_le (by assumption))
                                        simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  sv_le : x.sv + x.w ≤ x.sp := by first
                                    | omega
                                    | ( (try have := Light.Std.space_le (by assumption))
                                        (try have := Light.Std.const_le (by assumption))
                                        simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  sp_le : x.sp + x.L * (3 * x.w + 11) ≤ lim.space := by first
                                                          | omega
                                                          | ( (try have := Light.Std.space_le (by assumption))
                                                              (try have := Light.Std.const_le (by assumption))
                                                              simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)












/-! ## The program -/

namespace TilesLocal

/-- The number nB of bands. -/
abbrev NB : ℕ := 0
/-- The number L of levels. -/
abbrev LL : ℕ := 1
/-- T = 10^L, the length of an encoding. -/
abbrev TT : ℕ := 2
/-- The encoding of the row band β. -/
abbrev PEA : ℕ := 3
/-- The encodings of the column bands. -/
abbrev ENCB : ℕ := 4
/-- The address of START[t]. -/
abbrev PST : ℕ := 5
/-- The codes, sorted. -/
abbrev SC : ℕ := 6
/-- The values. -/
abbrev SV : ℕ := 7
/-- The stack of the pruned recursion. -/
abbrev SP : ℕ := 8
/-- The table of the powers of ten. -/
abbrev P10 : ℕ := 9
/-- The row band β. -/
abbrev CB : ℕ := 10
/-- The column band β'. -/
abbrev CC : ℕ := 11
/-- The encoding of the column band β'. -/
abbrev PEB : ℕ := 12
/-- START[t]. -/
abbrev S0 : ℕ := 13
/-- START[t + 1]. -/
abbrev S1 : ℕ := 14
/-- A result that is not used. -/
abbrev RES : ℕ := 15

end TilesLocal

open TilesLocal

/-- One tile: the pruned recursion is called if the tile has wanted positions; then the column band,
its encoding and the address of START[t] move on. -/
def runTile : Stmt :=
  (Light.Stmt.seq (.set S0 (M (v PST)))
    (Light.Stmt.seq (.set S1 (M ((Light.Expr.op Light.Op.add) (v PST) (k 1))))
      (Light.Stmt.seq
        (.ite (Light.Cond.lt (v S0) (v S1))
          (.call pPruned
            [v LL, v PEA, v PEB, (Light.Expr.op Light.Op.add) (v SC) (v S0), (Light.Expr.op Light.Op.sub) (v S1) (v S0),
              (Light.Expr.op Light.Op.add) (v SV) (v S0), v SP, v P10]
            RES)
          .skip)
        (Light.Stmt.seq (.set CC ((Light.Expr.op Light.Op.add) (v CC) (k 1)))
          (Light.Stmt.seq (.set PEB ((Light.Expr.op Light.Op.add) (v PEB) (v TT)))
            (.set PST ((Light.Expr.op Light.Op.add) (v PST) (k 1))))))))

/-- The tiles of one row band. -/
def runTilesInner : Stmt :=
  .while ((Light.Cond.lt (v CC) (v NB))) runTile

/-- One row band. -/
def runBand : Stmt :=
  (Light.Stmt.seq (.set CC (k 0))
    (Light.Stmt.seq (.set PEB (v ENCB))
      (Light.Stmt.seq runTilesInner
        (Light.Stmt.seq (.set CB ((Light.Expr.op Light.Op.add) (v CB) (k 1)))
          (.set PEA ((Light.Expr.op Light.Op.add) (v PEA) (v TT)))))))

/-- runTiles(nB, L, T, enca, encb, start, sc, sv, sp, p10). -/
def runTilesBody : Stmt :=
  (Light.Stmt.seq (.set CB (k 0)) (.while (Light.Cond.lt (v CB) (v NB)) runBand))

/-! ## The memory -/

variable {lim : Limits} {x : TilesArgs} {μ μ' : ℕ → ℤ} {β i : ℕ}

namespace TilesPre
















































end TilesPre

/-- The memory when the tiles before (β, i) are done: only SV and the stack have changed, and the
windows of the tiles that are done hold their values. -/
structure TilesInv (x : TilesArgs) (μ : ℕ → ℤ) (β i : ℕ) (μ' : ℕ → ℤ) : Prop where
  frame : SameOutside2 μ μ' x.sv x.w x.sp (x.L * (3 * x.w + 11))
  done : ∀ b < x.nB, ∀ b' < x.nB, (b < β ∨ (b = β ∧ b' < i)) →
    Seg μ' (x.sv + x.s (b * x.nB + b'))
      (Spec.prunedList (x.EA b) (x.EB b') x.L 0 (x.codes (b * x.nB + b')))














































section Tile

variable (pre : TilesPre lim μ x) (inv : TilesInv x μ β i μ') (hβ : β < x.nB) (hi : i < x.nB)
include pre inv hβ hi













































end Tile





/-! ## One tile -/

variable {P : Program} {c e : ℕ}





































































/-! ## The two loops -/



































































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Pruned_Recursion


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The pruned recursion (Section 2.4.2), recursive as printed

pruned(n, ea, eb, l, len, out, sp, p10).  The set S passed to the call is the increasing list of len
codes at l; ea and eb are the addresses at which the parts of the two encodings below the current
vertex begin; the array that is returned is written to the len cells from out, in the order of the
list.  The frame of a call with n ≥ 1 starts at sp: 11 cells for the bounds of the ten slices, len
cells for the codes without their first digits, len cells for the list of a child, len cells for the
values of a child.

(1) If n = 0: the product of the two numbers looked up, for each code of the list
    (`prunedBody_ends_zero`).
(2) The slices S_z are segments of the list (segBounds); S_λ is the merge of the slice at z_ij and
    the slice at z₀ (`prunedSlice_ends`, then union).
(3) For each term λ with S_λ ≠ ∅: the recursive call.
(4) The slice of the result at z_ij is C_{P_ij} restricted to S_{z_ij} (pick, writing); the slice at
    z₀ is the sum of the ten C_λ restricted to S_{z₀} (pick, adding, after the cells have been
    cleared).  Steps (3) and (4) for one term are `prunedChild_ends`.

One round of the loop over the ten terms is `prunedRound_ends`; the case n ≥ 1 is
`prunedSetup_ends` followed by the loop (`prunedBody_ends_succ`); `PrunedCtx.entry` is the induction
on n.  What the calls do to the memory is proved in Pruned/Memory.lean; here each call is one step.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace PrunedLocal

/-- The number n of levels that are left. -/
abbrev NN : ℕ := 0
/-- Where the part of the first encoding below the current vertex begins. -/
abbrev PA : ℕ := 1
/-- Where the part of the second encoding below the current vertex begins. -/
abbrev PB : ℕ := 2
/-- The list of the codes that are passed to the call. -/
abbrev PL : ℕ := 3
/-- The length of that list. -/
abbrev LEN : ℕ := 4
/-- Where the values are written. -/
abbrev OUT : ℕ := 5
/-- The frame of the call; it begins with the bounds of the ten slices. -/
abbrev SP : ℕ := 6
/-- The table of the powers of ten. -/
abbrev P10 : ℕ := 7
/-- 10^(n-1); for n = 0 the product of the two numbers looked up. -/
abbrev PW : ℕ := 8
/-- Results of calls that are not used. -/
abbrev RES : ℕ := 9
/-- The codes without their first digits. -/
abbrev COD : ℕ := 10
/-- The list of the child. -/
abbrev CH : ℕ := 11
/-- The values of the child. -/
abbrev VAL : ℕ := 12
/-- The frame of the child. -/
abbrev NXT : ℕ := 13
/-- The position of the slice at z₀. -/
abbrev Z0 : ℕ := 14
/-- The length of the slice at z₀. -/
abbrev NZ0 : ℕ := 15
/-- The term λ. -/
abbrev LAM : ℕ := 16
/-- The position of the slice at the output variable of λ. -/
abbrev POS : ℕ := 17
/-- The length of that slice (0 for λ = P₀). -/
abbrev NPOS : ℕ := 18
/-- The length of the list of the child. -/
abbrev NCH : ℕ := 19

end PrunedLocal

open PrunedLocal

/-- Step (2), first half: the position and the length of the slice at the output variable of λ. -/
def prunedSlice : Stmt :=
  (Light.Stmt.seq (.set POS (M ((Light.Expr.op Light.Op.add) (v SP) (v LAM))))
    (.ite (Light.Cond.lt (v LAM) (k 9))
      (.set NPOS
        ((Light.Expr.op Light.Op.sub)
          (M ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v SP) (v LAM)) (k 1))) (v POS)))
      (.set NPOS (k 0))))

/-- Steps (3) and (4) for a term λ with S_λ ≠ ∅. -/
def prunedChild : Stmt :=
  (Light.Stmt.seq
    (.call pPruned
      [(Light.Expr.op Light.Op.sub) (v NN) (k 1),
        (Light.Expr.op Light.Op.add) (v PA) ((Light.Expr.op Light.Op.mul) (v LAM) (v PW)),
        (Light.Expr.op Light.Op.add) (v PB) ((Light.Expr.op Light.Op.mul) (v LAM) (v PW)), v CH, v NCH, v VAL, v NXT,
        v P10]
      RES)
    (Light.Stmt.seq
      (.call pPick
        [(Light.Expr.op Light.Op.add) (v COD) (v POS), v NPOS, v CH, v NCH, v VAL,
          (Light.Expr.op Light.Op.add) (v OUT) (v POS), k 0]
        RES)
      (.call pPick
        [(Light.Expr.op Light.Op.add) (v COD) (v Z0), v NZ0, v CH, v NCH, v VAL,
          (Light.Expr.op Light.Op.add) (v OUT) (v Z0), k 1]
        RES)))

/-- One round of the loop over the ten terms. -/
def prunedRound : Stmt :=
  (Light.Stmt.seq prunedSlice
    (Light.Stmt.seq
      (.call pUnion
        [(Light.Expr.op Light.Op.add) (v COD) (v POS), v NPOS, (Light.Expr.op Light.Op.add) (v COD) (v Z0), v NZ0, v CH]
        NCH)
      (Light.Stmt.seq (.ite (Light.Cond.lt (k 0) (v NCH)) prunedChild .skip)
        (.set LAM ((Light.Expr.op Light.Op.add) (v LAM) (k 1))))))

/-- What a call with n ≥ 1 does before the loop: the slices are found, the parts of the frame get
their addresses, and the cells of the slice at z₀ are cleared. -/
def prunedSetup : Stmt :=
  (Light.Stmt.seq (.set PW (M ((Light.Expr.op Light.Op.add) (v P10) ((Light.Expr.op Light.Op.sub) (v NN) (k 1)))))
    (Light.Stmt.seq (.call pSegBounds [v PL, v LEN, v PW, v SP] RES)
      (Light.Stmt.seq (.set COD ((Light.Expr.op Light.Op.add) (v SP) (k 11)))
        (Light.Stmt.seq (.set CH ((Light.Expr.op Light.Op.add) (v COD) (v LEN)))
          (Light.Stmt.seq (.set VAL ((Light.Expr.op Light.Op.add) (v CH) (v LEN)))
            (Light.Stmt.seq (.set NXT ((Light.Expr.op Light.Op.add) (v VAL) (v LEN)))
              (Light.Stmt.seq (.set Z0 (M ((Light.Expr.op Light.Op.add) (v SP) (k 9))))
                (Light.Stmt.seq (.set NZ0 ((Light.Expr.op Light.Op.sub) (v LEN) (v Z0)))
                  (Light.Stmt.seq (.call pFill [(Light.Expr.op Light.Op.add) (v OUT) (v Z0), v NZ0, k 0] RES)
                    (.set LAM (k 0)))))))))))

/-- pruned(n, ea, eb, l, len, out, sp, p10). -/
def prunedBody : Stmt :=
  .ite ((Light.Cond.eq (v NN) (k 0)))
    ((Light.Stmt.seq (.set PW ((Light.Expr.op Light.Op.mul) (M (v PA)) (M (v PB)))) (.call pFill [v OUT, v LEN, v PW] RES)))
    ((Light.Stmt.seq prunedSetup (.while (Light.Cond.lt (v LAM) (k 10)) prunedRound)))

/-! ## What the proofs assume -/
























variable {lim : Limits} {P : Program} {h d n t : ℕ} {x : PrunedArgs} {μ μ' : ℕ → ℤ}

/-! ## Step (1) -/























/-! ## One round of the loop -/























































































































/-! ## The case n ≥ 1 -/













































































/-! ## The recursion -/











end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Pruned_Restrict


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Restricting an array on a set of codes to a subset (step (4) of Pruned, Section 2.4.2)

pick walks once through an increasing list of codes (big), which has a value for each of its codes,
and through an increasing list of some of these codes (small).  It writes the values of the codes of
the second list, or adds them to what is there.

* The lists.  `PickInv` says where the walk stands.  If the two heads agree, the value is taken and
  both lists advance (`PickInv.hit`); if not, the head of the large list is skipped
  (`PickInv.miss`).
* The memory.  `PickMem` says which cells of the destination are finished; `PickMem.write` finishes
  one more.
* The program.  `pickTake_ends` treats the round in which a value is taken, `pickBody_ends` the
  loop, for both modes.  `pickSet_entry` and `pickAdd_entry` are the results for the callers: a call
  of procedure `pPick` does what `PickSetSpec` (writing) or `PickAddSpec` (adding) says, in at most
  `cPick` steps for each entry of the two lists.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The program -/

namespace PickLocal

/-- The small list. -/
abbrev PSUB : ℕ := 0
/-- The length of the small list. -/
abbrev NSUB : ℕ := 1
/-- The large list. -/
abbrev PU : ℕ := 2
/-- The values of the codes of the large list. -/
abbrev PVAL : ℕ := 4
/-- The destination. -/
abbrev PDST : ℕ := 5
/-- The mode: 0 for writing, otherwise adding. -/
abbrev ADD : ℕ := 6
/-- The position i in the small list. -/
abbrev CI : ℕ := 7
/-- The position j in the large list. -/
abbrev CJ : ℕ := 8

end PickLocal

open PickLocal

/-- The two heads agree: the value is written or added, and both lists advance. -/
def pickTake : Stmt :=
  (Light.Stmt.seq
    (.ite (Light.Cond.eq (v ADD) (k 0))
      (.store ((Light.Expr.op Light.Op.add) (v PDST) (v CI)) (M ((Light.Expr.op Light.Op.add) (v PVAL) (v CJ))))
      (.store ((Light.Expr.op Light.Op.add) (v PDST) (v CI))
        ((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v PDST) (v CI)))
          (M ((Light.Expr.op Light.Op.add) (v PVAL) (v CJ))))))
    (Light.Stmt.seq (.set CI ((Light.Expr.op Light.Op.add) (v CI) (k 1)))
      (.set CJ ((Light.Expr.op Light.Op.add) (v CJ) (k 1)))))

/-- pick(pSub, nSub, pU, nU, pVal, pDst, add).  The length nU of the large list, local 3, is not
read: the large list cannot end before the small one. -/
def pickBody : Stmt :=
  (Light.Stmt.seq (.set CI (k 0))
    (Light.Stmt.seq (.set CJ (k 0))
      (.while (Light.Cond.lt (v CI) (v NSUB))
        (.ite
          (Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v PU) (v CJ)))
            (M ((Light.Expr.op Light.Op.add) (v PSUB) (v CI))))
          pickTake (.set CJ ((Light.Expr.op Light.Op.add) (v CJ) (k 1)))))))




/-! ## The lists -/

section Lists

variable {big small : List ℕ} {vals : List ℤ} {i j : ℕ}



























































































end Lists

/-! ## The memory -/

variable {lim : Limits} {P : Program} {d pDst add i j n : ℕ} {res : List ℤ} {μ μ' : ℕ → ℤ}
  {x : PickArgs}














































/-! ## The walk -/



































































































/-! ## The two results for the callers -/

































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Pruned_Slices


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Cutting an increasing list of codes into its ten slices (step (2) of Pruned, Section 2.4.2)

segBounds goes once through an increasing list of codes of n + 1 digits.  The codes with first digit
z are consecutive; it notes where they start, and writes every code without its first digit.

* The list.  `SegInv` says where the pass stands: i codes are copied, z is the current first digit,
  and lo = z 10^n.  A code below lo + 10^n is copied (`SegInv.copy`); otherwise the pass goes on to
  the next first digit (`SegInv.advance`), and the position reached is the start of the next slice
  (`SegInv.segStart_succ`).
* The memory.  `SegMem` says what has been written, `SegMem.copy` and `SegMem.advance` what a round
  adds, and `SegMem.slices` that in the end the ten slices stand in the memory.
* The program.  `segCopy_ends` and `segAdvance_ends` treat the two kinds of rounds, and
  `segBounds_entry` the loop.  The result: a call takes at most `cSegBounds` steps for each code and
  each of the eleven bounds; afterwards the cells bnd to bnd + 10 hold the starts of the slices, the
  slice at z stands at bnd + 11 + segStart n codes z, and no other cell has changed.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The program -/

namespace SegLocal

/-- The list of the codes. -/
abbrev PL : ℕ := 0
/-- The length of the list. -/
abbrev LEN : ℕ := 1
/-- 10^n. -/
abbrev PW : ℕ := 2
/-- Where the bounds are written; the codes without first digits follow 11 cells later. -/
abbrev BND : ℕ := 3
/-- The position i in the list. -/
abbrev CI : ℕ := 4
/-- The first digit z. -/
abbrev CZ : ℕ := 5
/-- z 10^n. -/
abbrev LO : ℕ := 6
/-- (z + 1) 10^n. -/
abbrev HI : ℕ := 7

end SegLocal

open SegLocal

/-- The code at position i has first digit z: it is written without that digit. -/
def segCopy : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v BND) (k 11)) (v CI))
      ((Light.Expr.op Light.Op.sub) (M ((Light.Expr.op Light.Op.add) (v PL) (v CI))) (v LO)))
    (.set CI ((Light.Expr.op Light.Op.add) (v CI) (k 1))))

/-- The next first digit: z := z + 1, the position reached is noted at bnd + z, and the two
thresholds move up. -/
def segAdvance : Stmt :=
  (Light.Stmt.seq (.set CZ ((Light.Expr.op Light.Op.add) (v CZ) (k 1)))
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v BND) (v CZ)) (v CI))
      (Light.Stmt.seq (.set LO (v HI)) (.set HI ((Light.Expr.op Light.Op.add) (v HI) (v PW))))))

/-- segBounds(l, len, pw, bnd). -/
def segBoundsBody : Stmt :=
  (Light.Stmt.seq (.set CI (k 0))
    (Light.Stmt.seq (.set CZ (k 0))
      (Light.Stmt.seq (.set LO (k 0))
        (Light.Stmt.seq (.set HI (v PW))
          (Light.Stmt.seq (.store (v BND) (k 0))
            (.while (Light.Cond.lt (v CZ) (k 10))
              (.ite (Light.Cond.lt (v CI) (v LEN))
                (.ite (Light.Cond.lt (M ((Light.Expr.op Light.Op.add) (v PL) (v CI))) (v HI)) segCopy segAdvance)
                segAdvance)))))))




/-! ## The list -/






























































variable {n pw l bnd i z lo : ℕ} {codes : List ℕ} {μ μ' : ℕ → ℤ}







































/-! ## The memory -/











































/-! ## The pass -/

variable {lim : Limits} {P : Program} {d : ℕ}





















































































































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Pruned_Union


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The merge of two lists (Section 2.4.4: "a union of slices is a merge")

union(pa, na, pb, nb, pc) writes the merge of the list of na numbers at pa and the list of nb
numbers at pb to pc, a number that heads both lists being taken once, and returns its length.  The
program follows Spec.mergeUnion step by step.

union_entry shows that a call does this in at most 70 (na + nb + 1) steps and changes no cell
outside the output.  Both loops keep UnionInv.  What writing one number does to the data is
union_emit.  The three bodies are unionBoth_ends, unionLeft_ends and unionRight_ends, and
union_entry treats the two loops.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace UnionLocal

/-- The first list, A in the comments of the proofs. -/
abbrev ListA : ℕ := 0
/-- The length na of the first list. -/
abbrev LenA : ℕ := 1
/-- The second list, B in the comments of the proofs. -/
abbrev ListB : ℕ := 2
/-- The length nb of the second list. -/
abbrev LenB : ℕ := 3
/-- Where the merge is written, C in the comments of the proofs. -/
abbrev Dest : ℕ := 4
/-- The number i of entries taken from the first list. -/
abbrev TakenA : ℕ := 5
/-- The number j of entries taken from the second list. -/
abbrev TakenB : ℕ := 6
/-- The number len of entries written. -/
abbrev Written : ℕ := 7
/-- The head a of what is left of the first list. -/
abbrev HeadA : ℕ := 8
/-- The head b of what is left of the second list. -/
abbrev HeadB : ℕ := 9

end UnionLocal

open UnionLocal

/-- Both lists have a head: the smaller one is written and its list advances; if they are equal, the
number is written once and both lists advance. -/
def unionBoth : Stmt :=
  (Light.Stmt.seq (.set HeadA (M ((Light.Expr.op Light.Op.add) (v ListA) (v TakenA))))
    (Light.Stmt.seq (.set HeadB (M ((Light.Expr.op Light.Op.add) (v ListB) (v TakenB))))
      (.ite (Light.Cond.lt (v HeadA) (v HeadB))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Written)) (v HeadA))
          (Light.Stmt.seq (.set TakenA ((Light.Expr.op Light.Op.add) (v TakenA) (k 1)))
            (.set Written ((Light.Expr.op Light.Op.add) (v Written) (k 1)))))
        (.ite (Light.Cond.lt (v HeadB) (v HeadA))
          (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Written)) (v HeadB))
            (Light.Stmt.seq (.set TakenB ((Light.Expr.op Light.Op.add) (v TakenB) (k 1)))
              (.set Written ((Light.Expr.op Light.Op.add) (v Written) (k 1)))))
          (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Written)) (v HeadA))
            (Light.Stmt.seq (.set TakenA ((Light.Expr.op Light.Op.add) (v TakenA) (k 1)))
              (Light.Stmt.seq (.set TakenB ((Light.Expr.op Light.Op.add) (v TakenB) (k 1)))
                (.set Written ((Light.Expr.op Light.Op.add) (v Written) (k 1))))))))))

/-- The head of the first list is written. -/
def unionLeft : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Written)) (M ((Light.Expr.op Light.Op.add) (v ListA) (v TakenA))))
    (Light.Stmt.seq (.set TakenA ((Light.Expr.op Light.Op.add) (v TakenA) (k 1)))
      (.set Written ((Light.Expr.op Light.Op.add) (v Written) (k 1)))))

/-- The head of the second list is written. -/
def unionRight : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Written)) (M ((Light.Expr.op Light.Op.add) (v ListB) (v TakenB))))
    (Light.Stmt.seq (.set TakenB ((Light.Expr.op Light.Op.add) (v TakenB) (k 1)))
      (.set Written ((Light.Expr.op Light.Op.add) (v Written) (k 1)))))

/-- union(pa, na, pb, nb, pc); it returns len. -/
def unionBody : Stmt :=
  (Light.Stmt.seq
    (.while (Light.Cond.lt (v TakenA) (v LenA)) (.ite (Light.Cond.lt (v TakenB) (v LenB)) unionBoth unionLeft))
    (Light.Stmt.seq (.while (Light.Cond.lt (v TakenB) (v LenB)) unionRight) (.set 0 (v Written))))

/-! ## The invariant -/





































variable {μ μ' : ℕ → ℤ} {pa pb pc : ℕ} {la lb : List ℕ} {i j : ℕ} {done : List ℕ}


































/-! ## The three bodies -/









































































/-! ## The procedure -/












































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_SharedStage


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The shared stage: everything up to the encodings of all bands

shared(L, m, N, D, aX, aY, b0) fills the shared block of the memory map: the tables of powers, the
coefficients φ and ψ of Schönhage's identity (Section 2.2), the table of the K₀² subsets (Section
2.3.4), band, block and digits of every row, the digits of every column, the encodings of all row
bands of X and of all column bands of Y (Section 2.4.1), and the directory. Theorem 5 and the data
structure of Section 4 both start with it.

The body is a straight line of 36 statements and the 31 stores of the directory. It is cut into
three parts (sharedA, sharedB, sharedC). For each part there are two lemmas: one runs the text
(sharedA_spec, sharedB_spec, sharedC_spec), and one, about memories only, says that what the calls
have written is all there at the end, because each call writes above the areas of the calls before
it (SharedA.of_calls, SharedB.of_calls, SharedReady.of_calls). shared_entry puts the parts together:
if every callee meets its entry with the constant c, then shared runs within 12 c + 600 times
sharedShape (sharedTime_le). The places of the areas are those of Par.places, and their sizes those
of Par.sizes.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

/-! ## The local variables -/

namespace Shared

/-- Local 0 of shared: L. -/
abbrev Levels : ℕ := 0
/-- Local 1 of shared: m. -/
abbrev Inner : ℕ := 1
/-- Local 2 of shared: N. -/
abbrev Rows : ℕ := 2
/-- Local 3 of shared: D. -/
abbrev Cols : ℕ := 3
/-- Local 4 of shared: the address of X. -/
abbrev AdrX : ℕ := 4
/-- Local 5 of shared: the address of Y. -/
abbrev AdrY : ℕ := 5
/-- Local 6 of shared: the base address b0 of the block. -/
abbrev Base : ℕ := 6
/-- Local 7 of shared: the address of the powers of 3. -/
abbrev AdrP3 : ℕ := 7
/-- Local 8 of shared: the address of the powers of 4. -/
abbrev AdrP4 : ℕ := 8
/-- Local 9 of shared: the address of the powers of 7. -/
abbrev AdrP7 : ℕ := 9
/-- Local 10 of shared: the address of the powers of 10. -/
abbrev AdrP10 : ℕ := 10
/-- Local 11 of shared: the address of the scratch row of Pascal's triangle. -/
abbrev AdrPas : ℕ := 11
/-- Local 12 of shared: the address of the coefficients φ. -/
abbrev AdrPhi : ℕ := 12
/-- Local 13 of shared: the address of the coefficients ψ. -/
abbrev AdrPsi : ℕ := 13
/-- Local 14 of shared: the address of the table of subsets. -/
abbrev AdrMask : ℕ := 14
/-- Local 15 of shared: the address of the bands of the rows. -/
abbrev AdrBand : ℕ := 15
/-- Local 16 of shared: the address of the blocks of the rows. -/
abbrev AdrBlock : ℕ := 16
/-- Local 17 of shared: the address of the base-3 digits. -/
abbrev AdrDig3 : ℕ := 17
/-- Local 18 of shared: the address of the base-4 digits. -/
abbrev AdrDig4 : ℕ := 18
/-- Local 19 of shared: the address of the encodings of the row bands. -/
abbrev AdrEncA : ℕ := 19
/-- Local 20 of shared: the address of the encodings of the column bands. -/
abbrev AdrEncB : ℕ := 20
/-- Local 21 of shared: the address of the input array of a band. -/
abbrev AdrArr : ℕ := 21
/-- Local 22 of shared: the address of the scratch array of encode. -/
abbrev AdrZs : ℕ := 22
/-- Local 23 of shared: the end of the block. -/
abbrev AdrEnd : ℕ := 23
/-- Local 24 of shared: L - m. -/
abbrev Outer : ℕ := 24
/-- Local 25 of shared: N₀. -/
abbrev BlockRows : ℕ := 25
/-- Local 26 of shared: K. -/
abbrev Subsets : ℕ := 26
/-- Local 27 of shared: K₀. -/
abbrev Root : ℕ := 27
/-- Local 28 of shared: K₀². -/
abbrev Table : ℕ := 28
/-- Local 29 of shared: the number of bands. -/
abbrev Bands : ℕ := 29
/-- Local 30 of shared: 10^L. -/
abbrev Leaves : ℕ := 30
/-- Local 31 of shared: 7^L. -/
abbrev Strings : ℕ := 31
/-- Local 32 of shared: takes the results of calls that return nothing. -/
abbrev Void : ℕ := 32

end Shared

open Shared

/-! ## The text -/

/-- Stores the locals of the list xs into the cells from b0 + i on. -/
def storeLocals : ℕ → List ℕ → Stmt
  | _, [] => .skip
  | i, x :: xs => (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Base) (k i)) (v x)) (storeLocals (i + 1) xs))
























/-- The first part of shared: the addresses of the first areas, the four tables of powers, and
L - m, N₀, 10^L, 7^L. -/
def sharedA : Stmt :=
  (Light.Stmt.seq (.set AdrP3 ((Light.Expr.op Light.Op.add) (v Base) (k 32)))
    (Light.Stmt.seq (.set AdrP4 ((Light.Expr.op Light.Op.add) (v AdrP3) ((Light.Expr.op Light.Op.add) (v Levels) (k 1))))
      (Light.Stmt.seq
        (.set AdrP7 ((Light.Expr.op Light.Op.add) (v AdrP4) ((Light.Expr.op Light.Op.add) (v Levels) (k 1))))
        (Light.Stmt.seq
          (.set AdrP10 ((Light.Expr.op Light.Op.add) (v AdrP7) ((Light.Expr.op Light.Op.add) (v Levels) (k 1))))
          (Light.Stmt.seq
            (.set AdrPas ((Light.Expr.op Light.Op.add) (v AdrP10) ((Light.Expr.op Light.Op.add) (v Levels) (k 1))))
            (Light.Stmt.seq
              (.set AdrPhi ((Light.Expr.op Light.Op.add) (v AdrPas) ((Light.Expr.op Light.Op.add) (v Levels) (k 2))))
              (Light.Stmt.seq (.set AdrPsi ((Light.Expr.op Light.Op.add) (v AdrPhi) (k 70)))
                (Light.Stmt.seq (.set AdrMask ((Light.Expr.op Light.Op.add) (v AdrPsi) (k 70)))
                  (Light.Stmt.seq (.call pPow [k 3, v Levels, v AdrP3] Void)
                    (Light.Stmt.seq (.call pPow [k 4, v Levels, v AdrP4] Void)
                      (Light.Stmt.seq (.call pPow [k 7, v Levels, v AdrP7] Void)
                        (Light.Stmt.seq (.call pPow [k 10, v Levels, v AdrP10] Void)
                          (Light.Stmt.seq (.set Outer ((Light.Expr.op Light.Op.sub) (v Levels) (v Inner)))
                            (Light.Stmt.seq (.set BlockRows (M ((Light.Expr.op Light.Op.add) (v AdrP3) (v Outer))))
                              (Light.Stmt.seq (.set Leaves (M ((Light.Expr.op Light.Op.add) (v AdrP10) (v Levels))))
                                (Light.Stmt.seq (.set Strings (M ((Light.Expr.op Light.Op.add) (v AdrP7) (v Levels))))
                                  .skip))))))))))))))))

/-- The second part of shared: K, K₀, K₀², the coefficients, the table of subsets, band, block and
digits of every row, the digits of every column. -/
def sharedB : Stmt :=
  (Light.Stmt.seq (.call pBinom [v Levels, v Inner, v AdrPas] Subsets)
    (Light.Stmt.seq (.call pSqrt [v Subsets] Root)
      (Light.Stmt.seq (.set Table ((Light.Expr.op Light.Op.mul) (v Root) (v Root)))
        (Light.Stmt.seq (.call pCoef [v AdrPhi] Void)
          (Light.Stmt.seq (.call pSubsets [v Levels, v Inner, v Table, v AdrMask] Void)
            (Light.Stmt.seq
              (.set AdrBand
                ((Light.Expr.op Light.Op.add) (v AdrMask) ((Light.Expr.op Light.Op.mul) (v Table) (v Levels))))
              (Light.Stmt.seq (.set AdrBlock ((Light.Expr.op Light.Op.add) (v AdrBand) (v Rows)))
                (Light.Stmt.seq (.set AdrDig3 ((Light.Expr.op Light.Op.add) (v AdrBlock) (v Rows)))
                  (Light.Stmt.seq (.call pCounters [v Rows, v Root, v BlockRows, v AdrBand] Void)
                    (Light.Stmt.seq (.call pDigits [v Rows, k 3, v Outer, v AdrDig3] Void)
                      (Light.Stmt.seq
                        (.set AdrDig4
                          ((Light.Expr.op Light.Op.add) (v AdrDig3) ((Light.Expr.op Light.Op.mul) (v Rows) (v Outer))))
                        (Light.Stmt.seq (.call pDigits [v Cols, k 4, v Inner, v AdrDig4] Void)
                          (Light.Stmt.seq
                            (.set AdrEncA
                              ((Light.Expr.op Light.Op.add) (v AdrDig4)
                                ((Light.Expr.op Light.Op.mul) (v Cols) (v Inner))))
                            .skip)))))))))))))

/-- The number of bands: 0 if there is no row, and else one more than the band of the last row. -/
def sharedBands : Stmt :=
  .ite ((Light.Cond.eq (v Rows) (k 0))) (.set Bands (k 0)) (.set Bands (((Light.Expr.op Light.Op.add)
                                                         (M ((Light.Expr.op Light.Op.add) (v AdrBand) ((Light.Expr.op Light.Op.sub) (v Rows) (k 1)))) (k 1))))

/-- The third part of shared: the number of bands, the last addresses, the encodings of all bands,
and the directory. -/
def sharedC : Stmt :=
  (Light.Stmt.seq sharedBands
    (Light.Stmt.seq
      (.set AdrEncB ((Light.Expr.op Light.Op.add) (v AdrEncA) ((Light.Expr.op Light.Op.mul) (v Bands) (v Leaves))))
      (Light.Stmt.seq
        (.set AdrArr ((Light.Expr.op Light.Op.add) (v AdrEncB) ((Light.Expr.op Light.Op.mul) (v Bands) (v Leaves))))
        (Light.Stmt.seq (.set AdrZs ((Light.Expr.op Light.Op.add) (v AdrArr) (v Strings)))
          (Light.Stmt.seq (.set AdrEnd ((Light.Expr.op Light.Op.add) (v AdrZs) (v Strings)))
            (Light.Stmt.seq
              (.call pEncodeBands
                [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings, v Leaves, v Bands, k 0, v AdrX,
                  v Cols, k 1, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v AdrPhi, v AdrP7, v AdrP10, v AdrEncA]
                Void)
              (Light.Stmt.seq
                (.call pEncodeBands
                  [v Levels, v Inner, v Rows, v Cols, v Root, v BlockRows, v Strings, v Leaves, v Bands, k 1, v AdrY, k 1,
                    v Rows, v AdrMask, v AdrDig3, v AdrDig4, v AdrArr, v AdrZs, v AdrPsi, v AdrP7, v AdrP10, v AdrEncB]
                  Void)
                (storeLocals 0
                  [Levels, Inner, Rows, Cols, Outer, BlockRows, Subsets, Root, Table, Bands, Leaves, Strings, AdrX, AdrY,
                    AdrP3, AdrP4, AdrP7, AdrP10, AdrPas, AdrPhi, AdrPsi, AdrMask, AdrBand, AdrBlock, AdrDig3, AdrDig4,
                    AdrEncA, AdrEncB, AdrArr, AdrZs, AdrEnd]))))))))

/-- shared(L, m, N, D, aX, aY, b0). -/
def sharedBody : Stmt := (Light.Stmt.seq sharedA (Light.Stmt.seq sharedB sharedC))

/-- The time of the first part, if every callee meets its entry with the constant c. -/
def sharedTimeA (c : ℕ) (p : Par) : ℕ := 4 * (c * (p.L + 1)) + 81

/-- The time of the second part. -/
def sharedTimeB (c : ℕ) (p : Par) : ℕ :=
  c * (p.L + 1) ^ 2 + c * (Nat.sqrt p.K + 1) + c + c * ((p.KK + 1) * (p.L + 1)) + c * (p.N + 1)
    + c * ((p.N + 1) * (p.Lo + 1)) + c * ((p.D + 1) * (p.m + 1)) + 65

/-- The time of the third part. -/
def sharedTimeC (c : ℕ) (p : Par) : ℕ := 2 * (c * (p.nB * (p.T + bandArrayShape p) + 1)) + 236

/-- The locals at the start: the arguments, then zeros. -/
def sharedLoc0 (p : Par) (aX aY b0 : ℕ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals after the first part; r is what the last call left in local 32. -/
def sharedLocA (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), (p.aP3 b0 : ℤ),
    (p.aP4 b0 : ℤ), (p.aP7 b0 : ℤ), (p.aP10 b0 : ℤ), (p.aPAS b0 : ℤ), (p.aPHI b0 : ℤ),
    (p.aPSI b0 : ℤ), (p.aMASK b0 : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, (p.Lo : ℤ), (p.N0 : ℤ), 0, 0, 0,
    0, (p.T : ℤ), (p.S7 : ℤ), r]

/-- The locals after the second part. -/
def sharedLocB (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [(p.L : ℤ), (p.m : ℤ), (p.N : ℤ), (p.D : ℤ), (aX : ℤ), (aY : ℤ), (b0 : ℤ), (p.aP3 b0 : ℤ),
    (p.aP4 b0 : ℤ), (p.aP7 b0 : ℤ), (p.aP10 b0 : ℤ), (p.aPAS b0 : ℤ), (p.aPHI b0 : ℤ),
    (p.aPSI b0 : ℤ), (p.aMASK b0 : ℤ), (p.aBAND b0 : ℤ), (p.aBLOCK b0 : ℤ), (p.aDIG3 b0 : ℤ),
    (p.aDIG4 b0 : ℤ), (p.aENCA b0 : ℤ), 0, 0, 0, 0, (p.Lo : ℤ), (p.N0 : ℤ), (p.K : ℤ), (p.K0 : ℤ),
    (p.KK : ℤ), 0, (p.T : ℤ), (p.S7 : ℤ), r]

/-- What the first part leaves in the memory. -/
structure SharedA (p : Par) (b0 : ℕ) (μ μ' : ℕ → ℤ) : Prop extends PowTables p b0 μ' where
  same : SameOutside μ μ' (p.aP3 b0) (p.aPAS b0 - p.aP3 b0)

/-- What the second part leaves in the memory. -/
structure SharedB (p : Par) (b0 : ℕ) (μ μ' : ℕ → ℤ) : Prop extends RowTables p b0 μ' where
  same : SameOutside μ μ' (p.aPAS b0) (p.aENCA b0 - p.aPAS b0)

/-- The entries of the routines that the shared stage calls, with their constants. -/
structure SharedCallees (lim : Limits) (P : Program) (c : ℕ) : Prop where
  pow : PowSpec lim P c
  binom : BinomSpec lim P c
  sqrt : SqrtSpec lim P c
  coef : CoefSpec lim P c
  subsets : SubsetsSpec lim P c
  counters : CountersSpec lim P c
  digits : DigitsSpec lim P c
  bandsL : EncodeBandsLSpec lim P c
  bandsR : EncodeBandsRSpec lim P c



















































































































































































/-- The addresses that the shared stage hands to encodeBands: the coefficients stand at tab, and the
encodings are written from enc on. -/
@[simp] def Par.bandsArgs (p : Par) (b0 tab enc : ℕ) : BandsArgs where
  mask := p.aMASK b0
  dig3 := p.aDIG3 b0
  dig4 := p.aDIG4 b0
  arr := p.aARR b0
  zs := p.aZS b0
  tab := tab
  p7 := p.aP7 b0
  p10 := p.aP10 b0
  enc := enc








































































































































































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Stages


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 5: the solver, stage by stage

The text of the solver after the search for m ("The algorithm", Section 2.4.4), cut into six parts:
the shared stage; tiles, codes and digits of the wanted positions (the code of a position is its
output string, read as a number); the sort; the codes in sorted order; the pruned recursions; the
report. There is one lemma for each part together with everything that follows it (fromShared_ends
to reportCall_ends), so that each lemma ends with the lemma of the next part. The lemmas are stated
for arbitrary parameters p, matrices X, Y and positions (I i, J i) (WantedJob). The result is
fromShared_ends: from the state after the search for m the solver ends within timeFromShared steps,
with the entries of XY at the w wanted positions in the cells from out on, and nothing else below
the free pointer changed (Reported).

Every stage writes above everything that the stages before it have written, except the report, which
writes the output. So each lemma hands on what the earlier stages have left, in a memory that agrees
with the earlier one below the area just written.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

open ThreeSumApsp.Spec

/-! ## The local variables and the cells of the directory -/

namespace Solver

/-- Local 10 of the solver: m. -/
abbrev Expo : ℕ := 10
/-- Local 11 of the solver: a power of four. -/
abbrev Pow4 : ℕ := 11
/-- Local 12 of the solver: L = 19 m. -/
abbrev Levels : ℕ := 12
/-- Local 13 of the solver: takes the results of the calls. -/
abbrev Void : ℕ := 13
/-- Local 14 of the solver: the address of TID. -/
abbrev AdrTid : ℕ := 14
/-- Local 16 of the solver: the number of bands. -/
abbrev Bands : ℕ := 16
/-- Local 22 of the solver: the address of PERM. -/
abbrev AdrPerm : ℕ := 22
/-- Local 23 of the solver: the number of tiles. -/
abbrev Tiles : ℕ := 23
/-- Local 26 of the solver: the address of SC. -/
abbrev AdrSc : ℕ := 26

/-- Cell 4 of the directory: L - m. -/
abbrev DirOuter : ℕ := 4
/-- Cell 7 of the directory: K₀. -/
abbrev DirRoot : ℕ := 7
/-- Cell 9 of the directory: the number of bands. -/
abbrev DirBands : ℕ := 9
/-- Cell 10 of the directory: 10^L. -/
abbrev DirLeaves : ℕ := 10
/-- Cell 17 of the directory: the address of the powers of ten. -/
abbrev DirP10 : ℕ := 17
/-- Cell 21 of the directory: the address of the table of subsets. -/
abbrev DirMask : ℕ := 21
/-- Cell 22 of the directory: the address of the bands of the rows. -/
abbrev DirBand : ℕ := 22
/-- Cell 24 of the directory: the address of the base-3 digits. -/
abbrev DirDig3 : ℕ := 24
/-- Cell 26 of the directory: the address of the encodings of the row bands. -/
abbrev DirEncA : ℕ := 26
/-- Cell 27 of the directory: the address of the encodings of the column bands. -/
abbrev DirEncB : ℕ := 27
/-- Cell 30 of the directory: the end of the shared block. -/
abbrev DirEnd : ℕ := 30

end Solver

open ThinArg Solver

/-! ## The text -/

/-- The report. -/
def reportCall : Stmt :=
  .call pReport [v Wanted, v AdrPerm, ((Light.Expr.op Light.Op.add) (v AdrSc) (v Wanted)), v AdrOut] Void

/-- The pruned recursions, and what follows. -/
def fromTiles : Stmt :=
  (Light.Stmt.seq
    (.call pRunTiles
      [v Bands, v Levels, M ((Light.Expr.op Light.Op.add) (v Free) (k DirLeaves)),
        M ((Light.Expr.op Light.Op.add) (v Free) (k DirEncA)), M ((Light.Expr.op Light.Op.add) (v Free) (k DirEncB)),
        (Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v AdrPerm) (v Wanted)) (v Wanted)) (v Tiles))
          (k 11),
        v AdrSc, (Light.Expr.op Light.Op.add) (v AdrSc) (v Wanted),
        (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v AdrSc) (v Wanted)) (v Wanted),
        M ((Light.Expr.op Light.Op.add) (v Free) (k DirP10))]
      Void)
    reportCall)

/-- The codes in sorted order, and what follows. -/
def fromGather : Stmt :=
  (Light.Stmt.seq
    (.set AdrSc
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v AdrPerm) (v Wanted)) (v Wanted)) (v Tiles))
            (k 11))
          (v Tiles))
        (k 1)))
    (Light.Stmt.seq
      (.call pGather [v Wanted, v AdrPerm, (Light.Expr.op Light.Op.add) (v AdrTid) (v Wanted), v AdrSc] Void) fromTiles))

/-- The sort, and what follows. -/
def fromSort : Stmt :=
  (Light.Stmt.seq
    (.set AdrPerm
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v AdrTid) (v Wanted)) (v Wanted))
        ((Light.Expr.op Light.Op.mul) (v Wanted) (v Levels))))
    (Light.Stmt.seq (.set Tiles ((Light.Expr.op Light.Op.mul) (v Bands) (v Bands)))
      (Light.Stmt.seq
        (.call pSortWanted
          [v Wanted, v Levels, v Tiles, v AdrTid,
            (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v AdrTid) (v Wanted)) (v Wanted), v AdrPerm]
          Void)
        fromGather)))

/-- Tiles, codes and digits of the wanted positions, and what follows. -/
def fromWanted : Stmt :=
  (Light.Stmt.seq (.set AdrTid (M ((Light.Expr.op Light.Op.add) (v Free) (k DirEnd))))
    (Light.Stmt.seq (.set Bands (M ((Light.Expr.op Light.Op.add) (v Free) (k DirBands))))
      (Light.Stmt.seq
        (.call pWanted
          [v Wanted, v Levels, M ((Light.Expr.op Light.Op.add) (v Free) (k DirOuter)), v Rows,
            M ((Light.Expr.op Light.Op.add) (v Free) (k DirRoot)), v Bands, v AdrWI, v AdrWJ,
            M ((Light.Expr.op Light.Op.add) (v Free) (k DirBand)), M ((Light.Expr.op Light.Op.add) (v Free) (k DirDig3)),
            M ((Light.Expr.op Light.Op.add) (v Free) (k DirMask)), v AdrTid]
          Void)
        fromSort)))

/-- The shared stage, and what follows. -/
def fromShared : Stmt :=
  (Light.Stmt.seq (.set Levels ((Light.Expr.op Light.Op.mul) (k 19) (v Expo)))
    (Light.Stmt.seq (.call pShared [v Levels, v Expo, v Rows, v Cols, v AdrX, v AdrY, v Free] Void) fromWanted))























































/-! ## The times: each stage with everything that follows it -/

















variable {lim : Limits} {P : Program} {c d : ℕ} {p : Par} {hmL : p.m ≤ p.L}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {w : ℕ}
  {u e1 e11 : ℤ} {ax ay wi wj out fr : ℕ} {A : ℤ} {I J : ℕ → ℕ} {V : ℕ → ℤ} {μ : ℕ → ℤ}

/-! ## The report -/






























/-! ## The pruned recursions -/
























































































/-! ## The codes in sorted order -/






























/-! ## The sort -/












































/-! ## Tiles, codes and digits of the wanted positions -/












































/-! ## The shared stage -/

























end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Solver


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5: the solver

thm5(N, D, w, U, x, y, wi, wj, out, fr) is the algorithm of Section 2.4.4: find m with D = 4^m; the
shared stage (tables, encodings of all row bands and column bands); the tile, the output string and
its digits for every wanted position; the sort by tile and string; the strings in sorted order; the
pruned recursion on every tile that has a wanted position; the report.  The work area begins at the
free pointer fr.

The result is thm5_spec: on an instance of the thin matrix product in the regime of Theorem 5, the
wanted entries of XY end up in the cells from out on, nothing else below fr changes, and the run
takes at most 2 c + 100 times thm5Shape steps, where c is the constant with which the called
procedures meet their entries.  findM_spec treats the search for m; everything after it is
fromShared_ends, which is stated for arbitrary parameters.  tilesShape_le gives the shape of the
time of the pruned recursions, whatever the sorting permutation, and thm5_time compares the sum of
the times with the shape.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

open ThinArg Solver

/-- The search for m with D = 4^m. -/
def findM : Stmt :=
  .while ((Light.Cond.lt (v Pow4) (v Cols))) (
    (Light.Stmt.seq (.set Pow4 ((Light.Expr.op Light.Op.mul) (v Pow4) (k 4)))
      (.set Expo ((Light.Expr.op Light.Op.add) (v Expo) (k 1)))))

/-- thm5(N, D, w, U, x, y, wi, wj, out, fr): the search for m, then the six stages.  Locals 0 to 9
are the arguments.  Everything that is not in a local is read from the directory, which the shared
stage leaves in the 32 cells from fr on. -/
def thm5Body : Stmt :=
  (Light.Stmt.seq (.set Pow4 (k 1)) (Light.Stmt.seq findM fromShared))


















variable {lim : Limits} {P : Program} {c d : ℕ}







































































































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Tables_BandCounters


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Band and block of every row, by counting (Section 2.3.4)

Section 2.3.4 cuts the N rows of X into bands of K₀ blocks of N₀ rows.  counters(N, K0, N0, dst)
writes, for every row I < N, its band I / (K0 N0) to the cell dst + I and its block I / N0 % K0 to
the cell dst + N + I.  There is no division: three counters (band, block, offset) are stepped from
each row to the next, as `Spec.stepCtr` says, and `Spec.ctrAt_succ` says that they are the
quotients and remainders.

A round writes two cells (`Counted.step`) and steps the counters (`countersRound_spec`);
`counters_spec` runs through the rows, and `counters_entry` is the specification that the callers of
the procedure assume.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Counters

/-- The local variables of counters: Total = N, Blocks = K0, Width = N0, Dest = dst (the arguments);
Row is the current row, and Band, Block, Offset are its band, its block and its offset. -/
abbrev Total : ℕ := 0
@[inherit_doc Total] abbrev Blocks : ℕ := 1
@[inherit_doc Total] abbrev Width : ℕ := 2
@[inherit_doc Total] abbrev Dest : ℕ := 3
@[inherit_doc Total] abbrev Row : ℕ := 4
@[inherit_doc Total] abbrev Band : ℕ := 5
@[inherit_doc Total] abbrev Block : ℕ := 6
@[inherit_doc Total] abbrev Offset : ℕ := 7

end Counters

open Counters in
/-- One round: the band and the block of the current row are written, and the counters move on to
the next row. -/
def countersRound : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Row)) (v Band))
    (Light.Stmt.seq
      (.store ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Dest) (v Total)) (v Row)) (v Block))
      (Light.Stmt.seq (.set Row ((Light.Expr.op Light.Op.add) (v Row) (k 1)))
        (Light.Stmt.seq (.set Offset ((Light.Expr.op Light.Op.add) (v Offset) (k 1)))
          (.ite (Light.Cond.lt (v Offset) (v Width)) .skip
            (Light.Stmt.seq (.set Offset (k 0))
              (Light.Stmt.seq (.set Block ((Light.Expr.op Light.Op.add) (v Block) (k 1)))
                (.ite (Light.Cond.lt (v Block) (v Blocks)) .skip
                  (Light.Stmt.seq (.set Block (k 0)) (.set Band ((Light.Expr.op Light.Op.add) (v Band) (k 1))))))))))))

open Counters in
/-- counters(N, K0, N0, dst).  The row and the three counters are not set at the beginning: local
variables that are not arguments start at 0. -/
def countersBody : Stmt := .while ((Light.Cond.lt (v Row) (v Total))) countersRound

namespace Counters

variable {μ μ' : ℕ → ℤ} {N K0 N0 dst i : ℕ}

/-- The memory before round i: band and block of the rows below i are written, and no cell outside
the 2 N cells from dst has changed. -/
def Counted (μ : ℕ → ℤ) (N K0 N0 dst i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ I < i, μ' (dst + I) = (I / (K0 * N0) : ℕ) ∧ μ' (dst + N + I) = (I / N0 % K0 : ℕ)) ∧
    SameOutside μ μ' dst (2 * N)













/-- The state before round i: the counters are those of row i. -/
def Inv (μ : ℕ → ℤ) (N K0 N0 dst i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [N, K0, N0, dst, i, (Spec.ctrAt K0 N0 i).band,
    (Spec.ctrAt K0 N0 i).block, (Spec.ctrAt K0 N0 i).off], μ'⟩ ∧ Counted μ N K0 N0 dst i μ'

end Counters

open Counters

variable {μ : ℕ → ℤ} {N K0 N0 dst : ℕ}





































































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Tables_Binomials


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# A binomial coefficient, by Pascal's triangle

Section 2.3.4 needs the number K = (L choose m) of subsets of size m.  binom(L, m, pas) returns this
binomial coefficient.  The cells pas, …, pas + L hold a row of Pascal's triangle.  Row 0 is 1
followed by zeros (`binomFirst_spec`), and the next row is formed in place, from right to left, so
that the two entries that are added are still those of the old row.  `binomPlace_spec` treats one
entry, by Pascal's rule, `binomInner_spec` one row, and `binom_spec` runs through the rows;
`binom_entry` is the specification that the callers of the procedure assume.
-/

@[expose] public section

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Binom

/-- The local variables of binom: Levels = L, Size = m, Addr = pas (the arguments); Row is the
number of the row, and Place the place in it. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Addr : ℕ := 2
@[inherit_doc Levels] abbrev Row : ℕ := 3
@[inherit_doc Levels] abbrev Place : ℕ := 4

end Binom

open Binom

/-- One entry of the next row: the entry above it plus the entry to the left of that. -/
def binomPlace : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) (v Addr) (v Place))
      ((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Addr) (v Place)))
        (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v Addr) (v Place)) (k 1)))))
    (.set Place ((Light.Expr.op Light.Op.sub) (v Place) (k 1))))

/-- The loop that turns row i of the triangle into row i + 1, from right to left. -/
def binomInner : Stmt := .while ((Light.Cond.lt (k 0) (v Place))) binomPlace

/-- One round of the loop over the rows. -/
def binomRow : Stmt := (Light.Stmt.seq (.set Place (v Levels))
                         (Light.Stmt.seq binomInner (.set Row ((Light.Expr.op Light.Op.add) (v Row) (k 1)))))

/-- Row 0 of the triangle: 1 followed by L zeros. -/
def binomFirst : Stmt :=
  (Light.Stmt.seq (.store (v Addr) (k 1))
    (Light.Stmt.seq (.set Place (k 1))
      (.while (Light.Cond.lt (v Place) ((Light.Expr.op Light.Op.add) (v Levels) (k 1)))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Addr) (v Place)) (k 0))
          (.set Place ((Light.Expr.op Light.Op.add) (v Place) (k 1)))))))

/-- binom(L, m, pas).  The number of the row is not set at the beginning: local variables that are
not arguments start at 0.  The result of a procedure is what it leaves in local variable 0. -/
def binomBody : Stmt :=
  (Light.Stmt.seq binomFirst
    (Light.Stmt.seq (.while (Light.Cond.lt (v Row) (v Levels)) binomRow)
      (.set Levels (M ((Light.Expr.op Light.Op.add) (v Addr) (v Size))))))

namespace Binom

/-! ## One row from the row before it -/

/-- The memory while row i is turned into row i + 1: the entries to the right of place p are those
of row i + 1, the others still those of row i; no cell outside the L + 2 cells that the procedure
may use has changed. -/
def Mixed (μ : ℕ → ℤ) (L pas i p : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j ≤ L, μ' (pas + j) = if p < j then (((i + 1).choose j : ℕ) : ℤ) else (i.choose j : ℕ)) ∧
    SameOutside μ μ' pas (L + 2)











variable {μ : ℕ → ℤ} {L m pas i : ℕ} {T : ℕ} {Q : State → Prop}

/-- The state after r entries have been replaced: the place is L - r. -/
def Inv (μ : ℕ → ℤ) (L m pas i r : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [L, m, pas, i, (L - r : ℕ)], μ'⟩ ∧ Mixed μ L pas i (L - r) μ'























































/-! ## The loop over the rows -/

/-- The state before round i: the cells hold row i of the triangle. -/
def RowAt (μ : ℕ → ℤ) (L m pas i : ℕ) (σ : State) : Prop :=
  ∃ (p : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L, m, pas, i, p], μ'⟩ ∧
    (∀ j ≤ L, μ' (pas + j) = (i.choose j : ℕ)) ∧ SameOutside μ μ' pas (L + 2)

/-- The time of one round of the loop over the rows. -/
def tRow (L : ℕ) : ℕ := 23 * L + 10














































end Binom

variable {μ : ℕ → ℤ} {L m pas : ℕ}






























end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Tables_Coefficients


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The tables of the coefficients of Schönhage's identity

Section 2.2 defines, for each of the ten terms λ of Schönhage's identity, two linear forms φ_λ and
ψ_λ in seven variables each; step (2) of the recursion applies them.  coef(phi) writes the
coefficient φ_λ(s) of the variable number s < 7 in the form of the term number λ < 10 to the cell
phi + 7 λ + s, and ψ_λ(t) to the cell phi + 70 + 7 λ + t.  The body is a straight line of 140
stores, made from the two tables `Spec.phiTable` and `Spec.psiTable`.  `storeSigns_spec` treats
such a line of stores by induction on the list, and `coef_entry`, the specification that the callers
of the procedure assume, applies it to the two tables.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-- A coefficient as an expression: 1, 0, or 0 - 1. -/
def signExpr (x : ℤ) : Expr := if x = 1 then k 1 else if x = 0 then k 0 else ((Light.Expr.op Light.Op.sub) (k 0) (k 1))

/-- The only local variable of coef: its argument phi. -/
abbrev Coef.Dest : ℕ := 0

open Coef in
/-- Stores the numbers of the list l, each of them 1, 0 or -1, into the cells from phi + i on. -/
def storeSigns : ℕ → List ℤ → Stmt
  | _, [] => .skip
  | i, x :: l => (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (k i)) (signExpr x)) (storeSigns (i + 1) l))

/-- coef(phi). -/
def coefBody : Stmt := storeSigns 0 (Spec.phiFlat ++ Spec.psiFlat)




















































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Tables_Digits


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Tables of digits, by an odometer

The programs for Theorem 5 turn the number of a row or of a column into a string ("locate the output
strings", in the proof of Theorem 5), so they need the digits of these numbers in base 3 and in
base 4. digits(n, b, len, dst) writes, for every x < n, the len digits of x % b^len in base b, most
significant first, to the len cells from dst + x * len.  There is no division: row 0 is zero, and
row x + 1 is row x plus one, formed from the least significant digit on with a carry.

* The pure side: `carryInto b j x` is the carry into the place of weight b^j when 1 is added to x,
  defined as the routine computes it, and `placeDigit_succ` says that a place of x plus its carry,
  reduced if it reaches b, is the place of x + 1.
* `digitsPlace_spec` treats one place, `digitsInner_spec` one row, `digitsZero_spec` row 0, and
  `digits_spec` runs through the rows; `digits_entry` is the specification that the callers of the
  procedure assume.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

namespace Digits

/-! ## Adding 1 to a number, place by place -/

/-- The digit of weight b^j of x. -/
def placeDigit (b j x : ℕ) : ℕ := x / b ^ j % b

/-- The carry into the digit of weight b^j when 1 is added to x: 1 into the last place, and then 1
as long as the digit plus the carry reaches b. -/
def carryInto (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, x => if placeDigit b j x + carryInto b j x < b then 0 else 1























































/-! ## The program -/

/-- The local variables of digits: Total = n, Base = b, Len = len, Dest = dst (the arguments); Row
is the number of the row being written, Cur its address and Prev the address of the row before it;
Place is the place, Carry the carry into it, and Digit the new digit. -/
abbrev Total : ℕ := 0
@[inherit_doc Total] abbrev Base : ℕ := 1
@[inherit_doc Total] abbrev Len : ℕ := 2
@[inherit_doc Total] abbrev Dest : ℕ := 3
@[inherit_doc Total] abbrev Row : ℕ := 4
@[inherit_doc Total] abbrev Cur : ℕ := 5
@[inherit_doc Total] abbrev Prev : ℕ := 6
@[inherit_doc Total] abbrev Place : ℕ := 7
@[inherit_doc Total] abbrev Carry : ℕ := 8
@[inherit_doc Total] abbrev Digit : ℕ := 9

end Digits

open Digits

variable {lim : Limits} {P : Program} {d : ℕ}

/-- One place of the new row: the digit of the row before it plus the carry, or 0 if this reaches
b; in the second case the carry stays 1. -/
def digitsPlace : Stmt :=
  (Light.Stmt.seq (.set Place ((Light.Expr.op Light.Op.sub) (v Place) (k 1)))
    (Light.Stmt.seq
      (.set Digit ((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Prev) (v Place))) (v Carry)))
      (.ite (Light.Cond.lt (v Digit) (v Base))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Cur) (v Place)) (v Digit)) (.set Carry (k 0)))
        (.store ((Light.Expr.op Light.Op.add) (v Cur) (v Place)) (k 0)))))

/-- The loop that forms one row from the row before it, from the last place on. -/
def digitsInner : Stmt := .while ((Light.Cond.lt (k 0) (v Place))) digitsPlace

/-- One round of the loop over the rows. -/
def digitsRow : Stmt :=
  (Light.Stmt.seq (.set Place (v Len))
    (Light.Stmt.seq (.set Carry (k 1))
      (Light.Stmt.seq digitsInner
        (Light.Stmt.seq (.set Row ((Light.Expr.op Light.Op.add) (v Row) (k 1)))
          (Light.Stmt.seq (.set Prev (v Cur)) (.set Cur ((Light.Expr.op Light.Op.add) (v Cur) (v Len))))))))

/-- Row 0 is zero.  The place is not set at the beginning: local variables that are not arguments
start at 0. -/
def digitsZero : Stmt :=
  .while ((Light.Cond.lt (v Place) (v Len))) (
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Place)) (k 0))
      (.set Place ((Light.Expr.op Light.Op.add) (v Place) (k 1)))))

/-- digits(n, b, len, dst). -/
def digitsBody : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v Total))) (
    (Light.Stmt.seq digitsZero
      (Light.Stmt.seq (.set Row (k 1))
        (Light.Stmt.seq (.set Prev (v Dest))
          (Light.Stmt.seq (.set Cur ((Light.Expr.op Light.Op.add) (v Dest) (v Len)))
            (.while (Light.Cond.lt (v Row) (v Total)) digitsRow)))))) .skip

namespace Digits

/-! ## One row from the row before it -/

/-- The memory after r places of the row of y + 1 have been written to the len cells from cur, from
the last place on; no other cell has changed. -/
def Placed (μ : ℕ → ℤ) (b len cur y r : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j < r, μ' (cur + (len - 1 - j)) = (placeDigit b j (y + 1) : ℕ)) ∧ SameOutside μ μ' cur len












/-- The state after r places: the place is len - r, and the carry is the carry into place r. -/
def Inv (μ : ℕ → ℤ) (n b len dst row cur prev y r : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [n, b, len, dst, row, cur, prev, (len - r : ℕ), carryInto b r y, x], μ'⟩ ∧
      Placed μ b len cur y r μ'

variable {μ : ℕ → ℤ} {n b len dst row cur prev y : ℕ} {T : ℕ} {Q : State → Prop}



































































/-! ## The loop over the rows -/

/-- The state after the rows 0, …, i have been written: they stand in the table, and no cell outside
the table has changed. -/
def RowsDone (μ : ℕ → ℤ) (n b len dst i : ℕ) (σ : State) : Prop :=
  ∃ (p c x : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [n, b, len, dst, (i + 1 : ℕ), (dst + (i + 1) * len : ℕ),
      (dst + i * len : ℕ), p, c, x], μ'⟩ ∧
    (∀ y < i + 1, ∀ q < len, μ' (dst + y * len + q) = (placeDigit b (len - 1 - q) y : ℕ)) ∧
    SameOutside μ μ' dst (n * len)

/-- The time of one round of the loop over the rows. -/
def tRow (len : ℕ) : ℕ := 26 * len + 18






















































end Digits

variable {μ : ℕ → ℤ} {n b len dst : ℕ}
















































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Tables_Subsets


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec.Subsets
end ThreeSumApsp.Spec.Subsets


/-!
# The table of subsets

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  Section 2.4.4 counts the time to "list the K₀² subsets".
subsets(L, m, KK, mask), which is called with KK = K₀², writes the first KK masks of the enumeration
`Spec.unrank`, one after the other, as 0/1 cells from mask.  Row 0 is m ones followed by zeros
(`firstRow_spec`).  Each further row is made from the row before it: one pass from the end of the
old row finds the last 1 that is followed by a 0 (`scan_spec`), and one pass writes the new row
(`write_spec`).  There is no arithmetic on the entries, and a row takes O(L) steps.  What the two
passes compute is described without a program by `scanAt` and `newCell`, with the facts
`bit_unrank_succ` and `scanAt_fits`; here each pass is connected with this description,
`tableRow_spec` treats one row, and `subsetTable_spec` runs through the rows.  `subsets_entry` is
the specification that the callers of the procedure assume.
-/

@[expose] public section

open ThreeSumApsp.Spec.Subsets

namespace Light.Sec2.Subsets

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The local variables of subsets: Levels = L, Size = m, Rows = KK, Table = mask (the arguments);
Row is the number of the current row and Addr its address; Phase, Ones and Pos are the state of the
scan (phase, number of ones at the end, position found); Cell is the counter of the inner loops. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Table : ℕ := 3
@[inherit_doc Levels] abbrev Row : ℕ := 4
@[inherit_doc Levels] abbrev Addr : ℕ := 5
@[inherit_doc Levels] abbrev Phase : ℕ := 6
@[inherit_doc Levels] abbrev Ones : ℕ := 7
@[inherit_doc Levels] abbrev Pos : ℕ := 8
@[inherit_doc Levels] abbrev Cell : ℕ := 9

/-- One cell of the first row: 1 for the first m cells, then 0. -/
def firstRowRound : Stmt :=
  .ite ((Light.Cond.lt (v Cell) (v Size))) (.store (((Light.Expr.op Light.Op.add) (v Addr) (v Cell))) (k 1)) (.store (((Light.Expr.op Light.Op.add) (v Addr) (v Cell))) (k 0))

/-- The first row: m ones, then zeros. -/
def firstRowLoop : Stmt := .for Cell (v Levels) firstRowRound

/-- One round of the scan: the cell number Cell from the end of the row before the current one. -/
def scanRound : Stmt :=
  .ite ((Light.Cond.lt (v Phase) (k 1)))
    (.ite ((Light.Cond.lt (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.sub) (v Addr) (k 1)) (v Cell))) (k 1))) (.set Phase (k 1)) (.set Ones (((Light.Expr.op Light.Op.add) (v Ones) (k 1)))))
    (.ite ((Light.Cond.lt (v Phase) (k 2)))
      (.ite ((Light.Cond.lt (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.sub) (v Addr) (k 1)) (v Cell))) (k 1))) .skip
        ((Light.Stmt.seq (.set Phase (k 2))
           (.set Pos ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.sub) (v Levels) (k 1)) (v Cell))))))
      .skip)

/-- The scan of the row before the current one, from its end. -/
def scanLoop : Stmt :=
  (Light.Stmt.seq (.set Phase (k 0))
    (Light.Stmt.seq (.set Ones (k 0)) (Light.Stmt.seq (.set Pos (k 0)) (.for Cell (v Levels) scanRound))))

/-- One cell of the new row, from the row before it and the result of the scan. -/
def writeRound : Stmt :=
  .ite ((Light.Cond.lt (v Cell) (v Pos))) (.store (((Light.Expr.op Light.Op.add) (v Addr) (v Cell))) (M (((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.sub) (v Addr) (v Levels)) (v Cell)))))
    (.ite ((Light.Cond.lt (v Cell) ((Light.Expr.op Light.Op.add) (v Pos) (k 1)))) (.store (((Light.Expr.op Light.Op.add) (v Addr) (v Cell))) (k 0))
      (.ite ((Light.Cond.lt (v Cell) ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Pos) (k 2)) (v Ones)))) (.store (((Light.Expr.op Light.Op.add) (v Addr) (v Cell))) (k 1))
        (.store (((Light.Expr.op Light.Op.add) (v Addr) (v Cell))) (k 0))))

/-- The new row, from the row before it and the result of the scan. -/
def writeLoop : Stmt := .for Cell (v Levels) writeRound

/-- A further row, from the row before it. -/
def nextRow : Stmt := (Light.Stmt.seq scanLoop writeLoop)

/-- One round of the loop over the rows. -/
def tableRow : Stmt :=
  (Light.Stmt.seq (.ite (Light.Cond.lt (v Row) (k 1)) firstRowLoop nextRow)
    (Light.Stmt.seq (.set Row ((Light.Expr.op Light.Op.add) (v Row) (k 1)))
      (.set Addr ((Light.Expr.op Light.Op.add) (v Addr) (v Levels)))))

/-- subsets(L, m, KK, mask). -/
def subsetTableBody : Stmt :=
  (Light.Stmt.seq (.set Row (k 0))
    (Light.Stmt.seq (.set Addr (v Table)) (.while (Light.Cond.lt (v Row) (v Rows)) tableRow)))

/-! ## The three passes -/

/-- The list of the local variables. -/
abbrev locals (L m KK mask s a : ℕ) (S : Scan) (j : ℤ) : List ℤ :=
  [L, m, KK, mask, s, a, S.phase, S.ones, S.pos, j]

/-- The row of L cells that ends just before the address a. -/
abbrev prevRow (μ : ℕ → ℤ) (a L : ℕ) : ℕ → ℤ := fun q => μ (a - L + q)

/-- The row that the writing pass forms from the row before the address a and the result S of its
scan. -/
abbrev newRow (μ : ℕ → ℤ) (a L : ℕ) (S : Scan) : ℕ → ℤ := fun r => newCell S (prevRow μ a L r) r

variable {μ : ℕ → ℤ} {L m KK mask s a : ℕ} {S : Scan} {j₀ : ℤ} {T : ℕ} {Q : State → Prop}

























































































































/-! ## The loop over the rows -/

/-- The state before row number s is written: the rows before it stand in the table, and no cell
outside the table has changed. -/
def RowsDone (μ : ℕ → ℤ) (L m KK mask s : ℕ) (σ : State) : Prop :=
  ∃ (S : Scan) (j : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals L m KK mask s (mask + s * L) S j), μ'⟩ ∧
    (∀ t < s, SegB μ' (mask + t * L) (Spec.unrank L m t)) ∧ SameOutside μ μ' mask (KK * L)

/-- The time of one round of the loop over the rows. -/
def tRow (L : ℕ) : ℕ := 64 * L + 30


























































































end Light.Sec2.Subsets

namespace Light.Sec2

open ThreeSumApsp Subsets

variable {lim : Limits} {P : Program}







end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Wanted_Codes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The tile and the output string of each wanted position

Section 2.4.4: "Each wanted position (I, J) ∈ W lies in one tile T and is indexed by one output
string of T".  For the i-th wanted position (I, J) the routine wanted(w, L, Lo, N, K0, nB, aWI, aWJ,
band, dig3, mask, tid) writes the number BAND[I] · nB + BAND[J] of its tile to tid + i, the code
Spec.outCodeOfPos L m I J of its output string to tid + w + i, and the L digits of the code to
tid + 2 w + i L.  The code is formed by Horner's rule in base 10 while walking the mask of the
subset number BLOCK[I] · K₀ + BLOCK[J]: digit 9 at a level of the subset, and otherwise 3 x + y for
the next base-3 digits x, y of the offsets of I and J.  O(L) steps for each position.

In the paper's letters (Sections 2.3.3 and 2.3.4): D = 4^m, N₀ = 3^(L-m) is the side of a block,
K₀ = ⌊√binom(L, m)⌋ is the number of blocks along the side of a tile, and the offset of I is
I mod N₀, the place of I within its block.

A round of the loop over the positions has three parts, each with its lemma: `prepBlock_ends` (the
position, its tile and the three addresses), `levelLoop_ends` (the walk along the mask; one level is
`levelRound_ends`) and `finishBlock_ends` (the tile and the code are stored).  `wantedRound_ends`
puts them together, `wantedBody_ends` is the loop, and `wanted_entry` is the result for the callers:
a call of procedure `pWanted` does what `WantedSpec` says.
-/

@[expose] public section

namespace Light.Sec2.Wanted

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace Local

/-- The number w of wanted positions. -/
abbrev WW : ℕ := 0
/-- The number L of levels. -/
abbrev LL : ℕ := 1
/-- Lo = L - m, the number of base-3 digits of an offset. -/
abbrev LO : ℕ := 2
/-- The size N. -/
abbrev NN : ℕ := 3
/-- K₀, the number of blocks along the side of a tile. -/
abbrev KK : ℕ := 4
/-- The number nB of bands. -/
abbrev NB : ℕ := 5
/-- The rows of the wanted positions. -/
abbrev AWI : ℕ := 6
/-- The columns of the wanted positions. -/
abbrev AWJ : ℕ := 7
/-- The table BAND, followed by the table BLOCK. -/
abbrev BAND : ℕ := 8
/-- The base-3 digits of the offsets. -/
abbrev DIG3 : ℕ := 9
/-- The masks of the subsets. -/
abbrev MASK : ℕ := 10
/-- Where the numbers of the tiles, the codes and the digits are written. -/
abbrev TID : ℕ := 11
/-- The number i of the position. -/
abbrev CI : ℕ := 12
/-- The row I. -/
abbrev PI : ℕ := 13
/-- The column J. -/
abbrev PJ : ℕ := 14
/-- The address of the mask. -/
abbrev AM : ℕ := 15
/-- The address of the next digit of the offset of I. -/
abbrev AI : ℕ := 16
/-- The address of the next digit of the offset of J. -/
abbrev AJ : ℕ := 17
/-- The number formed so far. -/
abbrev ACC : ℕ := 18
/-- The level. -/
abbrev LEV : ℕ := 19
/-- The address of the row of digits. -/
abbrev ROW : ℕ := 20
/-- The digit. -/
abbrev DIG : ℕ := 21
/-- The number of the tile. -/
abbrev TILE : ℕ := 22

end Local

open Local

/-- The digit is stored and appended to the number, and the level moves on. -/
def levelTail : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v ROW) (v LEV)) (v DIG))
    (Light.Stmt.seq (.set ACC ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v ACC) (k 10)) (v DIG)))
      (.set LEV ((Light.Expr.op Light.Op.add) (v LEV) (k 1)))))

/-- The digit of the level: 9 at a level of the subset, and otherwise 3 x + y for the next digits
x, y of the two offsets. -/
def levelDigit : Stmt :=
  .ite ((Light.Cond.lt (M ((Light.Expr.op Light.Op.add) (v AM) (v LEV))) (k 1)))
    ((Light.Stmt.seq (.set DIG ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (k 3) (M (v AI))) (M (v AJ))))
       (Light.Stmt.seq (.set AI ((Light.Expr.op Light.Op.add) (v AI) (k 1)))
         (.set AJ ((Light.Expr.op Light.Op.add) (v AJ) (k 1))))))
    (.set DIG (k 9))

/-- One level of the walk along the mask. -/
def levelRound : Stmt :=
  (Light.Stmt.seq levelDigit levelTail)

/-- The walk along the mask. -/
def levelLoop : Stmt :=
  .while ((Light.Cond.lt (v LEV) (v LL))) levelRound

/-- Before the walk: the position, the number of its tile, and the three addresses. -/
def prepBlock : Stmt :=
  (Light.Stmt.seq (.set PI (M ((Light.Expr.op Light.Op.add) (v AWI) (v CI))))
    (Light.Stmt.seq (.set PJ (M ((Light.Expr.op Light.Op.add) (v AWJ) (v CI))))
      (Light.Stmt.seq
        (.set TILE
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v BAND) (v PI))) (v NB))
            (M ((Light.Expr.op Light.Op.add) (v BAND) (v PJ)))))
        (Light.Stmt.seq
          (.set AM
            ((Light.Expr.op Light.Op.add) (v MASK)
              ((Light.Expr.op Light.Op.mul)
                ((Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.mul)
                    (M ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v BAND) (v NN)) (v PI))) (v KK))
                  (M ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v BAND) (v NN)) (v PJ))))
                (v LL))))
          (Light.Stmt.seq (.set AI ((Light.Expr.op Light.Op.add) (v DIG3) ((Light.Expr.op Light.Op.mul) (v PI) (v LO))))
            (Light.Stmt.seq (.set AJ ((Light.Expr.op Light.Op.add) (v DIG3) ((Light.Expr.op Light.Op.mul) (v PJ) (v LO))))
              (Light.Stmt.seq (.set ACC (k 0)) (.set LEV (k 0)))))))))

/-- After the walk: the number of the tile and the code are stored, and the counters move on. -/
def finishBlock : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v TID) (v CI)) (v TILE))
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v TID) (v WW)) (v CI)) (v ACC))
      (Light.Stmt.seq (.set CI ((Light.Expr.op Light.Op.add) (v CI) (k 1)))
        (.set ROW ((Light.Expr.op Light.Op.add) (v ROW) (v LL))))))

/-- wanted(w, L, Lo, N, K0, nB, aWI, aWJ, band, dig3, mask, tid). -/
def wantedBody : Stmt :=
  (Light.Stmt.seq (.set CI (k 0))
    (Light.Stmt.seq (.set ROW ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v TID) (v WW)) (v WW)))
      (.while (Light.Cond.lt (v CI) (v WW)) (Light.Stmt.seq prepBlock (Light.Stmt.seq levelLoop finishBlock)))))




/-- The twelve arguments of wanted. -/
structure Args where
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The number of levels. -/
  L : ℕ
  /-- The number of base-3 digits of an offset. -/
  Lo : ℕ
  /-- The size. -/
  N : ℕ
  /-- The number of blocks along the side of a tile. -/
  K₀ : ℕ
  /-- The number of bands. -/
  nB : ℕ
  /-- The rows of the wanted positions. -/
  aWI : ℕ
  /-- The columns of the wanted positions. -/
  aWJ : ℕ
  /-- The tables BAND and BLOCK. -/
  band : ℕ
  /-- The base-3 digits of the offsets. -/
  dig3 : ℕ
  /-- The masks. -/
  mask : ℕ
  /-- The output. -/
  tid : ℕ








/-! ## The walk along one mask -/






















variable {μ μ' : ℕ → ℤ} {m : ℕ} {mk : List Bool} {rI rJ : List ℕ} {L Lo am aI aJ row l : ℕ}




















































variable {a : Args} {i : ℕ} {pI pJ tile : ℤ}






































































































































/-! ## Before and after the walk -/









































































/-! ## One position -/








/-- What wanted leaves for the position number i. -/
def Row (p : Par) (w tid : ℕ) (I J : ℕ → ℕ) (μ : ℕ → ℤ) (i : ℕ) : Prop :=
  μ (tid + i) = (I i / (p.K0 * p.N0) * p.nB + J i / (p.K0 * p.N0) : ℕ) ∧
  μ (tid + w + i) = (Spec.outCodeOfPos p.L p.m (I i) (J i) : ℕ) ∧
  SegN μ (tid + 2 * w + i * p.L) (Spec.outDigitsOfPos p.L p.m (I i) (J i))

/-- The first i positions are done, and only the output has changed. -/
structure WantedMem (p : Par) (w tid : ℕ) (I J : ℕ → ℕ) (μ μ' : ℕ → ℤ) (i : ℕ) : Prop where
  done : ∀ i' < i, Row p w tid I J μ' i'
  rest : SameOutside μ μ' tid (2 * w + w * p.L)

section Position

variable {p : Par} {w aWI aWJ band dig3 mask tid : ℕ} {I J : ℕ → ℕ}
  (pre : WantedPre lim p w aWI aWJ band dig3 mask tid I J μ)
  (mem : WantedMem p w tid I J μ μ' i) (hi : i < w)
include pre













include hi











include mem


















































































































end Position









variable {p : Par} {w aWI aWJ band dig3 mask tid : ℕ} {I J : ℕ → ℕ}















































end Light.Sec2.Wanted

namespace Light.Sec2

open ThreeSumApsp Wanted

variable {lim : Limits} {P : Program}

















end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Wanted_Gather


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5 in the light language: gathering the codes in sorted order

Section 2.4.4: "sort the sets W_T", the wanted positions of each tile T.  Sorting produces a
permutation of the wanted positions.  The procedure gather(w, perm, src, dst) then copies their
codes into sorted order: dst[i] := src[perm[i]] for i < w.

gather_entry shows that a call ends within 20 (w + 1) steps, with dst[i] = src[π[i]] for the list π
at perm, and that no cell outside the w cells of dst has changed.  The proof is one loop with the
invariant GatherInv; each round reads two cells that are still as at the start and writes dst[i].
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace GatherLocal

/-- The number w of cells. -/
abbrev Len : ℕ := 0
/-- The permutation. -/
abbrev Perm : ℕ := 1
/-- The array that is read. -/
abbrev Src : ℕ := 2
/-- The array that is written. -/
abbrev Dest : ℕ := 3
/-- The counter i of the loop. -/
abbrev Pos : ℕ := 4

end GatherLocal

open GatherLocal

/-- gather(w, perm, src, dst): dst[i] := src[perm[i]] for i < w. -/
def gatherBody : Stmt :=
  .for Pos (v Len) (.store (((Light.Expr.op Light.Op.add) (v Dest) (v Pos))) (M (((Light.Expr.op Light.Op.add) (v Src) (M ((Light.Expr.op Light.Op.add) (v Perm) (v Pos)))))))

































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Wanted_Report


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5 as a program: the report

Section 2.4.4: "and report, for each (I, J) ∈ W, the value at its output string."

The pruned recursions leave the values in the sorted order of the wanted positions.  report puts
them back in the order in which the positions were given: OUT[PERM[i]] := SV[i].  It is the
counterpart of gather, which reads through the permutation.  `report_entry` is one loop with the
invariant `ReportInv`; the places PERM[i] are different, so no value is overwritten
(`ReportInv.write`).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp











namespace ReportLocal

/-- The number w of wanted positions. -/
abbrev LEN : ℕ := 0
/-- The permutation, sorted order to given order. -/
abbrev PERM : ℕ := 1
/-- The values, in sorted order. -/
abbrev VALS : ℕ := 2
/-- The output. -/
abbrev OUT : ℕ := 3
/-- The place i in the sorted order. -/
abbrev POS : ℕ := 4

end ReportLocal

open ReportLocal in
/-- report(w, perm, sv, out): OUT[PERM[i]] := VALS[i] for i < w, where VALS is the array at sv. -/
def reportBody : Stmt :=
  .for POS (v LEN) (.store (((Light.Expr.op Light.Op.add) (v OUT) (M ((Light.Expr.op Light.Op.add) (v PERM) (v POS))))) (M (((Light.Expr.op Light.Op.add) (v VALS) (v POS)))))

variable {lim : Limits} {P : Program} {c i : ℕ} {μ μ' : ℕ → ℤ}

/-! ## The report -/




















































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Wanted_Sort


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 5 in the light language: sorting the wanted positions

sortWanted(w, L, nT, tid, dgt, perm): "sort the sets W_T" (Section 2.4.4), by a radix sort of the
indices 0, …, w - 1, in O((L + 1) (w + 10) + nT) steps.  The routine writes the list 0, …, w - 1 to
perm (swInit_ends).  Then, unless w = 0, it makes L stable passes on the stored digits of the codes,
the last digit first: after r of them the list is sorted by the last r digits (swDigit_ends for one
pass, swDigits_ends for all).  One more pass, on the numbers of the tiles, sorts the list by tile
and code and leaves the number of positions in the tiles below s, for every s (swTiles_ends).
sortWantedBody_ends puts the parts together, and sortWanted_entry is the specification
SortWantedSpec that the callers use.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec2

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace SortWanted

/-- The local variables of sortWanted: the arguments w (Num), L (Levels), nT (Tiles), tid (TileOf),
dgt (Digits), perm (Perm); a counter (Idx); the unused results of the calls (Res).  A pass
(radixPass) reads w and perm from the locals 0 and 5 and writes to local 7, which are Num, Perm and
Res. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Levels : ℕ := 1
@[inherit_doc Num] abbrev Tiles : ℕ := 2
@[inherit_doc Num] abbrev TileOf : ℕ := 3
@[inherit_doc Num] abbrev Digits : ℕ := 4
@[inherit_doc Num] abbrev Perm : ℕ := 5
@[inherit_doc Num] abbrev Idx : ℕ := 6


end SortWanted

open SortWanted

/-- perm[i] := i for i < w. -/
def swInit : Stmt := .for Idx (v Num) (.store (((Light.Expr.op Light.Op.add) (v Perm) (v Idx))) (v Idx))

/-- The pass on the digit whose index is in the counter. -/
def swDigit : Stmt :=
  radixPass pCountSort pCopy (v Digits) (v Levels) (v Idx) (k 10) (((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Perm) (v Num)) (v Num)))

/-- The passes on the digits L - 1, …, 0. -/
def swDigits : Stmt :=
  (Light.Stmt.seq (.set Idx (v Levels))
    (.while (Light.Cond.lt (k 0) (v Idx))
      (Light.Stmt.seq (.set Idx ((Light.Expr.op Light.Op.sub) (v Idx) (k 1))) swDigit)))

/-- The pass on the numbers of the tiles. -/
def swTiles : Stmt :=
  radixPass pCountSort pCopy (v TileOf) (k 1) (k 0) (v Tiles)
    (((Light.Expr.op Light.Op.add)
       ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Perm) (v Num)) (v Num))
         (v Tiles))
       (k 11)))

/-- sortWanted(w, L, nT, tid, dgt, perm).  For w = 0 there are no passes on the digits: only for
w > 0 do the assumptions say that L fits in a word. -/
def sortWantedBody : Stmt := (Light.Stmt.seq swInit (Light.Stmt.seq (.ite (Light.Cond.lt (k 0) (v Num)) swDigits .skip) swTiles))

/-! ## What is assumed, and the state between the passes -/

namespace SortWanted





end SortWanted













variable {μ μ' : ℕ → ℤ} {A : Args} {t x g : ℕ → ℕ} {π : List ℕ} {σ : State}









/-! ## The list 0, …, w - 1 -/
































/-! ## The passes on the digits -/




































































































/-! ## The pass on the tiles -/



































































/-! ## The routine -/













































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_Program


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Theorem 5: the program

The list of the procedures of Theorem 5's program, in the order of their numbers.  An entry is the
specification of a procedure together with a bound on its time, a constant times a shape.  In every
program that begins with this list, the procedures that the shared stage calls meet their entries
with the constant cShared5 (sharedCallees_of_prefix), and those that the solver calls with the
constant cMain5 (mainCallees_of_prefix).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The program of Theorem 5.  The numbers of the procedures begin with 1; number 0 is empty. -/
def program5 : Program :=
  [.skip, sharedBody, powBody, binomBody, sqrtBody, Subsets.subsetTableBody, countersBody,
   digitsBody, coefBody, bandArrayBody, encStepBody, encodeBody pEncStep pEncode, encodeBandsBody,
   Wanted.wantedBody, countSortBody, sortWantedBody, segBoundsBody, unionBody, pickBody, prunedBody,
   runTilesBody, reportBody, fillBody, copyBody, gatherBody, thm5Body]










/-! ## All entries -/

/-- The constant of the procedures that the shared stage calls. -/
def cShared5 : ℕ := 2000
































end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec2_Theorem5_AllInstances_Program


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The running-time claim "Theorem 5" for the light model, for the program of Theorem 5

programThin is program5 followed by regimeBody (the test whether an instance is in the regime of
Theorem 5), thinBruteBody (the brute force, for the instances outside it) and thinBody (the solver
for all instances). claim_theorem_5: it solves the thin matrix product on all instances, and for D ≥
4 a power of four, N ≥ D^18, w ≤ N²/√D and entries of at most N^c its time is at most a constant
times N² log² D / D^{1/18}. This is thin_claim for the program and the solver of Theorem 5.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- The program of the thin matrix product on all instances. -/
def programThin : Program := program5 ++ [regimeBody, thinBruteBody, thinBody]





end Light.Sec2

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Corollary15_16_CountAndDetect


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/

















/-! ## Counting with the thin matrix product -/






















end LopHosts

open LopHosts










/-! ## Detecting with counting -/

namespace LopArgs

/-- The local variables that hold the arguments of a solver of the thin matrix product or of a
lopsided triangle problem: N, D, w, U, x, y, wi, wj, out, fr. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev DD : ℕ := 1
@[inherit_doc N] abbrev W : ℕ := 2
@[inherit_doc N] abbrev U : ℕ := 3
@[inherit_doc N] abbrev X : ℕ := 4
@[inherit_doc N] abbrev Y : ℕ := 5
@[inherit_doc N] abbrev WI : ℕ := 6
@[inherit_doc N] abbrev WJ : ℕ := 7
@[inherit_doc N] abbrev OUT : ℕ := 8
@[inherit_doc N] abbrev FR : ℕ := 9

end LopArgs

open LopArgs in
/-- detect(N, D, w, U, x, y, wi, wj, out, fr): calls the counting solver on the same arguments, then
replaces every nonzero answer by 1.  Local 10 takes the result of the call and is then the
counter. -/
def lopDetectBody (pCount : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCount [v N, v DD, v W, v U, v X, v Y, v WI, v WJ, v OUT, v FR] 10)
    (.for 10 (v W)
      (.ite (Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v OUT) (v 10))) (k 0)) .skip
        (.store ((Light.Expr.op Light.Op.add) (v OUT) (v 10)) (k 1)))))

/-- The number of steps of detect, if the counting solver takes Tn; the third parameter is w. -/
def lopDetectTime (Tn : List ℕ → ℕ) (ps : List ℕ) : ℕ := Tn ps + 20 * ps.getD 2 0 + 18

/-- What detect needs: one more level of calls. -/
def lopDetectNeed (need : List ℕ → Need) (ps : List ℕ) : Need :=
  ⟨(need ps).word, (need ps).cells, (need ps).depth + 1⟩

namespace LopHosts































































end LopHosts

open LopHosts
















end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Claim


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Theorem 17 as a claim about programs of the light language

`Claim.Theorem_17 M MM D g` says: from every solver of Lop-AE-SparseTri with running time `T` there
is a solver of Exact Triangle whose running time is at most
`4ng (T + C n²/√D) + C (κ n³ log n/g + MM(n) D^{3/2} + n² D g)` (`bound17`, with the three terms
`termScans`, `termPrime`, `termBuild` of the additional time).  Here `κ` is the exponent in
`|w(e)| ≤ n^κ` (the paper's ν), `D` and `g` are the parameters of the reduction as functions of
`n`, `MM(n)` is the number of ring operations of the matrix multiplication, and `M` says what
"solved in time" means.
This file reduces the claim, for the interpretation by programs of the light language, to two facts
about a host: it turns solvers into solvers and keeps their need (word size, cells, depth of calls)
polynomial, and its time function obeys the bound (`ObeysBound17`, `claim17_of_host`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

/-- The right-hand side of `Claim.Theorem_17`. -/
noncomputable def bound17 (MM : ℕ → ℝ) (D g : ℕ → ℕ) (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ) (n : ℕ)
    (κ : ℝ) : ℝ :=
  4 * (n : ℝ) * (g n : ℝ) * (T n (D n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
    C * (termScans n (g n) κ + termPrime MM n (D n) + termBuild n (D n) (g n))

/-- The time of a host, as a function `time` of the time of the solver, obeys the bound of
Theorem 17 with some constant: whenever `T` bounds the time `Tn` of the solver, `bound17` with `T`
bounds `time Tn`, under the hypotheses of the theorem. -/
def ObeysBound17 (MM : ℕ → ℝ) (D g : ℕ → ℕ) (time : (List ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (Tn : List ℕ → ℕ) (T : ℕ → ℕ → ℕ → ℝ),
    (∀ m d w w' : ℕ, 1 ≤ m → 1 ≤ d → w ≤ w' → (Tn [m, d, w] : ℝ) ≤ T m d w') →
    ∀ (n U : ℕ) (κ : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
      (U : ℝ) ≤ (n : ℝ) ^ κ → (time Tn n U : ℝ) ≤ bound17 MM D g C T n κ



















end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Parameters_Sizes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The parameters of Theorems 17 and 19, without division and without roots

The proof of Theorem 19 chooses D as "the largest power of four with D ≤ n^{1/18}"
and g := ⌈D^{1/36}⌉, or D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉; the reduction of Theorem 17 uses
⌊n²/√D⌋ and quotients rounded up.  The language has neither division nor roots, so all of these are
found by counting up.  A power is compared with a bound without forming a number above the bound
times the base.

* powLt(g, e, t), for g ≥ 1, returns 1 if g^e < t, and 0 if not (`powLt_meets`); what it holds after
  i factors is `capPow g t i`.
* rootCeil(e, t) returns the least g with g^e ≥ t (`rootCeil_meets`).
* The four parameters; 5 and 26 stand for the two routes of Theorem 19, through Theorem 5 and
  through Corollary 26.  d5(n) returns the largest power of four that is at most n^{1/18}, g5(D)
  returns ⌈D^{1/36}⌉, d26(n) returns ⌊n^{1/18}⌋, and g26(D) returns ⌈D^{0.0315}⌉; g5 and g26
  are for D ≥ 1 (`d5_spec`, `g5_spec`, `d26_spec`, `g26_spec`).
* queryCapNat(n, D) returns ⌊n²/√D⌋, and ceilDiv(a, b) returns ⌈a/b⌉ (`queryCapNat_meets`,
  `ceilDiv_meets`).

No routine touches the memory.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Comparing a power with a bound -/

/-- The powers of g, as long as they are below t: the value stays as it is once it has reached
t. -/
def capPow (g t : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => if capPow g t i < t then capPow g t i * g else capPow g t i























namespace PowLt

/-- The local variables of powLt: the arguments g, e, t; the number of factors so far; their
product (Acc). -/
abbrev Base : ℕ := 0
@[inherit_doc Base] abbrev Exp : ℕ := 1
@[inherit_doc Base] abbrev Bound : ℕ := 2
@[inherit_doc Base] abbrev Cnt : ℕ := 3
@[inherit_doc Base] abbrev Acc : ℕ := 4

end PowLt

open PowLt in
/-- powLt(g, e, t). -/
def powLtBody : Stmt :=
  (Light.Stmt.seq (.set Cnt (k 0))
    (Light.Stmt.seq (.set Acc (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v Cnt) (v Exp))
          (Light.Stmt.seq
            (.ite (Light.Cond.lt (v Acc) (v Bound)) (.set Acc ((Light.Expr.op Light.Op.mul) (v Acc) (v Base))) .skip)
            (.set Cnt ((Light.Expr.op Light.Op.add) (v Cnt) (k 1)))))
        (.ite (Light.Cond.lt (v Acc) (v Bound)) (.set Base (k 1)) (.set Base (k 0))))))








































/-! ## Roots, rounded up -/

namespace RootCeil

/-- The local variables of rootCeil: the arguments e, t; the candidate g; whether g^e < t. -/
abbrev Exp : ℕ := 0
@[inherit_doc Exp] abbrev Bound : ℕ := 1
@[inherit_doc Exp] abbrev Cand : ℕ := 2
@[inherit_doc Exp] abbrev More : ℕ := 3

end RootCeil

open RootCeil in
/-- rootCeil(e, t), over the procedure pPow (powLt). -/
def rootCeilBody (pPow : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Cand (k 1))
    (Light.Stmt.seq (.call pPow [v Cand, v Exp, v Bound] More)
      (Light.Stmt.seq
        (.while (Light.Cond.eq (v More) (k 1))
          (Light.Stmt.seq (.set Cand ((Light.Expr.op Light.Op.add) (v Cand) (k 1)))
            (.call pPow [v Cand, v Exp, v Bound] More)))
        (.set Exp (v Cand)))))

/-- The time of rootCeil. -/
def tRootCeil (e t : ℕ) : ℕ := rootCeil e t * (16 * e + 27)

















































/-! ## The four parameters of the proof of Theorem 19 -/

/-- d26(n), over the procedure pRoot (rootCeil): ⌊n^{1/18}⌋.  Local 0 is the argument, local 1 takes
⌈(n + 1)^{1/18}⌉. -/
def d26Body (pRoot : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pRoot [k 18, (Light.Expr.op Light.Op.add) (v 0) (k 1)] 1)
    (.set 0 ((Light.Expr.op Light.Op.sub) (v 1) (k 1))))

/-- The time of d26. -/
def tD26 (n : ℕ) : ℕ := (paramD₂₆Nat n + 1) * 315 + 10

























/-- d5(n), over the procedure pD26: the largest power of four that is at most n^{1/18}.  Local 0 is
the argument, local 1 is ⌊n^{1/18}⌋, local 2 the power of four. -/
def d5Body (pD26 : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pD26 [v 0] 1)
    (Light.Stmt.seq (.set 2 (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.le ((Light.Expr.op Light.Op.mul) (k 4) (v 2)) (v 1))
          (.set 2 ((Light.Expr.op Light.Op.mul) (k 4) (v 2))))
        (.set 0 (v 2)))))





















































/-- g5(D), over the procedure pRoot: ⌈D^{1/36}⌉. -/
def g5Body (pRoot : ℕ) : Stmt := .call pRoot [k 36, v 0] 0
















/-- g26(D), over the procedure pRoot: ⌈D^{0.0315}⌉, the least g with g^2000 ≥ D^63.  Local 0 is the
argument, local 1 counts the factors, local 2 is their product. -/
def g26Body (pRoot : ℕ) : Stmt :=
  (Light.Stmt.seq (.set 1 (k 0))
    (Light.Stmt.seq (.set 2 (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v 1) (k 63))
          (Light.Stmt.seq (.set 2 ((Light.Expr.op Light.Op.mul) (v 2) (v 0)))
            (.set 1 ((Light.Expr.op Light.Op.add) (v 1) (k 1)))))
        (.call pRoot [k 2000, v 2] 0))))

/-- The time of g26. -/
def tG26 (D : ℕ) : ℕ := paramG₂₆Nat D * 32027 + 768





































/-! ## ⌊n²/√D⌋ and quotients rounded up -/

/-- queryCapNat(n, D).  Locals 0 and 1 are the arguments, local 2 is n⁴, local 3 the candidate. -/
def queryCapNatBody : Stmt :=
  (Light.Stmt.seq
    (.set 2
      ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (v 0) (v 0)) (v 0))
        (v 0)))
    (Light.Stmt.seq (.set 3 (k 0))
      (Light.Stmt.seq
        (.while
          (Light.Cond.le
            ((Light.Expr.op Light.Op.mul)
              ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v 3) (k 1))
                ((Light.Expr.op Light.Op.add) (v 3) (k 1)))
              (v 1))
            (v 2))
          (.set 3 ((Light.Expr.op Light.Op.add) (v 3) (k 1))))
        (.set 0 (v 3)))))

/-- The time of queryCapNat. -/
def tQueryCapNat (n D : ℕ) : ℕ := 18 * queryCapNat n D + 26

























































/-- ceilDiv(a, b).  Locals 0 and 1 are the arguments, local 2 is the candidate q, local 3 is
q b. -/
def ceilDivBody : Stmt :=
  (Light.Stmt.seq (.set 2 (k 0))
    (Light.Stmt.seq (.set 3 (k 0))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v 3) (v 0))
          (Light.Stmt.seq (.set 3 ((Light.Expr.op Light.Op.add) (v 3) (v 1)))
            (.set 2 ((Light.Expr.op Light.Op.add) (v 2) (k 1)))))
        (.set 0 (v 2)))))

/-- The time of ceilDiv. -/
def tCeilDiv (a b : ℕ) : ℕ := 12 * (a ⌈/⌉ b) + 10





























end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_ClaimAtParameters


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 17 for programs of the light language, with the two choices of parameters of Section 3.3

Theorem 17 reduces Exact Triangle to at most `4ng` instances of Lop-AE-SparseTri(n, D). As
a claim about programs: from every solver of Lop-AE-SparseTri there is a solver of Exact Triangle
whose time obeys the bound of the theorem, here with Strassen's algorithm for the matrix product
(`Claim.Theorem_17` with `strassen`).  The program is the host `et17`.

The host takes the procedures that compute `D` from `n` and `g` from `D` as parameters.  Here they
are the routines for the two choices of the proof of Theorem 19: "Let D be the largest power of four
with D ≤ n^{1/18} [...] and let g := ⌈D^{1/36}⌉", and "Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉".
The program is the solver's program, followed by the parameter routines (`paramProcs`), followed by
the procedures of the host.

1. The four routines are parameter procedures in the sense of the host (`paramProc_d5`,
   `paramProc_g5`, `paramProc_d26`, `paramProc_g26`).
2. The parameters and the numbers that the routines form are polynomially bounded
   (`polyBounded_paramD₅Nat`, `polyBounded_paramG₅Nat`, `polyBounded_wD5`, `polyBounded_wG5`,
   and the same for the second choice).  So the need of the host (word size, cells, depth of calls)
   is polynomially bounded if that of the solver is (`hostNeed_poly`).  With `et17_solves` this
   makes the host turn solvers into solvers (`host_of_paramProcs`).
3. The routines take `O(n)`, respectively `O(D)`, steps (`steps_tD5`, `steps_tG5`, `steps_tD26`,
   `steps_tG26`).  So the time of the host obeys the bound of the theorem (`obeysBound17_hostTime`).
   Together: `claim_theorem_17₅` and `claim_theorem_17₂₆`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The parameter routines -/

/-- The six parameter routines, placed behind a program of length `o`, at the numbers `o`, …,
`o + 5`.  The arguments are the numbers of the routines that a routine calls. -/
 def paramProcs (o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, d26Body (o + 1), d5Body (o + 2), g5Body (o + 1), g26Body (o + 1)]

/-- A bound on the numbers that `d26Body` forms. -/
 def wD26 (n : ℕ) : ℕ := (n + 1) * (paramD₂₆Nat n + 1) + 19







/-- A bound on the numbers that `g26Body` forms.  It looks for the least `g` with `g^2000 ≥ D^63`,
since `0.0315 = 63/2000`. -/
 def wG26 (D : ℕ) : ℕ := D ^ 63 * paramG₂₆Nat D + 2001








































/-! ## The parameters and the words are polynomially bounded -/


















































/-! ## The time of the parameter routines -/





























/-! ## The host with parameter routines -/





































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_Count


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The count of the proof of Theorem 17, read off the product PQ

"then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in
(PQ)[a,b]."  Here F(p) is the number of false positives of p, that is, of triples with S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ is the number of zero triangles.

This file proves that the routine countZero returns this sum, `countBy`.  It does not prove that the
sum is F(p) + Z₀: that is `countOf_eq`, a theorem about lists with no program in it.

countZero(rm, rab, mort, n, p): the cells from rm hold the product PQ, a matrix of 4^K vectors of p
coefficients each, in Z-order, where 2^K ≥ n; the cells from rab hold the residues of the weights
w(a,b) mod p, that of (a, b) at place a n + b; the cells from mort hold the table of `spread`, from
which the place of a pair in Z-order is formed.  The routine goes through the pairs (a, b) in the
order of their places a n + b, reads the residue ϱ of w(a,b), forms (p - ϱ) mod p by one test, and
adds the coefficient number (p - ϱ) mod p of the vector of (a, b) (`countTerm`,
`countZeroAdd_spec`); then it steps to the next pair.  The loop is `countZero_spec`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace CountZero

/-- The local variables of countZero.  The arguments: Mat = rm, Residues = rab, Places = mort,
Num = n, Prime = p.  Then Square = n²; Idx = t = a n + b, the number of the pair; Row = a; Col = b;
Total, the sum; Expo, the exponent (p - ϱ) mod p. -/
abbrev Mat : ℕ := 0
@[inherit_doc Mat] abbrev Residues : ℕ := 1
@[inherit_doc Mat] abbrev Places : ℕ := 2
@[inherit_doc Mat] abbrev Num : ℕ := 3
@[inherit_doc Mat] abbrev Prime : ℕ := 4
@[inherit_doc Mat] abbrev Square : ℕ := 5
@[inherit_doc Mat] abbrev Idx : ℕ := 6
@[inherit_doc Mat] abbrev Row : ℕ := 7
@[inherit_doc Mat] abbrev Col : ℕ := 8
@[inherit_doc Mat] abbrev Total : ℕ := 9
@[inherit_doc Mat] abbrev Expo : ℕ := 10

end CountZero

open CountZero in
/-- The term of the pair (a, b) is added to the sum. -/
def countZeroAdd : Stmt :=
  (Light.Stmt.seq (.set Expo (M ((Light.Expr.op Light.Op.add) (v Residues) (v Idx))))
    (Light.Stmt.seq
      (.ite (Light.Cond.eq (v Expo) (k 0)) .skip (.set Expo ((Light.Expr.op Light.Op.sub) (v Prime) (v Expo))))
      (.set Total
        ((Light.Expr.op Light.Op.add) (v Total)
          (M
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v Mat)
                ((Light.Expr.op Light.Op.mul)
                  ((Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.mul) (k 2) (M ((Light.Expr.op Light.Op.add) (v Places) (v Row))))
                    (M ((Light.Expr.op Light.Op.add) (v Places) (v Col))))
                  (v Prime)))
              (v Expo)))))))

open CountZero in
/-- countZero(rm, rab, mort, n, p).  The sum is returned in local 0. -/
def countZeroBody : Stmt :=
  (Light.Stmt.seq (.set Square ((Light.Expr.op Light.Op.mul) (v Num) (v Num)))
    (Light.Stmt.seq (.set Row (k 0))
      (Light.Stmt.seq (.set Col (k 0))
        (Light.Stmt.seq (.set Total (k 0))
          (Light.Stmt.seq (.for Idx (v Square) (Light.Stmt.seq countZeroAdd (nextPair Row Col Num)))
            (.set 0 (v Total)))))))

/-- An upper bound on the number of steps of countZero. -/
def countZeroTime (n : ℕ) : ℕ := 60 * (n * n) + 30

/-- The term of the pair number i: the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]. -/
def countTerm (n p : ℕ) (RM : List ℤ) (RAB : List ℕ) (i : ℕ) : ℤ :=
  RM.getD (zIdx (i / n) (i % n) * p + (p - RAB.getD i 0) % p) 0

/-- What countZero needs: where the arrays lie, and what they hold.  RM is the list of the 4^K p
coefficients at rm, of absolute value at most V, and RAB is the list of the n² residues at rab. -/
structure CountZeroPre (lim : Limits) (μ : ℕ → ℤ) (rm rab mort n K p : ℕ) (RM : List ℤ)
    (RAB : List ℕ) (V : ℤ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  mat : ArrayAt μ rm RM (4 ^ K * p) V lim.space
  res : IndexAt μ rab RAB (n * n) p lim.space
  table : ListAt μ mort (spreadList (2 ^ K)) (2 ^ K) lim.space
  n_le : n ≤ 2 ^ K
  rm_lt : rm + 4 ^ K * p < lim.space
  sum_le : ((n * n : ℕ) : ℤ) * V ≤ lim.word

namespace CountZeroPre

variable {μ : ℕ → ℤ} {rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ} {t : ℕ}




















end CountZeroPre

variable {μ : ℕ → ℤ} {rm rab mort n K p : ℕ} {RM : List ℤ} {RAB : List ℕ} {V : ℤ}













































































































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_RingOps


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Vectors: sums, differences, and the product in ℤ[x]/(x^p - 1)

The proof of Theorem 17 computes with matrices over the ring ℤ[x]/(x^p - 1); an element of the ring
is a vector of p integers, and a ring operation takes "O(p²) word operations".

* vlin(dst, a, b, n, s): dst[i] := a[i] + s b[i] for i < n, with s = 1 or s = -1; dst may be the
  segment a itself (accumulation).  It is one pass (`vlin_spec`), and what it writes is `vadd` or
  `vsub` (`vlinList_one`, `vlinList_neg_one`).
* cconv(dst, a, b, p): dst := the cyclic convolution of a and b.  The inner loop adds up the p terms
  of one entry (`cconvEntry_spec`), the outer loop stores the p entries (`cconv_spec`).  The partial
  sums stay below p α β if the entries of a and b are bounded by α and β (`abs_convPartialSum_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Sums and differences -/

namespace Vlin

/-- The local variables of vlin: the arguments dst, a, b, n, s, and the counter. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Len : ℕ := 3
@[inherit_doc Dst] abbrev Sign : ℕ := 4
@[inherit_doc Dst] abbrev Idx : ℕ := 5

end Vlin

open Vlin in
/-- vlin(dst, a, b, n, s): for i < n: dst[i] := a[i] + s b[i]. -/
def vlinBody : Stmt :=
  pass Idx (v Len) (v Dst) (((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v ArgA) (v Idx)))
                              ((Light.Expr.op Light.Op.mul) (v Sign) (M ((Light.Expr.op Light.Op.add) (v ArgB) (v Idx))))))

/-- The list that vlin writes. -/
def vlinList (s : ℤ) (A B : List ℤ) : List ℤ := List.zipWith (fun x y => x + s * y) A B












/-- Entry j of that list. -/
def vlinAt (s : ℤ) (A B : List ℤ) (j : ℕ) : ℤ := A.getD j 0 + s * B.getD j 0

/-- What vlin assumes: the lists A and B of n numbers of absolute value at most V stand at a and b;
the n cells at dst lie in the memory, do not meet b, and are the cells at a or do not meet them. -/
structure VlinPre (lim : Limits) (μ : ℕ → ℤ) (dst a b n : ℕ) (s V : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A n V lim.space
  opB : ArrayAt μ b B n V lim.space
  sign : |s| ≤ 1
  word : 2 * V ≤ lim.word := by first
                                  | omega
                                  | ( (try have := Light.Std.space_le (by assumption))
                                      (try have := Light.Std.const_le (by assumption))
                                      simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  space : dst + n ≤ lim.space := by first
                                      | omega
                                      | ( (try have := Light.Std.space_le (by assumption))
                                          (try have := Light.Std.const_le (by assumption))
                                          simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  apartA : dst = a ∨ dst + n ≤ a ∨ a + n ≤ dst := by first
                                                             | omega
                                                             | ( (try have := Light.Std.space_le (by assumption))
                                                                 (try have := Light.Std.const_le (by assumption))
                                                                 simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  apartB : dst + n ≤ b ∨ b + n ≤ dst := by first
                                                 | omega
                                                 | ( (try have := Light.Std.space_le (by assumption))
                                                     (try have := Light.Std.const_le (by assumption))
                                                     simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)














































/-! ## The product -/

/-- A term of the convolution. -/
def convTerm (p : ℕ) (A B : List ℤ) (r i : ℕ) : ℤ :=
  A.getD i 0 * B.getD (if i ≤ r then r - i else r + p - i) 0

/-- The sum of the first j terms of entry r of the convolution. -/
def convPartialSum (p : ℕ) (A B : List ℤ) (r j : ℕ) : ℤ :=
    ((List.range j).map (convTerm p A B r)).sum










section bounds

variable {p : ℕ} {A B : List ℤ} {α β : ℤ}














end bounds

namespace Cconv

/-- The local variables of cconv: the arguments dst, a, b, p; the number r of the entry; the number
i of the term; the sum (Acc); the index into b. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Len : ℕ := 3
@[inherit_doc Dst] abbrev Row : ℕ := 4
@[inherit_doc Dst] abbrev Idx : ℕ := 5
@[inherit_doc Dst] abbrev Acc : ℕ := 6
@[inherit_doc Dst] abbrev Jdx : ℕ := 7

end Cconv

open Cconv in
/-- One term: j := r - i or r + p - i; sum := sum + a[i] b[j]. -/
def cconvTerm : Stmt :=
  (Light.Stmt.seq
    (.ite (Light.Cond.le (v Idx) (v Row)) (.set Jdx ((Light.Expr.op Light.Op.sub) (v Row) (v Idx)))
      (.set Jdx ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v Row) (v Len)) (v Idx))))
    (.set Acc
      ((Light.Expr.op Light.Op.add) (v Acc)
        ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v ArgA) (v Idx)))
          (M ((Light.Expr.op Light.Op.add) (v ArgB) (v Jdx)))))))

open Cconv in
/-- One entry: sum := the entry number r of the convolution. -/
def cconvEntry : Stmt :=
  (Light.Stmt.seq (.set Acc (k 0)) (.for Idx (v Len) cconvTerm))

open Cconv in
/-- cconv(dst, a, b, p): for r < p: dst[r] := the entry number r. -/
def cconvBody : Stmt :=
  .for Row (v Len) ((Light.Stmt.seq cconvEntry (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Row)) (v Acc))))

/-- What the inner loop of cconv assumes: the lists A and B of p numbers, bounded by α and β, stand
at a and b, and p α β fits in a word. -/
structure CconvPre (lim : Limits) (μ : ℕ → ℤ) (a b p : ℕ) (α β : ℤ) (A B : List ℤ) : Prop where
  opA : ArrayAt μ a A p α lim.space
  opB : ArrayAt μ b B p β lim.space
  word : p * (α * β) ≤ lim.word
  nonnegA : 0 ≤ α := by first
                           | omega
                           | ( (try have := Light.Std.space_le (by assumption))
                               (try have := Light.Std.const_le (by assumption))
                               simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  nonnegB : 0 ≤ β := by first
                           | omega
                           | ( (try have := Light.Std.space_le (by assumption))
                               (try have := Light.Std.const_le (by assumption))
                               simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  room : 2 * p < lim.space := by first
                                 | omega
                                 | ( (try have := Light.Std.space_le (by assumption))
                                     (try have := Light.Std.const_le (by assumption))
                                     simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

section cconv

variable {μ : ℕ → ℤ} {dst a b p r : ℕ} {α β : ℤ} {A B : List ℤ}



























































open Cconv in
/-- The state of cconv before round r: the first r entries are written, and no cell outside dst has
changed. -/
def CconvInv (μ : ℕ → ℤ) (dst a b p : ℕ) (A B : List ℤ) (r : ℕ) (σ : State) : Prop :=
  ∃ (i s t : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [dst, a, b, p, r, i, s, t], μ'⟩ ∧
    (∀ e < r, μ' (dst + e) = convPartialSum p A B e p) ∧ SameOutside μ μ' dst p


















































end cconv

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_SizeTable


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The table of the sizes of Strassen's recursion

szTable(dst, p, J) writes the sizes p, 4p, …, 4^J p of the matrices of Strassen's recursion, the
list `szList p J`, and changes nothing else (`szTable_spec`, `szTable_meets`).
-/

@[expose] public section

namespace Light.Sec3

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The table of the sizes: 4^i p for i ≤ J. -/
def szList (p J : ℕ) : List ℤ := (List.range (J + 1)).map fun i : ℕ => ((4 ^ i * p : ℕ) : ℤ)




namespace SzTable

/-- The local variables of szTable: the arguments dst, p, J; the exponent; the entry. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Prime : ℕ := 1
@[inherit_doc Dst] abbrev Top : ℕ := 2
@[inherit_doc Dst] abbrev Exp : ℕ := 3
@[inherit_doc Dst] abbrev Entry : ℕ := 4

end SzTable

open SzTable in
/-- szTable(dst, p, J). -/
def szTableBody : Stmt :=
  (Light.Stmt.seq (.set Exp (k 0))
    (Light.Stmt.seq (.set Entry (v Prime))
      (Light.Stmt.seq (.store (v Dst) (v Entry))
        (.while (Light.Cond.lt (v Exp) (v Top))
          (Light.Stmt.seq (.set Entry ((Light.Expr.op Light.Op.mul) (k 4) (v Entry)))
            (Light.Stmt.seq (.set Exp ((Light.Expr.op Light.Op.add) (v Exp) (k 1)))
              (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Exp)) (v Entry))))))))

/-- An upper bound on the number of steps of szTable. -/
def tSzTable (J : ℕ) : ℕ := 17 * J + 11






/-- The state of szTable before round j: the entries p, …, 4^j p are written, the last of them is in
a local, and no cell outside the table has changed. -/
def SzInv (μ : ℕ → ℤ) (dst p J j : ℕ) (σ : State) : Prop :=
  ∃ μ', σ = ⟨frame [dst, p, J, j, (4 ^ j * p : ℕ)], μ'⟩ ∧ Seg μ' dst (szList p j) ∧
    SameOutside μ μ' dst (J + 1)















































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Sec3_Theorem17_Hashing


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Theorem 17, first step: hashing modulo a prime

The first step of the proof of Theorem 17 reduces the weights modulo a prime `p` in the range
`[√D/2, √D)` with few false positives.

* **Counting.**  The number of triples with `S(a,b,c) ≡ 0 (mod p)` is `F(p) + Z₀`
  (`TriangleInstance.countZeroMod_eq`), and it can be read off the product of two matrices over
  `ℤ[x]/(x^p − 1)` (`TriangleInstance.coeff_matP_mul_matQ`,
  `TriangleInstance.F_add_Z₀_eq_sum_coeff`).  There are fewer than `√D` primes in the range
  (`card_primesInRange_lt`).
* **Selecting.**  The prime with the smallest count exists
  (`TriangleInstance.exists_isSelectedPrime`) and has the fewest false positives
  (`TriangleInstance.IsSelectedPrime.F_le`).
* **The bound on `F(p)`**, `TriangleInstance.F_le_of_le_card_primesInRange` and
  `TriangleInstance.exists_F_le`.  A triple is a false positive of at most `log_{√D/2}(3n^ν)` primes
  in the range (`TriangleInstance.card_falsePositive_primes_le`), so the numbers `F(q)` add up to at
  most `n³` times that (`TriangleInstance.sum_F_le`); there are `Ω(√D/log D)` primes in the range
  (`exists_le_card_primesInRange`); `F(p)` is at most the average
  (`TriangleInstance.IsSelectedPrime.F_mul_card_le_sum`); and `log D ≤ 4 log(√D/2)`
  (`log_le_four_mul_log_sqrt_div_two`).  The constant of the bound has a name,
  `Hashing.falsePositiveConst`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ### The primes in the range -/

/-- Proof of Theorem 17, "a prime p ∈ [√D/2, √D)": the primes in the range are the primes `p` with
`√D/2 ≤ p < √D`.  (The bound `p < D` in the definition excludes none of them.) -/
theorem mem_primesInRange {D p : ℕ} :
    p ∈ primesInRange D ↔ p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D := by
  unfold primesInRange
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- From `p < √D` we get `p ≤ p² < D`.
  have hsq : p ^ 2 < D := by exact_mod_cast (Real.lt_sqrt (Nat.cast_nonneg p)).1 h.2.2
  exact (Nat.le_self_pow two_ne_zero p).trans_lt hsq

/-! ### The ring `ℤ[x]/(x^p − 1)` -/

open Polynomial in
/-- Proof of Theorem 17: "the ring ℤ[x]/(x^p − 1)".  (`Polynomial.C 1` is the constant polynomial
1.) -/
abbrev CyclicRing (p : ℕ) : Type := AdjoinRoot ((X : ℤ[X]) ^ p - C 1)

namespace CyclicRing

open Polynomial

variable {p : ℕ}

/-- The element `x` of `ℤ[x]/(x^p − 1)`. -/
noncomputable def x (p : ℕ) : CyclicRing p := AdjoinRoot.root _

/-- Proof of Theorem 17: "the coefficient of x^r" in an element `z` of `ℤ[x]/(x^p − 1)`, for `0 ≤ r
< p`, as a linear map: the coefficient of `x^r` in the unique polynomial of degree less than `p`
that represents `z` (Mathlib's `AdjoinRoot.modByMonicHom` gives that polynomial; it asks for the
fact that `x^p − 1` is monic, which holds as `p ≠ 0`). -/
noncomputable def coeff (hp : p ≠ 0) (r : ℕ) : CyclicRing p →ₗ[ℤ] ℤ :=
  lcoeff ℤ r ∘ₗ AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp)
























end CyclicRing












/-! ### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

namespace TriangleInstance

variable {n : ℕ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17: "A false positive of p is a triple (a,b,c) with S(a,b,c) ≠ 0 and p ∣
S(a,b,c)". -/
def IsFalsePositive (p : ℕ) (t : Fin n × Fin n × Fin n) : Prop :=
  T.S t.1 t.2.1 t.2.2 ≠ 0 ∧ (p : ℤ) ∣ T.S t.1 t.2.1 t.2.2

open Classical in
/-- Proof of Theorem 17: "let F(p) denote the number of false positives of p". -/
noncomputable def F (p : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => T.IsFalsePositive p t).card

open Classical in
/-- Proof of Theorem 17: "Z₀, the number of zero triangles". -/
noncomputable def Z₀ : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => T.IsZeroTriangle t.1 t.2.1 t.2.2).card

/-- Proof of Theorem 17: "This number is the number of false positives F(p) plus Z₀, the number of
zero triangles, which does not depend on p." -/
theorem countZeroMod_eq (p : ℕ) : T.countZeroMod p = T.F p + T.Z₀ := by
  classical
  simp only [countZeroMod, F, Z₀, Finset.card_filter, ← Finset.sum_add_distrib]
  -- A triple with `p ∣ S(a,b,c)` is a zero triangle or a false positive, and not both.
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h0 : T.S t.1 t.2.1 t.2.2 = 0 <;>
    simp [IsFalsePositive, IsZeroTriangle, Int.modEq_zero_iff_dvd, h0]

/-- Proof of Theorem 17: "let P[a,c] := x^{w(a,c) mod p}", a matrix over `ℤ[x]/(x^p − 1)`.  `w mod
p` is the residue in `{0, …, p − 1}`. -/
noncomputable def matP (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicRing p) :=
  Matrix.of fun a c => CyclicRing.x p ^ (T.wAC a c % (p : ℤ)).toNat

/-- Proof of Theorem 17: "and Q[c,b] := x^{w(b,c) mod p}". -/
noncomputable def matQ (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicRing p) :=
  Matrix.of fun c b => CyclicRing.x p ^ (T.wBC b c % (p : ℤ)).toNat



















































end TriangleInstance


















/-! ### Selecting the prime -/

namespace TriangleInstance

variable {n D p : ℕ} {κ : ℝ} (T : TriangleInstance ℤ n)







/-- Proof of Theorem 17: "We select the prime with the smallest count, which is also the prime with
the fewest false positives". -/
theorem IsSelectedPrime.F_le {T : TriangleInstance ℤ n} (hp : T.IsSelectedPrime D p) :
    ∀ q ∈ primesInRange D, T.F p ≤ T.F q := by
  intro q hq
  have h := hp.2 q hq
  rw [countZeroMod_eq, countZeroMod_eq] at h
  omega

/-! ### The bound on the number of false positives of the selected prime -/

/-- Proof of Theorem 17: "|S(a,b,c)| ≤ 3n^ν". -/
theorem abs_S_le (hT : T.WeightsPolyBounded κ) (a b c : Fin n) :
    ((|T.S a b c| : ℤ) : ℝ) ≤ 3 * (n : ℝ) ^ κ := by
  obtain ⟨hAB, hBC, hAC⟩ := hT
  have habs : |T.S a b c| ≤ |T.wAB a b| + |T.wBC b c| + |T.wAC a c| := abs_add_three _ _ _
  have hcast : ((|T.S a b c| : ℤ) : ℝ)
      ≤ ((|T.wAB a b| : ℤ) : ℝ) + ((|T.wBC b c| : ℤ) : ℝ) + ((|T.wAC a c| : ℤ) : ℝ) := by
    exact_mod_cast habs
  linarith [hAB a b, hBC b c, hAC a c]

open Classical in
/-- Proof of Theorem 17: "a triple with S(a,b,c) ≠ 0 is a false positive exactly of the primes in
the range that divide S(a,b,c).  Since 0 < |S(a,b,c)| ≤ 3n^ν and these primes are at least √D/2,
there are at most log_{√D/2}(3n^ν) of them." -/
theorem card_falsePositive_primes_le (hD : 16 ≤ D) (hT : T.WeightsPolyBounded κ)
    (t : Fin n × Fin n × Fin n) (ht : T.S t.1 t.2.1 t.2.2 ≠ 0) :
    (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
      ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  have hsqrt := Real.four_le_sqrt_natCast_of_sixteen_le hD
  set divisors := (primesInRange D).filter fun p => T.IsFalsePositive p t
  have hmem : ∀ p ∈ divisors,
      p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℤ) ∣ T.S t.1 t.2.1 t.2.2 := by
    intro p hp
    obtain ⟨hrange, -, hdvd⟩ := Finset.mem_filter.1 hp
    obtain ⟨hprime, hge, -⟩ := mem_primesInRange.1 hrange
    exact ⟨hprime, hge, hdvd⟩
  -- The product of these primes divides `S(a,b,c)`, so it is at most `|S(a,b,c)| ≤ 3n^κ`.
  have hdvd : ∏ p ∈ divisors, p ∣ (T.S t.1 t.2.1 t.2.2).natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (hmem p hp).1.prime)
      fun p hp => Int.natCast_dvd.1 (hmem p hp).2.2
  have hprod : ∏ p ∈ divisors, (p : ℝ) ≤ 3 * (n : ℝ) ^ κ :=
    calc ∏ p ∈ divisors, (p : ℝ) = ((∏ p ∈ divisors, p : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
      _ ≤ ((T.S t.1 t.2.1 t.2.2).natAbs : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.2 ht) hdvd
      _ = ((|T.S t.1 t.2.1 t.2.2| : ℤ) : ℝ) := Nat.cast_natAbs _
      _ ≤ 3 * (n : ℝ) ^ κ := T.abs_S_le hT _ _ _
  -- Each of these primes is at least `√D/2`.
  have hpow : (Real.sqrt D / 2) ^ divisors.card ≤ ∏ p ∈ divisors, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith) fun p hp => (hmem p hp).2.1
  have hY : 0 < 3 * (n : ℝ) ^ κ := lt_of_lt_of_le (by positivity) (hpow.trans hprod)
  rw [Real.le_logb_iff_rpow_le (by linarith) hY, Real.rpow_natCast]
  exact hpow.trans hprod

/-- Proof of Theorem 17: "Hence the numbers of false positives of all the primes in the range add up
to at most n³ log_{√D/2}(3n^ν)." -/
theorem sum_F_le (hD : 16 ≤ D) (hκ : 1 ≤ κ) (hT : T.WeightsPolyBounded κ) :
    ((∑ p ∈ primesInRange D, T.F p : ℕ) : ℝ)
      ≤ (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  classical
  have hsqrt := Real.four_le_sqrt_natCast_of_sixteen_le hD
  -- Count the pairs (prime, false positive of that prime) triple by triple.
  have hswap : ∑ p ∈ primesInRange D, T.F p = ∑ t : Fin n × Fin n × Fin n,
      ((primesInRange D).filter fun p => T.IsFalsePositive p t).card := by
    simp only [F, Finset.card_filter]
    exact Finset.sum_comm
  have hterm : ∀ t : Fin n × Fin n × Fin n,
      (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
        ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
    intro t
    by_cases ht : T.S t.1 t.2.1 t.2.2 = 0
    · -- A zero triangle is a false positive of no prime.
      rw [Finset.filter_eq_empty_iff.2 fun p _ h => h.1 ht, Finset.card_empty, Nat.cast_zero]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fin.pos t.1
      have hpow : (1 : ℝ) ≤ (n : ℝ) ^ κ := Real.one_le_rpow hn (by linarith)
      exact Real.logb_nonneg (by linarith) (by linarith)
    · -- Otherwise this is the bound of `card_falsePositive_primes_le` for this triple.
      convert T.card_falsePositive_primes_le hD hT t ht
  rw [hswap, Nat.cast_sum]
  calc ∑ t : Fin n × Fin n × Fin n,
        (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
      ≤ ∑ _t : Fin n × Fin n × Fin n, Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end TriangleInstance

/-- Proof of Theorem 17: "By the prime number theorem there are Ω(√D/log D) primes in the range".

NOTE.  The proof of Theorem 17 needs this for every `D ≥ 16`, not only for large `D`, and so it is
stated.  It follows from a counting form of Bertrand's postulate; the prime number theorem is not
needed. -/
theorem exists_le_card_primesInRange :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D →
      c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := Nat.exists_forall_mul_sqrt_div_log_le_card_primes
  exact ⟨c, hc, fun D hD => hcount D hD _
    fun _ hp hge hlt => mem_primesInRange.2 ⟨hp, hge, hlt⟩⟩

/-- Proof of Theorem 17: "F(p) is at most the average over them", multiplied out. -/
theorem TriangleInstance.IsSelectedPrime.F_mul_card_le_sum {n D p : ℕ} {T : TriangleInstance ℤ n}
    (hp : T.IsSelectedPrime D p) :
    T.F p * (primesInRange D).card ≤ ∑ q ∈ primesInRange D, T.F q := by
  rw [mul_comm, ← smul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ hp.F_le

/-- Proof of Theorem 17: "log D = O(log(√D/2)) for D ≥ 16". -/
theorem log_le_four_mul_log_sqrt_div_two (D : ℕ) (hD : 16 ≤ D) :
    Real.log D ≤ 4 * Real.log (Real.sqrt D / 2) := by
  have hD16 : (16 : ℝ) ≤ D := by exact_mod_cast hD
  have hsqrt : 0 < Real.sqrt D := by linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD]
  -- `log(√D/2) = (log D)/2 - log 2`, and `4 log 2 = log 16 ≤ log D`.
  have hlog16 : 4 * Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 4 ≤ D by linarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  rw [Real.log_div hsqrt.ne' (by norm_num), Real.log_sqrt (by linarith)]
  linarith [hlog16]

/-- Proof of Theorem 17: "F(p) is at most the average over them, so [...] F(p) = O(n³
log(3n^ν)/√D)": if there are at least `c √D/log D` primes in the range, then `F(p) ≤ (4/c) n³
log(3n^κ)/√D`. -/
theorem TriangleInstance.F_le_of_le_card_primesInRange {n D p : ℕ} {κ c : ℝ}
    (T : TriangleInstance ℤ n) (hc : 0 < c)
    (hcard : c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ)) (hD : 16 ≤ D)
    (hDn : D ≤ n) (hκ : 1 ≤ κ) (hT : T.WeightsPolyBounded κ) (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^ κ) / Real.sqrt D) := by
  -- The quantities of the paper's sentence: `r = √D`, `Y = 3n^κ`, and the number of primes in the
  -- range.
  set r := Real.sqrt D
  set Y := 3 * (n : ℝ) ^ κ with hY
  set numPrimes := (primesInRange D).card
  have hr : 4 ≤ r := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogD_pos : 0 < Real.log D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hlogr_pos : 0 < Real.log (r / 2) := Real.log_pos (by linarith)
  have hlogY_nonneg : 0 ≤ Real.log Y := by
    have : 1 ≤ (n : ℝ) ^ κ := Real.one_le_rpow (by linarith) (by linarith)
    exact Real.log_nonneg (by rw [hY]; linarith)
  -- "F(p) is at most the average", multiplied out; the false positives of all the primes in the
  -- range add up to at most `n³ log_{r/2} Y`.
  have average : (T.F p : ℝ) * numPrimes ≤ (n : ℝ) ^ 3 * Real.logb (r / 2) Y :=
    le_trans (by exact_mod_cast hp.F_mul_card_le_sum) (T.sum_F_le hD hκ hT)
  -- The base of the logarithm changes: `log_{r/2} Y ≤ 4 log Y / log D`.
  have hlogD_le : Real.log D ≤ 4 * Real.log (r / 2) := log_le_four_mul_log_sqrt_div_two D hD
  have changeBase : Real.logb (r / 2) Y ≤ 4 * Real.log Y / Real.log D := by
    rw [Real.logb, div_le_div_iff₀ hlogr_pos hlogD_pos]
    linarith [mul_le_mul_of_nonneg_left hlogD_le hlogY_nonneg]
  rw [show 4 / c * ((n : ℝ) ^ 3 * Real.log Y / r) = 4 * (n : ℝ) ^ 3 * Real.log Y / (c * r) by
    field_simp, le_div_iff₀ (by positivity)]
  calc (T.F p : ℝ) * (c * r) = T.F p * (c * (r / Real.log D)) * Real.log D := by field_simp
    _ ≤ T.F p * numPrimes * Real.log D := by gcongr
    _ ≤ (n : ℝ) ^ 3 * Real.logb (r / 2) Y * Real.log D := by gcongr
    _ ≤ (n : ℝ) ^ 3 * (4 * Real.log Y / Real.log D) * Real.log D := by gcongr
    _ = 4 * (n : ℝ) ^ 3 * Real.log Y := by field_simp

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)". -/
theorem TriangleInstance.exists_F_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n D p : ℕ} {κ : ℝ}, 16 ≤ D → D ≤ n → 1 ≤ κ → ∀ T : TriangleInstance ℤ n,
      T.WeightsPolyBounded κ → T.IsSelectedPrime D p →
      (T.F p : ℝ) ≤ C * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by
  obtain ⟨c, hc, hcard⟩ := exists_le_card_primesInRange
  refine ⟨max 1 (8 / c), le_max_left _ _, fun {n D p κ} hD hDn hκ T hT hp => ?_⟩
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  -- `log(3n^κ) = log 3 + κ log n ≤ 2κ log n`, because `3 ≤ n` and `κ ≥ 1`.
  have hlog : Real.log (3 * (n : ℝ) ^ κ) ≤ 2 * κ * Real.log n := by
    have hlog3 : Real.log 3 ≤ κ * Real.log n :=
      (Real.log_le_log (by norm_num) (by linarith)).trans (le_mul_of_one_le_left hlogn hκ)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
    linarith [hlog3]
  calc (T.F p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^ κ) / Real.sqrt D) :=
        T.F_le_of_le_card_primesInRange hc (hcard D hD) hD hDn hκ hT hp
    _ ≤ 4 / c * ((n : ℝ) ^ 3 * (2 * κ * Real.log n) / Real.sqrt D) := by gcongr
    _ = 8 / c * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by ring
    _ ≤ max 1 (8 / c) * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by
        gcongr
        exact le_max_right _ _

/-- A name for the constant in "F(p) = [...] = O(ν n³ log n/√D)", for the bounds on running times
that are built on this one. -/
noncomputable def Hashing.falsePositiveConst : ℝ := Classical.choose TriangleInstance.exists_F_le













end ThreeSumApsp

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Cyclic


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The ring `ℤ[x]/(x^p − 1)` as vectors of `p` integers

The proof of Theorem 17 computes with matrices over the ring `ℤ[x]/(x^p − 1)`.  For a program an
element of the ring is the list of its `p` coefficients (`cycVec`).  This file shows that the
operations of the ring are operations on lists that use no division:

* zero, sums and differences are entrywise (`cycVec_zero`, `cycVec_add`, `cycVec_sub`);
* a power of `x` is a unit vector (`cycVec_x_pow`);
* multiplication is cyclic convolution, "O(p²) word operations" (`cycVec_mul`).  For the proof both
  factors are expanded in powers of `x` (`eq_sum_coeff`), and `x^i x^j` contributes to the
  coefficient of `x^r` exactly if `i + j ≡ r (mod p)`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- An element of `ℤ[x]/(x^p − 1)` as the list of its coefficients of `x^0, …, x^{p-1}`. -/
noncomputable def cycVec {p : ℕ} (hp : p ≠ 0) (z : CyclicRing p) : List ℤ :=
  (List.range p).map fun r => CyclicRing.coeff hp r z

/-- Entrywise sum. -/
def vadd (u v : List ℤ) : List ℤ := List.zipWith (· + ·) u v

/-- Entrywise difference. -/
def vsub (u v : List ℤ) : List ℤ := List.zipWith (· - ·) u v

/-- The vector of `x^k`, for `k < p`. -/
def vunit (p k : ℕ) : List ℤ := (List.range p).map fun i => if i = k then 1 else 0

/-- Cyclic convolution: entry `r` is the sum of `u_i v_j` over `i + j ≡ r (mod p)`.  The index `j`
is `r - i` or `r + p - i`. -/
def cconv (p : ℕ) (u v : List ℤ) : List ℤ :=
  (List.range p).map fun r =>
    ((List.range p).map fun i => u.getD i 0 * v.getD (if i ≤ r then r - i else r + p - i) 0).sum

variable {p : ℕ} (hp : p ≠ 0)

/-! ## Coefficients -/




































/-! ## Vectors -/























































end ThreeSumApsp.Spec

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Strassen


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Strassen's algorithm on lists, and the count of the proof of Theorem 17

Proof of Theorem 17: "Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm".
`strassenList` multiplies two `2^K × 2^K` matrices over `ℤ[x]/(x^p - 1)`, given as lists in Z-order,
and `countOf` reads the number of triples `(a,b,c)` with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≡ 0
(mod p)` off the product.

1. `zRing hp K α` is the list of the matrix `α` over the ring.  The operations on lists are the
   operations of the ring, entry by entry (`zRing_add`, `zRing_sub`), and the quadrants of a matrix
   are the quarters of its list (`quarter_zRing`, `zRing_succ`).
2. `strassenList_zRing`: the algorithm computes the product.  By induction on `K`; Strassen's seven
   products give the four quadrants of the product by an identity that holds summand by summand.
   It makes `7^K` multiplications in the ring, which is `O(n^{log₂ 7})` (`seven_pow_clog_le`).
3. The lists that the routine fills are the matrices `P` and `Q` of the proof of Theorem 17, padded
   with zeros to `2^K` rows and columns (`matPList_eq_zRing`, `matQList_eq_zRing`), and the padding
   does not change the entries of the product (`sum_padP_mul_padQ`).
4. `countOf_eq`: the count is the count of the proof of Theorem 17.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

open Finset

/-! ## Matrices over the ring, as lists -/

section Ring

variable {p : ℕ} (hp : p ≠ 0) (K : ℕ)

/-- A matrix over the ring as a list in Z-order. -/
noncomputable def zRing (α : ℕ → ℕ → CyclicRing p) : List ℤ :=
  zList K fun a c => cycVec hp (α a c)




























end Ring

/-! ## Strassen's algorithm -/

/-- Strassen's algorithm [Str69] for `2^j × 2^j` matrices over `ℤ[x]/(x^p - 1)` in Z-order. -/
def strassenList (p : ℕ) : ℕ → List ℤ → List ℤ → List ℤ
  | 0, A, B => cconv p A B
  | j + 1, A, B =>
    let q := 4 ^ j * p
    let a11 := quarter q 0 A; let a12 := quarter q 1 A
    let a21 := quarter q 2 A; let a22 := quarter q 3 A
    let b11 := quarter q 0 B; let b12 := quarter q 1 B
    let b21 := quarter q 2 B; let b22 := quarter q 3 B
    let m1 := strassenList p j (vadd a11 a22) (vadd b11 b22)
    let m2 := strassenList p j (vadd a21 a22) b11
    let m3 := strassenList p j a11 (vsub b12 b22)
    let m4 := strassenList p j a22 (vsub b21 b11)
    let m5 := strassenList p j (vadd a11 a12) b22
    let m6 := strassenList p j (vsub a21 a11) (vadd b11 b12)
    let m7 := strassenList p j (vsub a12 a22) (vadd b21 b22)
    vadd (vsub (vadd m1 m4) m5) m7 ++ vadd m3 m5 ++ vadd m2 m4 ++ vadd (vadd (vsub m1 m2) m3) m6





































/-! ## The count of the proof of Theorem 17 -/

/-- The zero vector. -/
abbrev zeros (len : ℕ) : List ℤ := List.replicate len 0

/-- Proof of Theorem 17: `P[a,c] := x^{w(a,c) mod p}`, padded with zeros to `2^K` rows and columns;
`RAC` holds the residues. -/
def matPList (n p K : ℕ) (RAC : List ℕ) : List ℤ :=
  zList K fun a c => if a < n ∧ c < n then vunit p (RAC.getD (a * n + c) 0) else zeros p

/-- Proof of Theorem 17: `Q[c,b] := x^{w(b,c) mod p}`. -/
def matQList (n p K : ℕ) (RBC : List ℕ) : List ℤ :=
  zList K fun c b => if c < n ∧ b < n then vunit p (RBC.getD (b * n + c) 0) else zeros p

/-- Proof of Theorem 17: "the sum over the pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod
p} in (PQ)[a,b]"; `RM` is `PQ` in Z-order. -/
def countBy (n p : ℕ) (RM : List ℤ) (RAB : List ℕ) : ℤ :=
  ((List.range (n * n)).map fun i =>
    RM.getD (zIdx (i / n) (i % n) * p + (p - RAB.getD i 0) % p) 0).sum

/-- The number `F(p) + Z₀` of triples with `p ∣ S(a,b,c)`, computed as in the proof of Theorem 17.
-/
def countOf (n p : ℕ) (AB BC AC : List ℤ) : ℤ :=
  let K := Nat.clog 2 n
  countBy n p (strassenList p K (matPList n p K (residList p AC)) (matQList n p K (residList p BC)))
    (residList p AB)

section Count

variable {n : ℕ} (T : TriangleInstance ℤ n) {p : ℕ}

/-- The matrix `P` of the proof of Theorem 17, padded with zeros. -/
noncomputable def padP (p : ℕ) (a c : ℕ) : CyclicRing p :=
  if h : a < n ∧ c < n then T.matP p ⟨a, h.1⟩ ⟨c, h.2⟩ else 0

/-- The matrix `Q` of the proof of Theorem 17, padded with zeros. -/
noncomputable def padQ (p : ℕ) (c b : ℕ) : CyclicRing p :=
  if h : c < n ∧ b < n then T.matQ p ⟨c, h.1⟩ ⟨b, h.2⟩ else 0










variable (n) (AB BC AC : List ℤ)











































end Count

end ThreeSumApsp.Spec

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_StrassenFacts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Strassen's algorithm in seven uniform phases: the pure side

An entry of a matrix is a vector of `p` numbers, an element of the ring ℤ[x]/(x^p - 1), whose
product is `cconv p`; `vlinList s A B` is the list `A + s B`, which the routine vlin writes.  The
routine for Strassen's algorithm clears the four quarters of the result and then runs seven
phases.  A phase forms `S = A₁ + s_A A₂`, `T = B₁ + s_B B₂`, `M = S · T` (recursively) and adds
`s₁ M` and `s₂ M` to two quarters of the result; the signs are 1, -1 or 0.  This file has the facts
about lists that the proof about the routine uses:

* lengths (`length_vlinList`, `length_quarter`, `length_strassenList`);
* magnitudes: for operands bounded by `α` and `β`, all numbers that are formed at level `j` are
  bounded by `strassenBound p j α β = 16^j p α β` (`absLe_strassenList`);
* the seven phases give `strassenList` (`strassenList_succ_eq_phases`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec














































































































/-- The product of a phase. -/
def phaseM (p j : ℕ) (sA : ℤ) (A1 A2 : List ℤ) (sB : ℤ) (B1 B2 : List ℤ) : List ℤ :=
  strassenList p j (vlinList sA A1 A2) (vlinList sB B1 B2)

/-- The bound on all the numbers that the routine forms at level `j`, for operands bounded by `α`
and `β`. -/
def strassenBound (p j : ℕ) (α β : ℤ) : ℤ := 16 ^ j * (p * α * β)

























































































































































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_Strassen


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Strassen's algorithm for matrices over ℤ[x]/(x^p - 1) in Z-order

"Computing PQ takes […] O(n^{log₂ 7}) with Strassen's algorithm" (proof of Theorem 17).

strassen(dst, a, b, j, szt, p, scr): dst := a · b for 2^j × 2^j matrices whose entries are vectors
of p numbers, stored in Z-order, so that the four quadrants of a matrix are the four quarters of its
segment.  szt is the address of the table of the sizes 4^i p, and scr is scratch space.

* At level 0 the product is one product in the ring (`strassen_zero`).
* At level j + 1 the routine clears dst and runs seven phases (`strassen_succ`).  phase(a1, a2, sA,
  b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q) forms S = a1 + sA a2 and T = b1 + sB b2 in the
  scratch space, M = S · T by a recursive call, and adds s1 M to c1 and s2 M to c2 (`phase_meets`).
* Between two phases the four quarters of dst hold four lists, and the operands and the table are in
  place (`StrInv`); a phase changes two of the lists (`phase_step`).  After the seven phases the
  four lists are the four quadrants of the product (`sevenPhases_spec`).
* `strassen_spec` is the induction on the level: the product stands at dst after at most
  `strSteps p j` steps, and nothing has changed outside dst and `strScr p j` cells of scratch space.
  The recursion `strSteps` is bounded where the running times are added up.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

/-- The numbers of the procedures that Strassen's algorithm consists of. -/
structure StrNums : Type where
  pVlin : ℕ
  pCconv : ℕ
  pFill : ℕ
  pPhase : ℕ
  pStr : ℕ

namespace Phase

/-- The local variables of phase: the arguments a1, a2, sA, b1, b2, sB, c1, s1, c2, s2, j, szt, p,
scr, q, and a local that takes the results of the calls. -/
abbrev OpA1 : ℕ := 0
@[inherit_doc OpA1] abbrev OpA2 : ℕ := 1
@[inherit_doc OpA1] abbrev SignA : ℕ := 2
@[inherit_doc OpA1] abbrev OpB1 : ℕ := 3
@[inherit_doc OpA1] abbrev OpB2 : ℕ := 4
@[inherit_doc OpA1] abbrev SignB : ℕ := 5
@[inherit_doc OpA1] abbrev Out1 : ℕ := 6
@[inherit_doc OpA1] abbrev Sign1 : ℕ := 7
@[inherit_doc OpA1] abbrev Out2 : ℕ := 8
@[inherit_doc OpA1] abbrev Sign2 : ℕ := 9
@[inherit_doc OpA1] abbrev Level : ℕ := 10
@[inherit_doc OpA1] abbrev Sizes : ℕ := 11
@[inherit_doc OpA1] abbrev Prime : ℕ := 12
@[inherit_doc OpA1] abbrev Scr : ℕ := 13
@[inherit_doc OpA1] abbrev Size : ℕ := 14
@[inherit_doc OpA1] abbrev Res : ℕ := 15

end Phase

open Phase in
/-- The operands of a phase: S := a1 + sA a2 at scr, and T := b1 + sB b2 at scr + q. -/
def phaseOpnds (ν : StrNums) : Stmt :=
  (Light.Stmt.seq (.call ν.pVlin [v Scr, v OpA1, v OpA2, v Size, v SignA] Res)
    (.call ν.pVlin [(Light.Expr.op Light.Op.add) (v Scr) (v Size), v OpB1, v OpB2, v Size, v SignB] Res))

open Phase in
/-- The end of a phase: c1 := c1 + s1 M and c2 := c2 + s2 M, where M stands at scr + 2 q. -/
def phaseAccum (ν : StrNums) : Stmt :=
  (Light.Stmt.seq
    (.call ν.pVlin
      [v Out1, v Out1, (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Scr) (v Size)) (v Size), v Size,
        v Sign1]
      Res)
    (.call ν.pVlin
      [v Out2, v Out2, (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Scr) (v Size)) (v Size), v Size,
        v Sign2]
      Res))

open Phase in
/-- phase(a1, a2, sA, b1, b2, sB, c1, s1, c2, s2, j, szt, p, scr, q): the operands; M := S · T at
scr + 2 q, with the scratch space from scr + 3 q on; the end. -/
def phaseBody (ν : StrNums) : Stmt :=
  (Light.Stmt.seq (phaseOpnds ν)
    (Light.Stmt.seq
      (.call ν.pStr
        [(Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Scr) (v Size)) (v Size), v Scr,
          (Light.Expr.op Light.Op.add) (v Scr) (v Size), v Level, v Sizes, v Prime,
          (Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Scr) (v Size)) (v Size)) (v Size)]
        Res)
      (phaseAccum ν)))

namespace Str

/-- The local variables of strassen: the arguments dst, a, b, j, szt, p, scr; the numbers q, 2q, 3q,
where q is the size of a quarter; j - 1; a local that is not used; a local that takes the results of
the calls. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev ArgA : ℕ := 1
@[inherit_doc Dst] abbrev ArgB : ℕ := 2
@[inherit_doc Dst] abbrev Level : ℕ := 3
@[inherit_doc Dst] abbrev Sizes : ℕ := 4
@[inherit_doc Dst] abbrev Prime : ℕ := 5
@[inherit_doc Dst] abbrev Scr : ℕ := 6
@[inherit_doc Dst] abbrev Size1 : ℕ := 7
@[inherit_doc Dst] abbrev Size2 : ℕ := 8
@[inherit_doc Dst] abbrev Size3 : ℕ := 9
@[inherit_doc Dst] abbrev Below : ℕ := 10
@[inherit_doc Dst] abbrev Res : ℕ := 12

end Str

open Str in
/-- The address of the quarter number t of the segment whose address is in local x. -/
@[simp] def qAddr (x : ℕ) : ℕ → Expr
  | 0 => v x
  | 1 => ((Light.Expr.op Light.Op.add) (v x) (v Size1))
  | 2 => ((Light.Expr.op Light.Op.add) (v x) (v Size2))
  | _ => ((Light.Expr.op Light.Op.add) (v x) (v Size3))

/-- The sign 1. -/
@[simp] def sPos : Expr := k 1

/-- The sign 0. -/
@[simp] def sNil : Expr := k 0

/-- The sign -1. -/
@[simp] def sNeg : Expr := ((Light.Expr.op Light.Op.sub) (k 0) (k 1))

open Str in
/-- A call of phase from the body of strassen: the operands are the quarters number a1, a2 of a and
b1, b2 of b, and the results go to the quarters number c1, c2 of dst. -/
def phaseCall (ν : StrNums) (a1 a2 : ℕ) (sA : Expr) (b1 b2 : ℕ) (sB : Expr) (c1 : ℕ) (s1 : Expr)
    (c2 : ℕ) (s2 : Expr) : Stmt :=
  .call ν.pPhase [qAddr ArgA a1, qAddr ArgA a2, sA, qAddr ArgB b1, qAddr ArgB b2, sB, qAddr Dst c1,
    s1, qAddr Dst c2, s2, v Below, v Sizes, v Prime, v Scr, v Size1] Res

/-- The seven phases. -/
def sevenPhases (ν : StrNums) : Stmt :=
  (Light.Stmt.seq (phaseCall ν 0 3 sPos 0 3 sPos 0 sPos 3 sPos)
    (Light.Stmt.seq (phaseCall ν 2 3 sPos 0 0 sNil 2 sPos 3 sNeg)
      (Light.Stmt.seq (phaseCall ν 0 0 sNil 1 3 sNeg 1 sPos 3 sPos)
        (Light.Stmt.seq (phaseCall ν 3 3 sNil 2 0 sNeg 0 sPos 2 sPos)
          (Light.Stmt.seq (phaseCall ν 0 1 sPos 3 3 sNil 0 sNeg 1 sPos)
            (Light.Stmt.seq (phaseCall ν 2 0 sNeg 0 1 sPos 3 sPos 0 sNil)
              (phaseCall ν 1 3 sNeg 2 3 sPos 0 sPos 3 sNil)))))))

open Str in
/-- strassen(dst, a, b, j, szt, p, scr). -/
def strBody (ν : StrNums) : Stmt :=
  .ite ((Light.Cond.eq (v Level) (k 0)))
    (.call ν.pCconv [v Dst, v ArgA, v ArgB, v Prime] Res)
    ((Light.Stmt.seq (.set Below ((Light.Expr.op Light.Op.sub) (v Level) (k 1)))
       (Light.Stmt.seq (.set Size1 (M ((Light.Expr.op Light.Op.add) (v Sizes) (v Below))))
         (Light.Stmt.seq (.set Size2 ((Light.Expr.op Light.Op.add) (v Size1) (v Size1)))
           (Light.Stmt.seq (.set Size3 ((Light.Expr.op Light.Op.add) (v Size2) (v Size1)))
             (Light.Stmt.seq (.call ν.pFill [v Dst, (Light.Expr.op Light.Op.add) (v Size3) (v Size1), k 0] Res)
               (sevenPhases ν)))))))

/-- The procedures of Strassen's algorithm stand in the program at their numbers. -/
structure StrProg (P : Program) (ν : StrNums) : Prop where
  vlin : P[ν.pVlin]? = some vlinBody
  cconv : P[ν.pCconv]? = some cconvBody
  fill : P[ν.pFill]? = some fillBody
  phase : P[ν.pPhase]? = some (phaseBody ν)
  str : P[ν.pStr]? = some (strBody ν)

/-! ## The specification -/

/-- The scratch space of strassen at level j. -/
def strScr (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 3 * (4 ^ j * p) + strScr p j

/-- The steps of strassen at level j.  At level j + 1, with q = 4^j p: seven phases, each with a
recursive call and 92 q further steps, and the clearing of 4 q cells in 13 steps each, so that
696 = 7 · 92 + 4 · 13; the 900 covers the steps that do not depend on q. -/
def strSteps (p : ℕ) : ℕ → ℕ
  | 0 => 32 * p * p + 21 * p + 16
  | j + 1 => 7 * strSteps p j + 696 * (4 ^ j * p) + 900

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The arguments of strassen other than the level, with the data behind them: the operands `A` and
`B` have `len` numbers each, bounded by `α` and `β`, and the table of sizes reaches level `J`. -/
structure StrArgs : Type where
  (dst a b szt p scr : ℕ)
  (len J : ℕ)
  (A B : List ℤ)
  (α β : ℤ)

/-- The values of the arguments of strassen at level j. -/
abbrev StrArgs.vals (x : StrArgs) (j : ℕ) : List ℤ := [x.dst, x.a, x.b, j, x.szt, x.p, x.scr]

/-- What strassen assumes at level j.  The operands have len = 4^j p numbers each.  They and the
table of sizes lie below dst, and dst lies below the scratch space. -/
structure StrPre (lim : Limits) (μ : ℕ → ℤ) (j : ℕ) (x : StrArgs) : Prop where
  size : x.len = 4 ^ j * x.p
  prime : 1 ≤ x.p
  opA : ArrayAt μ x.a x.A x.len x.α x.dst
  opB : ArrayAt μ x.b x.B x.len x.β x.dst
  table : ListAt μ x.szt (szList x.p x.J) (x.J + 1) x.dst
  oneA : 1 ≤ x.α := by first
                          | omega
                          | ( (try have := Light.Std.space_le (by assumption))
                              (try have := Light.Std.const_le (by assumption))
                              simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  oneB : 1 ≤ x.β := by first
                          | omega
                          | ( (try have := Light.Std.space_le (by assumption))
                              (try have := Light.Std.const_le (by assumption))
                              simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  word : 4 * strassenBound x.p j x.α x.β ≤ lim.word := by first
                                                              | omega
                                                              | ( (try have := Light.Std.space_le (by assumption))
                                                                  (try have := Light.Std.const_le (by assumption))
                                                                  simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  level : j ≤ x.J := by first
                          | omega
                          | ( (try have := Light.Std.space_le (by assumption))
                              (try have := Light.Std.const_le (by assumption))
                              simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  dstBelow : x.dst + x.len ≤ x.scr := by first
                                           | omega
                                           | ( (try have := Light.Std.space_le (by assumption))
                                               (try have := Light.Std.const_le (by assumption))
                                               simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  space : x.scr + strScr x.p j ≤ lim.space := by first
                                                   | omega
                                                   | ( (try have := Light.Std.space_le (by assumption))
                                                       (try have := Light.Std.const_le (by assumption))
                                                       simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  room : 8 * x.len < lim.space := by first
                                     | omega
                                     | ( (try have := Light.Std.space_le (by assumption))
                                         (try have := Light.Std.const_le (by assumption))
                                         simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)






/-- What strassen does at level j, in the program P: it writes the product to dst and changes
nothing else but the scratch space. -/
def StrSpec (lim : Limits) (P : Program) (ν : StrNums) (j : ℕ) : Prop :=
  ∀ (x : StrArgs) (μ : ℕ → ℤ), StrPre lim μ j x → ∀ d, d + 2 * j + 1 ≤ lim.depth →
    Meets lim P ν.pStr d (x.vals j) μ (strSteps x.p j) fun _ μ' =>
      Seg μ' x.dst (strassenList x.p j x.A x.B) ∧ SameOutside2 μ μ' x.dst x.len x.scr (strScr x.p j)

/-! ## A phase -/

/-- The arguments of phase other than the level, with the data behind them: the six lists that stand
at the six addresses, the bounds `α` and `β` on the operands, and the level `J` that the table of
sizes reaches. -/
structure PhaseArgs : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)
  (szt p scr q J : ℕ)
  (A1 A2 B1 B2 C1 C2 : List ℤ)
  (α β : ℤ)

namespace PhaseArgs

variable (x : PhaseArgs) (j : ℕ)

/-- The values of the arguments of phase at level j. -/
abbrev vals : List ℤ :=
  [x.a1, x.a2, x.sA, x.b1, x.b2, x.sB, x.c1, x.s1, x.c2, x.s2, j, x.szt, x.p, x.scr, x.q]

/-- The first operand of the product of the phase, S = A1 + sA A2. -/
abbrev S : List ℤ := vlinList x.sA x.A1 x.A2

/-- The second operand of the product of the phase, T = B1 + sB B2. -/
abbrev T : List ℤ := vlinList x.sB x.B1 x.B2

/-- The product of the phase, M = S · T. -/
abbrev prod : List ℤ := phaseM x.p j x.sA x.A1 x.A2 x.sB x.B1 x.B2

/-- The arguments of the recursive call: S stands at scr, T at scr + q, the product goes to
scr + 2 q, and the scratch space begins at scr + 3 q. -/
@[simp] def inner : StrArgs :=
  { dst := x.scr + x.q + x.q, a := x.scr, b := x.scr + x.q, szt := x.szt, p := x.p
    scr := x.scr + x.q + x.q + x.q, len := x.q, J := x.J, A := x.S, B := x.T
    α := 2 * x.α, β := 2 * x.β }

end PhaseArgs

/-- What a phase assumes at level j + 1.  The six lists have q = 4^j p numbers each.  All of them
and the table of sizes lie below the scratch space, and the two results do not meet. -/
structure PhasePre (lim : Limits) (μ : ℕ → ℤ) (j : ℕ) (x : PhaseArgs) : Prop where
  size : x.q = 4 ^ j * x.p
  prime : 1 ≤ x.p
  opA1 : ArrayAt μ x.a1 x.A1 x.q x.α x.scr
  opA2 : ArrayAt μ x.a2 x.A2 x.q x.α x.scr
  opB1 : ArrayAt μ x.b1 x.B1 x.q x.β x.scr
  opB2 : ArrayAt μ x.b2 x.B2 x.q x.β x.scr
  out1 : ArrayAt μ x.c1 x.C1 x.q (2 * strassenBound x.p (j + 1) x.α x.β) x.scr
  out2 : ArrayAt μ x.c2 x.C2 x.q (2 * strassenBound x.p (j + 1) x.α x.β) x.scr
  table : ListAt μ x.szt (szList x.p x.J) (x.J + 1) x.scr
  signA : |x.sA| ≤ 1
  signB : |x.sB| ≤ 1
  sign1 : |x.s1| ≤ 1
  sign2 : |x.s2| ≤ 1
  oneA : 1 ≤ x.α
  oneB : 1 ≤ x.β
  word : 4 * strassenBound x.p (j + 1) x.α x.β ≤ lim.word
  space : x.scr + strScr x.p (j + 1) ≤ lim.space
  apart : Apart x.c1 x.q x.c2 x.q := by first
                                        | omega
                                        | ( (try have := Light.Std.space_le (by assumption))
                                            (try have := Light.Std.const_le (by assumption))
                                            simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  level : j ≤ x.J := by first
                          | omega
                          | ( (try have := Light.Std.space_le (by assumption))
                              (try have := Light.Std.const_le (by assumption))
                              simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  room : 8 * x.q < lim.space := by first
                                   | omega
                                   | ( (try have := Light.Std.space_le (by assumption))
                                       (try have := Light.Std.const_le (by assumption))
                                       simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

/-- What a phase promises: s1 M has been added to the list at c1 and s2 M to the list at c2, and
nothing else has changed but the scratch space. -/
structure PhasePost (μ : ℕ → ℤ) (j : ℕ) (x : PhaseArgs) (μ' : ℕ → ℤ) : Prop where
  out1 : Seg μ' x.c1 (vlinList x.s1 x.C1 (x.prod j))
  out2 : Seg μ' x.c2 (vlinList x.s2 x.C2 (x.prod j))
  same : SameOutside3 μ μ' x.c1 x.q x.c2 x.q x.scr (strScr x.p (j + 1))

section phase

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j : ℕ} {x : PhaseArgs}

namespace PhasePre














































end PhasePre

variable (prog : StrProg P ν) (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw
































































end phase

/-! ## Between two phases -/

/-- A row of the table of Strassen's seven products.  With a[t], b[t] and c[t] for the quarters
number t of the operands and of the result, the product is
M = (a[a1] + sA a[a2]) · (b[b1] + sB b[b2]), and s1 M is added to c[c1] and s2 M to c[c2]. -/
structure PhaseRow : Type where
  (a1 a2 : ℕ) (sA : ℤ) (b1 b2 : ℕ) (sB : ℤ) (c1 : ℕ) (s1 : ℤ) (c2 : ℕ) (s2 : ℤ)

/-- The entries of a row are numbers of quarters and signs, and the two results are different
quarters. -/
structure PhaseRow.Ok (row : PhaseRow) : Prop where
  a1 : row.a1 < 4
  a2 : row.a2 < 4
  b1 : row.b1 < 4
  b2 : row.b2 < 4
  c1 : row.c1 < 4
  c2 : row.c2 < 4
  ne : row.c1 ≠ row.c2
  sA : |row.sA| ≤ 1
  sB : |row.sB| ≤ 1
  s1 : |row.s1| ≤ 1
  s2 : |row.s2| ≤ 1

/-- The arguments of the phase of a row, called from strassen with the arguments x, when a
quarter has q numbers and the four quarters of dst hold the lists L 0, …, L 3. -/
@[simp] def StrArgs.phase (x : StrArgs) (q : ℕ) (L : ℕ → List ℤ) (row : PhaseRow) : PhaseArgs :=
  { a1 := x.a + row.a1 * q, a2 := x.a + row.a2 * q, sA := row.sA
    b1 := x.b + row.b1 * q, b2 := x.b + row.b2 * q, sB := row.sB
    c1 := x.dst + row.c1 * q, s1 := row.s1, c2 := x.dst + row.c2 * q, s2 := row.s2
    szt := x.szt, p := x.p, scr := x.scr, q := q, J := x.J
    A1 := quarter q row.a1 x.A, A2 := quarter q row.a2 x.A
    B1 := quarter q row.b1 x.B, B2 := quarter q row.b2 x.B
    C1 := L row.c1, C2 := L row.c2, α := x.α, β := x.β }

/-- The four lists after the phase of a row. -/
def StrArgs.after (x : StrArgs) (j q : ℕ) (L : ℕ → List ℤ) (row : PhaseRow) : ℕ → List ℤ :=
  Function.update (Function.update L row.c1 (vlinList row.s1 (L row.c1) ((x.phase q L row).prod j)))
    row.c2 (vlinList row.s2 (L row.c2) ((x.phase q L row).prod j))

/-- The state of strassen at level j + 1 after κ phases: what strassen assumes still holds, and the
four quarters of dst hold the lists L 0, …, L 3, of q = 4^j p numbers each, bounded by κ times the
bound on a product. -/
structure StrInv (lim : Limits) (μ : ℕ → ℤ) (j q : ℕ) (x : StrArgs) (L : ℕ → List ℤ) (κ : ℕ) : Prop
    extends StrPre lim μ (j + 1) x where
  quarterLen : q = 4 ^ j * x.p
  out : ∀ t < 4, ArrayAt μ (x.dst + t * q) (L t) q (κ * strassenBound x.p j (2 * x.α) (2 * x.β))
    x.scr





















section step

variable {ν : StrNums} {μ μ' : ℕ → ℤ} {j q κ : ℕ} {x : StrArgs} {L : ℕ → List ℤ} {row : PhaseRow}

namespace StrInv




























































end StrInv

















end step

























/-! ## The seven phases -/

section levels

variable {ν : StrNums} {μ : ℕ → ℤ} {j q : ℕ} {x : StrArgs} (prog : StrProg P ν)
  (hw : (lim.space : ℤ) ≤ lim.word)
include prog hw



















































/-! ## The two cases and the induction -/

























































end levels

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_ZOrder


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Matrices over ℤ[x]/(x^p - 1) in Z-order: the table of places, and P and Q of Theorem 17's proof

spreadTable(dst, N2) writes the table of `spread`: the number with the binary digits of i, read in
base 4.  There is no division: a pointer j = ⌊i/2⌋ and the parity of i are carried along, and
dst[i] = 4 dst[j] + parity (`spreadStep_spec`, `spreadTable_spec`).

buildZ(dst, r, mort, n, N2, p, mx, my), with N2 = 2^K, writes an N2 × N2 matrix of vectors of length
p in Z-order, 4^K p cells in all, whose entry for the pair (x, y), x, y < n, is the unit vector with
its 1 at place r[x n + y], and whose other entries are zero vectors.  Here mort is the address of
the table that spreadTable has written, so that mort[x] = spread x.  The place of the pair (x, y) is
mx · spread x + my · spread y.  With (mx, my) = (2, 1) the pair is (row, column), which gives
"P[a,c] := x^{w(a,c) mod p}"; with (1, 2) it is (column, row), which gives
"Q[c,b] := x^{w(b,c) mod p}" from the residues of w(b,c) stored at b n + c.  (Inside the two quoted
formulas x is the paper's indeterminate, and P and Q are the paper's matrices; in the code `P` is
the program.)  The routine clears the matrix (`buildZClear_spec`) and marks one cell for each pair
(`buildZMark_spec`); `markList_eq_zList` identifies the marked list with the matrix.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The table of places -/

namespace SpreadTable

/-- The local variables of spreadTable.  The arguments: Dst = dst, Rows = N2.  Then Idx = i;
Half = j = ⌊i/2⌋; Parity, the parity of i. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Rows : ℕ := 1
@[inherit_doc Dst] abbrev Idx : ℕ := 2
@[inherit_doc Dst] abbrev Half : ℕ := 3
@[inherit_doc Dst] abbrev Parity : ℕ := 4

end SpreadTable

open SpreadTable in
/-- dst[i] := 4 dst[j] + parity; then i, j and the parity go on to i + 1. -/
def spreadStep : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Idx))
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.mul) (k 4) (M ((Light.Expr.op Light.Op.add) (v Dst) (v Half)))) (v Parity)))
    (Light.Stmt.seq
      (.ite (Light.Cond.eq (v Parity) (k 0)) (.set Parity (k 1))
        (Light.Stmt.seq (.set Parity (k 0)) (.set Half ((Light.Expr.op Light.Op.add) (v Half) (k 1)))))
      (.set Idx ((Light.Expr.op Light.Op.add) (v Idx) (k 1)))))

open SpreadTable in
/-- spreadTable(dst, N2). -/
def spreadTableBody : Stmt :=
  .ite ((Light.Cond.lt (k 0) (v Rows))) (
    (Light.Stmt.seq (.store (v Dst) (k 0))
      (Light.Stmt.seq (.set Idx (k 1))
        (Light.Stmt.seq (.set Half (k 0))
          (Light.Stmt.seq (.set Parity (k 1)) (.while (Light.Cond.lt (v Idx) (v Rows)) spreadStep))))))
    .skip

section spreadTable

variable {μ μ' : ℕ → ℤ} {dst N₂ : ℕ}







































































end spreadTable









/-! ## The matrices -/

namespace BuildZ

/-- The local variables of buildZ.  The arguments: Dst = dst, Residues = r, Places = mort, Num = n,
Rows = N2, Prime = p, MulX = mx, MulY = my.  Then Ptr, the first cell that is still to be cleared;
Stop, the end of the matrix; Square = n²; Idx = t = x n + y, the number of the pair; Row = x;
Col = y. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Residues : ℕ := 1
@[inherit_doc Dst] abbrev Places : ℕ := 2
@[inherit_doc Dst] abbrev Num : ℕ := 3
@[inherit_doc Dst] abbrev Rows : ℕ := 4
@[inherit_doc Dst] abbrev Prime : ℕ := 5
@[inherit_doc Dst] abbrev MulX : ℕ := 6
@[inherit_doc Dst] abbrev MulY : ℕ := 7
@[inherit_doc Dst] abbrev Ptr : ℕ := 8
@[inherit_doc Dst] abbrev Stop : ℕ := 9
@[inherit_doc Dst] abbrev Square : ℕ := 10
@[inherit_doc Dst] abbrev Idx : ℕ := 11
@[inherit_doc Dst] abbrev Row : ℕ := 12
@[inherit_doc Dst] abbrev Col : ℕ := 13

end BuildZ

open BuildZ in
/-- The N2 N2 p cells of the matrix are cleared. -/
def buildZClear : Stmt :=
  (Light.Stmt.seq (.set Ptr (v Dst))
    (Light.Stmt.seq
      (.set Stop
        ((Light.Expr.op Light.Op.add) (v Dst)
          ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (v Rows) (v Rows)) (v Prime))))
      (.while (Light.Cond.lt (v Ptr) (v Stop))
        (Light.Stmt.seq (.store (v Ptr) (k 0)) (.set Ptr ((Light.Expr.op Light.Op.add) (v Ptr) (k 1)))))))

open BuildZ in
/-- The pair (x, y) marks its cell: dst[(mx mort[x] + my mort[y]) p + r[t]] := 1. -/
def buildZMark : Stmt :=
  .store
    (((Light.Expr.op Light.Op.add)
       ((Light.Expr.op Light.Op.add) (v Dst)
         ((Light.Expr.op Light.Op.mul)
           ((Light.Expr.op Light.Op.add)
             ((Light.Expr.op Light.Op.mul) (v MulX) (M ((Light.Expr.op Light.Op.add) (v Places) (v Row))))
             ((Light.Expr.op Light.Op.mul) (v MulY) (M ((Light.Expr.op Light.Op.add) (v Places) (v Col)))))
           (v Prime)))
       (M ((Light.Expr.op Light.Op.add) (v Residues) (v Idx)))))
    (k 1)

open BuildZ in
/-- buildZ(dst, r, mort, n, N2, p, mx, my). -/
def buildZBody : Stmt :=
  (Light.Stmt.seq buildZClear
    (Light.Stmt.seq (.set Square ((Light.Expr.op Light.Op.mul) (v Num) (v Num)))
      (Light.Stmt.seq (.set Row (k 0))
        (Light.Stmt.seq (.set Col (k 0)) (.for Idx (v Square) (Light.Stmt.seq buildZMark (nextPair Row Col Num)))))))

/-- An upper bound on the number of steps of buildZ. -/
def buildZTime (n N2 p : ℕ) : ℕ := 11 * (N2 * N2 * p) + 50 * (n * n) + 40

/-- What buildZ needs: where the arrays lie, and what they hold.  The matrix has N2 = 2^K rows and
columns, so 4^K entries of p cells each, and R is the list of the n² residues that stand at r. -/
structure BuildZPre (lim : Limits) (μ : ℕ → ℤ) (dst r mort n K p : ℕ) (R : List ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  res : IndexAt μ r R (n * n) p lim.space
  table : ListAt μ mort (spreadList (2 ^ K)) (2 ^ K) lim.space
  n_le : n ≤ 2 ^ K
  p_pos : 0 < p
  dst_le : dst + 4 ^ K * p < lim.space
  apartR : Apart dst (4 ^ K * p) r (n * n)
  apartM : Apart dst (4 ^ K * p) mort (2 ^ K)

/-! ### The pure side: a list of zeros in which places are marked one after the other -/

/-- The list of `len` zeros in which the places `idx 0, …, idx (t - 1)` have been set to 1. -/
def markList (len : ℕ) (idx : ℕ → ℕ) : ℕ → List ℤ
  | 0 => List.replicate len 0
  | t + 1 => (markList len idx t).set (idx t) 1










































































































/-! ### The program -/

section buildZ

variable {μ μ' : ℕ → ℤ} {dst r mort n K p mx my : ℕ} {R : List ℕ}

namespace BuildZPre













end BuildZPre











































































































































end buildZ















/-! ## The matrices P and Q as lists -/


































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Parameters_Residues


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Residues without division

"We reduce the weights modulo a prime p" (proof of Theorem 17).  The language has no division.  The
residue of a number w modulo p is found by greedy subtraction of 2^len p, …, 2p, p, which are kept
in a table.

* bitLen(U) returns the number of binary digits of U, by doubling (`bitLen_spec`).
* dblTable(dst, p, len) writes p, 2p, …, 2^len p to dst (`dblTable_spec`).
* resid(w, dbl, len) returns w mod p, for |w| < 2^len, given the table at dbl (`resid_meets`).  What
  the routine holds after i rounds is `greedyAt p len w i`: it is not negative, below 2^(len+1-i) p,
  and congruent to w (`greedyAt_inv`), so that it ends with the residue (`greedyAt_end`).
* residues(src, dst, m, dbl, len) writes the residues of the m numbers at src to dst, by one call of
  resid for each (`residues_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The number of binary digits -/

namespace BitLen

/-- The local variables of bitLen: the argument U, the number of doublings, and the power of two. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Len : ℕ := 1
@[inherit_doc Arg] abbrev Pow : ℕ := 2

end BitLen

open BitLen in
/-- bitLen(U). -/
def bitLenBody : Stmt :=
  (Light.Stmt.seq (.set Len (k 0))
    (Light.Stmt.seq (.set Pow (k 1))
      (Light.Stmt.seq
        (.while (Light.Cond.le (v Pow) (v Arg))
          (Light.Stmt.seq (.set Pow ((Light.Expr.op Light.Op.add) (v Pow) (v Pow)))
            (.set Len ((Light.Expr.op Light.Op.add) (v Len) (k 1)))))
        (.set Arg (v Len)))))

/-- The time of bitLen. -/
def tBitLen (U : ℕ) : ℕ := 14 * bitLen U + 12































/-! ## The table of the doubles -/















namespace DblTable

/-- The local variables of dblTable: the arguments dst, p, len; the exponent; the entry. -/
abbrev Dst : ℕ := 0
@[inherit_doc Dst] abbrev Prime : ℕ := 1
@[inherit_doc Dst] abbrev Len : ℕ := 2
@[inherit_doc Dst] abbrev Exp : ℕ := 3
@[inherit_doc Dst] abbrev Entry : ℕ := 4

end DblTable

open DblTable in
/-- dblTable(dst, p, len). -/
def dblTableBody : Stmt :=
  (Light.Stmt.seq (.set Exp (k 0))
    (Light.Stmt.seq (.set Entry (v Prime))
      (Light.Stmt.seq (.store (v Dst) (v Entry))
        (.while (Light.Cond.lt (v Exp) (v Len))
          (Light.Stmt.seq (.set Entry ((Light.Expr.op Light.Op.add) (v Entry) (v Entry)))
            (Light.Stmt.seq (.set Exp ((Light.Expr.op Light.Op.add) (v Exp) (k 1)))
              (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Exp)) (v Entry))))))))

/-- The time of dblTable. -/
def tDblTable (len : ℕ) : ℕ := 17 * len + 11

/-- The state of dblTable before round j: the entries p, …, 2^j p are written, the last of them is
in a local, and no cell outside the table has changed. -/
def DblInv (μ : ℕ → ℤ) (dst p len j : ℕ) (σ : State) : Prop :=
  ∃ μ', σ = ⟨frame [dst, p, len, j, (p * 2 ^ j : ℕ)], μ'⟩ ∧ Seg μ' dst (dblList p j) ∧
    SameOutside μ μ' dst (len + 1)







































/-! ## One residue -/

/-- The number that resid holds after i rounds: it starts from w + 2^len p, and round number i
subtracts 2^(len-i) p if that leaves a number that is not negative. -/
def greedyAt (p len : ℕ) (w : ℤ) : ℕ → ℤ
  | 0 => w + ((p * 2 ^ len : ℕ) : ℤ)
  | i + 1 =>
    if ((p * 2 ^ (len - i) : ℕ) : ℤ) ≤ greedyAt p len w i then
      greedyAt p len w i - ((p * 2 ^ (len - i) : ℕ) : ℤ)
    else greedyAt p len w i




















































namespace Resid

/-- The local variables of resid: the arguments w, dbl, len; one more than the next exponent; the
number that is reduced. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Dbl : ℕ := 1
@[inherit_doc Arg] abbrev Len : ℕ := 2
@[inherit_doc Arg] abbrev Exp : ℕ := 3
@[inherit_doc Arg] abbrev Num : ℕ := 4

end Resid

open Resid in
/-- resid(w, dbl, len). -/
def residBody : Stmt :=
  (Light.Stmt.seq (.set Num ((Light.Expr.op Light.Op.add) (v Arg) (M ((Light.Expr.op Light.Op.add) (v Dbl) (v Len)))))
    (Light.Stmt.seq (.set Exp ((Light.Expr.op Light.Op.add) (v Len) (k 1)))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (k 0) (v Exp))
          (Light.Stmt.seq (.set Exp ((Light.Expr.op Light.Op.sub) (v Exp) (k 1)))
            (.ite (Light.Cond.le (M ((Light.Expr.op Light.Op.add) (v Dbl) (v Exp))) (v Num))
              (.set Num ((Light.Expr.op Light.Op.sub) (v Num) (M ((Light.Expr.op Light.Op.add) (v Dbl) (v Exp)))))
              .skip)))
        (.set Arg (v Num)))))

/-- The time of resid. -/
def tResid (len : ℕ) : ℕ := 24 * len + 41












































/-! ## The residues of a list -/

namespace Residues

/-- The local variables of residues: the arguments src, dst, m, dbl, len; the counter; the
residue. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Num : ℕ := 2
@[inherit_doc Src] abbrev Dbl : ℕ := 3
@[inherit_doc Src] abbrev Len : ℕ := 4
@[inherit_doc Src] abbrev Idx : ℕ := 5
@[inherit_doc Src] abbrev Res : ℕ := 6

end Residues

open Residues in
/-- residues(src, dst, m, dbl, len).  The parameter pResid is the number of the procedure resid in
the program. -/
def residuesBody (pResid : ℕ) : Stmt :=
  .for Idx (v Num) (
    (Light.Stmt.seq (.call pResid [M ((Light.Expr.op Light.Op.add) (v Src) (v Idx)), v Dbl, v Len] Res)
      (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Idx)) (v Res))))

/-- The time of residues. -/
def tResidues (m len : ℕ) : ℕ := m * (tResid len + 21) + 6

/-- What residues assumes: the table of the doubles of p stands at dbl, and the list l of m numbers
of absolute value at most U < 2^len at src; the m cells at dst lie in the memory and meet
neither. -/
structure ResiduesPre (lim : Limits) (μ : ℕ → ℤ) (src dst m dbl p len U : ℕ) (l : List ℤ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  prime : 1 ≤ p
  segDbl : Seg μ dbl (dblList p len)
  segSrc : Seg μ src l
  length : l.length = m
  le : AbsLe l U
  lt : U < 2 ^ len
  spaceDbl : dbl + (len + 1) ≤ lim.space
  spaceSrc : src + m ≤ lim.space
  spaceDst : dst + m ≤ lim.space
  count : m < lim.space
  apartSrc : Apart dst m src m
  apartDbl : Apart dst m dbl (len + 1)
  word : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word

/-- The state of residues before round i: the first i residues are written, and no cell outside dst
has changed. -/
def ResiduesInv (μ : ℕ → ℤ) (src dst m dbl p len : ℕ) (l : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [src, dst, m, dbl, len, i, r], μ'⟩ ∧
    SegN μ' dst (residList p (l.take i)) ∧ SameOutside μ μ' dst m














































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_CountPrime


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The count for one prime (proof of Theorem 17, "Hashing modulo a prime")

"For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod p)", where S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) is the weight of the triangle.  "Let P[a,c] := x^{w(a,c) mod p} and Q[c,b]
:= x^{w(b,c) mod p} be matrices over the ring ℤ[x]/(x^p - 1) […]; then F(p) + Z₀ is the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]."  Here F(p) is the number
of triples with S(a,b,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ the number of triples with S(a,b,c) = 0.

countPrime(n, ab, bc, ac, p, len, K, N2, w) computes this count for one prime, in a work area at w.
Two letters of the quotation mean something else in the code.  There w is the address of the work
area, and the weights are the three lists ab, bc and ac.  And `P` is the program, while the matrices
P and Q occur only as the lists `matPList` and `matQList`.

The routine has three parts.

* The addresses of the parts of the work area (`cpAddr_spec`); they lie one behind the other
  (`cp_places`).
* Six tables: the doubles of p, the residues of the three lists of weights, the places of the
  Z-order, and the sizes 4^i p of the matrices of Strassen's recursion, which szTable(dst, p, J)
  writes (`szTable_spec`, `cpTables_spec`, `CpTabs`).
* The matrices P and Q in Z-order, their product by Strassen's algorithm, and the sum of the
  coefficients (`cpProduct_spec`).

`countPrime_spec` puts the three parts together.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The numbers of the procedures that countPrime calls. -/
structure CpNums : Type where
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pSpread : ℕ
  pSz : ℕ
  pBuild : ℕ
  pCount : ℕ
  str : StrNums

/-- The program holds the procedures that countPrime calls. -/
structure CpCtx (P : Program) (ν : CpNums) : Prop where
  hDbl : P[ν.pDbl]? = some dblTableBody
  hResid : P[ν.pResid]? = some residBody
  hResidues : P[ν.pResidues]? = some (residuesBody ν.pResid)
  hSpread : P[ν.pSpread]? = some spreadTableBody
  hSz : P[ν.pSz]? = some szTableBody
  hBuild : P[ν.pBuild]? = some buildZBody
  hCount : P[ν.pCount]? = some countZeroBody
  str : StrProg P ν.str

namespace CountPrime

/-- The local variables of countPrime.  The arguments n, ab, bc, ac, p, len, K, N2, w: N2 = 2^K is
the number of rows and columns of the padded matrices, and w, the address of the work area, is also
the address of the table of doubles.  Then n²; the addresses of the residues of the lists ab, bc and
ac, of the table of places and of the table of sizes; the size 4^K p of a matrix; the addresses
of P, Q, PQ and of the scratch space of Strassen's algorithm; a local that takes the results of the
calls, except the last one, whose result (the count) goes to local 0 and is returned. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev ListAB : ℕ := 1
@[inherit_doc Num] abbrev ListBC : ℕ := 2
@[inherit_doc Num] abbrev ListAC : ℕ := 3
@[inherit_doc Num] abbrev Prime : ℕ := 4
@[inherit_doc Num] abbrev Len : ℕ := 5
@[inherit_doc Num] abbrev Level : ℕ := 6
@[inherit_doc Num] abbrev Rows : ℕ := 7
@[inherit_doc Num] abbrev Work : ℕ := 8
@[inherit_doc Num] abbrev Square : ℕ := 9
@[inherit_doc Num] abbrev ResAB : ℕ := 10
@[inherit_doc Num] abbrev ResBC : ℕ := 11
@[inherit_doc Num] abbrev ResAC : ℕ := 12
@[inherit_doc Num] abbrev Places : ℕ := 13
@[inherit_doc Num] abbrev Sizes : ℕ := 14
@[inherit_doc Num] abbrev Size : ℕ := 15
@[inherit_doc Num] abbrev MatP : ℕ := 16
@[inherit_doc Num] abbrev MatQ : ℕ := 17
@[inherit_doc Num] abbrev MatR : ℕ := 18
@[inherit_doc Num] abbrev Scr : ℕ := 19
@[inherit_doc Num] abbrev Res : ℕ := 20

end CountPrime

open CountPrime in
/-- The first part of countPrime: the addresses of the parts of the work area. -/
def cpAddr : Stmt :=
  (Light.Stmt.seq (.set Square ((Light.Expr.op Light.Op.mul) (v Num) (v Num)))
    (Light.Stmt.seq (.set ResAB ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Work) (v Len)) (k 1)))
      (Light.Stmt.seq (.set ResBC ((Light.Expr.op Light.Op.add) (v ResAB) (v Square)))
        (Light.Stmt.seq (.set ResAC ((Light.Expr.op Light.Op.add) (v ResBC) (v Square)))
          (Light.Stmt.seq (.set Places ((Light.Expr.op Light.Op.add) (v ResAC) (v Square)))
            (Light.Stmt.seq (.set Sizes ((Light.Expr.op Light.Op.add) (v Places) (v Rows)))
              (Light.Stmt.seq
                (.set Size ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.mul) (v Rows) (v Rows)) (v Prime)))
                (Light.Stmt.seq
                  (.set MatP ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Sizes) (v Level)) (k 1)))
                  (Light.Stmt.seq (.set MatQ ((Light.Expr.op Light.Op.add) (v MatP) (v Size)))
                    (Light.Stmt.seq (.set MatR ((Light.Expr.op Light.Op.add) (v MatQ) (v Size)))
                      (.set Scr ((Light.Expr.op Light.Op.add) (v MatR) (v Size)))))))))))))

open CountPrime in
/-- The second part: the table of doubles, the residues of the three lists, the table of places, the
table of sizes. -/
def cpTables (ν : CpNums) : Stmt :=
  (Light.Stmt.seq (.call ν.pDbl [v Work, v Prime, v Len] Res)
    (Light.Stmt.seq (.call ν.pResidues [v ListAB, v ResAB, v Square, v Work, v Len] Res)
      (Light.Stmt.seq (.call ν.pResidues [v ListBC, v ResBC, v Square, v Work, v Len] Res)
        (Light.Stmt.seq (.call ν.pResidues [v ListAC, v ResAC, v Square, v Work, v Len] Res)
          (Light.Stmt.seq (.call ν.pSpread [v Places, v Rows] Res) (.call ν.pSz [v Sizes, v Prime, v Level] Res))))))

open CountPrime in
/-- The third part: the matrices P and Q, their product, the count. -/
def cpProduct (ν : CpNums) : Stmt :=
  (Light.Stmt.seq (.call ν.pBuild [v MatP, v ResAC, v Places, v Num, v Rows, v Prime, k 2, k 1] Res)
    (Light.Stmt.seq (.call ν.pBuild [v MatQ, v ResBC, v Places, v Num, v Rows, v Prime, k 1, k 2] Res)
      (Light.Stmt.seq (.call ν.str.pStr [v MatR, v MatP, v MatQ, v Level, v Sizes, v Prime, v Scr] Res)
        (.call ν.pCount [v MatR, v ResAB, v Places, v Num, v Prime] Num))))

/-- countPrime(n, ab, bc, ac, p, len, K, N2, w). -/
def countPrimeBody (ν : CpNums) : Stmt := (Light.Stmt.seq cpAddr (Light.Stmt.seq (cpTables ν) (cpProduct ν)))

/-- The number of cells of the work area of countPrime.  (The last summand is not written; it is
room that Strassen's algorithm asks for.) -/
def countCells (n p len K : ℕ) : ℕ :=
  (len + 1) + 3 * (n * n) + 2 ^ K + (K + 1) + 3 * (4 ^ K * p) + strScr p K + (8 * (4 ^ K * p) + 1)

/-- An upper bound on the number of steps of countPrime. -/
def countTime (n p len K : ℕ) : ℕ :=
  tDblTable len + 3 * tResidues (n * n) len + (30 * 2 ^ K + 17) + tSzTable K +
    2 * buildZTime n (2 ^ K) p + strSteps p K + countZeroTime n + 150

/-! ## The layout of the work area -/

/-- The address of the residues of the list ab. -/
def cpRab (w len : ℕ) : ℕ := w + (len + 1)

/-- The address of the residues of the list bc. -/
def cpRbc (w len n : ℕ) : ℕ := cpRab w len + n * n

/-- The address of the residues of the list ac. -/
def cpRac (w len n : ℕ) : ℕ := cpRbc w len n + n * n

/-- The address of the table of places. -/
def cpMort (w len n : ℕ) : ℕ := cpRac w len n + n * n

/-- The address of the table of sizes. -/
def cpSzt (w len n K : ℕ) : ℕ := cpMort w len n + 2 ^ K

/-- The address of the matrix P. -/
def cpPm (w len n K : ℕ) : ℕ := cpSzt w len n K + (K + 1)

/-- The address of the matrix Q. -/
def cpQm (w len n K p : ℕ) : ℕ := cpPm w len n K + 4 ^ K * p

/-- The address of the product. -/
def cpRm (w len n K p : ℕ) : ℕ := cpQm w len n K p + 4 ^ K * p

/-- The address of the scratch space of Strassen's algorithm. -/
def cpScr (w len n K p : ℕ) : ℕ := cpRm w len n K p + 4 ^ K * p














/-- The local variables of countPrime after its first part. -/
@[simp] def cpFrame (n ab bc ac p len K w : ℕ) : List ℤ :=
  [n, ab, bc, ac, p, len, K, (2 ^ K : ℕ), w, (n * n : ℕ), cpRab w len, cpRbc w len n,
    cpRac w len n, cpMort w len n, cpSzt w len n K, (4 ^ K * p : ℕ), cpPm w len n K,
    cpQm w len n K p, cpRm w len n K p, cpScr w len n K p]























/-! ## What countPrime assumes -/

/-- What countPrime needs: the three lists of n² weights of absolute value at most U < 2^len lie
below the work area, the work area lies in the memory, and the numbers that are formed fit in a
word. -/
structure CountPrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) :
    Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  p_pos : 1 ≤ p
  hK : K = Nat.clog 2 x.n
  hU : x.U < 2 ^ len
  cells : w + countCells x.n p len K ≤ lim.space
  wordDbl : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * K + 2 ≤ lim.depth











section Premise

variable {μ : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}


























end Premise

/-! ## The procedures that countPrime calls -/

section meets

variable {μ : ℕ → ℤ}

















end meets

/-! ## The tables -/

/-- The tables of countPrime are in their places. -/
structure CpTabs (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) : Prop where
  dbl : Seg μ w (dblList p len)
  rab : SegN μ (cpRab w len) (residList p x.AB)
  rbc : SegN μ (cpRbc w len x.n) (residList p x.BC)
  rac : SegN μ (cpRac w len x.n) (residList p x.AC)
  mort : Seg μ (cpMort w len x.n) (spreadList (2 ^ K))
  szt : Seg μ (cpSzt w len x.n K) (szList p K)

section parts

variable {ν : CpNums} {μ₀ μ μ' : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}





























































/-! ## The product and the count -/
































































































end parts

/-! ## Larger primes need more cells and more time -/

















end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Parameters_Primes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The primes of the window (proof of Theorem 17)

The hashing of the proof of Theorem 17 uses "a prime p ∈ [√D/2, √D)".  primes(dst, D) lists these
primes in increasing order and returns their number (`primes_spec`).

* It computes s = ⌊√D⌋ and calls the sieve of Eratosthenes, which writes all primes up to s to dst.
  The sieve gets the s + 1 cells behind these s cells for its table.
* One pass keeps the primes p with D ≤ 4p² and p² < D and moves them to the front (`pass_spec`, with
  the round `keep_spec`).  What it keeps is the list of the window (`filter_primesBelow`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- The number p lies in the window: √D/2 ≤ p < √D, by integer comparisons. -/
abbrev InWindow (D p : ℕ) : Prop := D ≤ 4 * (p * p) ∧ p * p < D

/-- The numbers of the list L that lie in the window. -/
abbrev inWindow (D : ℕ) (L : List ℕ) : List ℕ := L.filter fun p => InWindow D p




































/-! ## The program -/

namespace Primes

/-- The local variables of primes: the arguments dst and D; s = ⌊√D⌋; the number of primes up to s;
the number j of those that have been looked at; the prime p that is looked at and its square; the
number cnt of primes that have been kept. -/
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Size : ℕ := 1
@[inherit_doc Dest] abbrev Root : ℕ := 2
@[inherit_doc Dest] abbrev Total : ℕ := 3
@[inherit_doc Dest] abbrev Index : ℕ := 4
@[inherit_doc Dest] abbrev Prime : ℕ := 5
@[inherit_doc Dest] abbrev Square : ℕ := 6
@[inherit_doc Dest] abbrev Count : ℕ := 7

end Primes

open Primes

/-- The prime number j of the list is kept if it lies in the window. -/
def primesKeep : Stmt :=
  (Light.Stmt.seq (.set Prime (M ((Light.Expr.op Light.Op.add) (v Dest) (v Index))))
    (Light.Stmt.seq (.set Square ((Light.Expr.op Light.Op.mul) (v Prime) (v Prime)))
      (Light.Stmt.seq (.set Index ((Light.Expr.op Light.Op.add) (v Index) (k 1)))
        (.ite (Light.Cond.le (v Size) ((Light.Expr.op Light.Op.mul) (k 4) (v Square)))
          (.ite (Light.Cond.lt (v Square) (v Size))
            (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Count)) (v Prime))
              (.set Count ((Light.Expr.op Light.Op.add) (v Count) (k 1))))
            .skip)
          .skip))))

/-- The pass over the primes up to s; the result is the number of primes that are kept. -/
def primesPass : Stmt :=
  (Light.Stmt.seq (.set Count (k 0))
    (Light.Stmt.seq (.set Index (k 0))
      (Light.Stmt.seq (.while (Light.Cond.lt (v Index) (v Total)) primesKeep) (.set 0 (v Count)))))

/-- primes(dst, D), with the numbers of the procedure sqrt and of the sieve. -/
def primesBody (pSqrt pSieve : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pSqrt [v Size] Root)
    (Light.Stmt.seq (.call pSieve [v Root, v Dest, (Light.Expr.op Light.Op.add) (v Dest) (v Root)] Total) primesPass))

/-- The number of steps of primes(dst, D). -/
def tPrimes (D : ℕ) : ℕ := 80 * (Nat.sqrt D ^ 3 + 1)

namespace Primes

variable {μ : ℕ → ℤ} {dst D s : ℕ} {L : List ℕ}

/-- The first j primes of the list L have been looked at: those in the window stand at the front of
dst, the primes from number j on are still in their places, and no cell outside the list has
changed. -/
def Sifted (μ : ℕ → ℤ) (dst D s : ℕ) (L : List ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (p q : ℤ),
    σ = ⟨frame [dst, D, s, L.length, j, p, q, (inWindow D (L.take j)).length], μ'⟩ ∧
    SegN μ' dst (inWindow D (L.take j)) ∧ SegN μ' (dst + j) (L.drop j) ∧
    SameOutside μ μ' dst L.length






































































/-- What primes needs of the program: the procedures sqrt and the sieve of Eratosthenes. -/
structure Ctx (P : Program) (pSqrt pSieve : ℕ) : Prop where
  hSqrt : P[pSqrt]? = some sqrtBody
  hSieve : P[pSieve]? = some sieveBody
















end Primes


































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Theorem17_Choice


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The prime that is chosen (proof of Theorem 17)

`chosenPrime n D AB BC AC` is the first prime of the window `√D/2 ≤ p < √D` at which the count,
computed with Strassen's algorithm from the three lists of weights, is smallest.  Here
`triOf n AB BC AC` is the instance of Exact Triangle whose weights are read from the three lists:
`w(a,b)` at `a n + b` of `AB`, `w(b,c)` at `b n + c` of `BC`, `w(a,c)` at `a n + c` of `AC`.

* The computed count is the count of the proof of Theorem 17 at every prime of the window
  (`countOf_eq`), so the chosen prime is a selected prime in the sense of the proof of Theorem 17,
  "We select the prime with the smallest count" (`chosenPrime_isSelected`).  It lies between 2 and
  `⌊√D⌋` (`two_le_chosenPrime`, `chosenPrime_le_sqrt`).
* A program finds it in one pass over the primes: `bestOf f L i` is the best of the first `i`
  elements of a list (`bestOf_one`, `bestOf_succ`, `bestOf_length`).
* The paper bounds the weights by `n^ν`; a program has a bound `U`.  `kappaOf n U` is the least
  exponent `κ ≥ 1` with `U ≤ n^κ`, and with it the bound of the proof of Theorem 17 on the number
  `F(p)` of false positives, that is, of triples with `S(a,b,c) ≠ 0` and `p ∣ S(a,b,c)`, holds for
  the chosen prime (`F_chosenPrime_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The chosen prime -/

/-- "We select the prime with the smallest count" (the first such prime; 0 if the window has no
prime). -/
def chosenPrime (n D : ℕ) (AB BC AC : List ℤ) : ℕ :=
  ((primesList D).argmin fun p => (countOf n p AB BC AC).toNat).getD 0

section Chosen

variable {n D : ℕ} (AB BC AC : List ℤ)








































end Chosen

/-! ## The smallest count, by one pass -/

/-- The first of the first `i` elements of a list at which `f` is smallest; 0 for `i = 0`. -/
def bestOf (f : ℕ → ℕ) (L : List ℕ) (i : ℕ) : ℕ := ((L.take i).argmin f).getD 0

















/-! ## False positives, in terms of a bound on the weights -/

/-- The least exponent `κ ≥ 1` with `U ≤ n^κ`. -/
noncomputable def kappaOf (n U : ℕ) : ℝ := max 1 (Real.log U / Real.log n)








































end ThreeSumApsp.Spec

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Hashing_ChoosePrime


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The choice of the prime (proof of Theorem 17, "Hashing modulo a prime")

"We reduce the weights modulo a prime p ∈ [√D/2, √D), chosen deterministically. […] For every prime
p in the range we count the triples with S(a,b,c) ≡ 0 (mod p). […] We select the prime with the
smallest count".  Here S(a,b,c) is the weight of the triangle, the sum of its entries in the three
lists of weights ab, bc and ac, and D is the parameter of Theorem 17.

choosePrime(n, U, ab, bc, ac, D, w), where w is the address of the work area, lists the primes of
the range (`primesList D`) at w, computes the number len of binary digits of U and the numbers
K = ⌈log₂ n⌉ and 2^K (`chLevel_spec`), and goes through the primes once.  A round counts for one
prime, by a call of countPrime with the work area behind the list of the primes, and keeps the prime
if it is the first one or its count is smaller than the best so far (`chKeep_spec`,
`chRound_spec`).

On the pure side, `bestOf f L i` is the first of the first i primes with the smallest count, one
more prime changes it as the program does (`BestSoFar.step`), and at the end it is the chosen prime
(`bestOf_length`).  `choosePrime_spec` is the whole routine.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The numbers of the procedures that choosePrime calls. -/
structure ChNums : Type where
  pPrimes : ℕ
  pBitLen : ℕ
  pCountPrime : ℕ
  cp : CpNums
  pSqrt : ℕ
  pSieve : ℕ

/-- The program holds the procedures that choosePrime calls. -/
structure ChCtx (P : Program) (ν : ChNums) : Prop where
  hPrimes : P[ν.pPrimes]? = some (primesBody ν.pSqrt ν.pSieve)
  hBitLen : P[ν.pBitLen]? = some bitLenBody
  hCountPrime : P[ν.pCountPrime]? = some (countPrimeBody ν.cp)
  cp : CpCtx P ν.cp
  primes : Primes.Ctx P ν.pSqrt ν.pSieve

namespace ChoosePrime

/-- The local variables of choosePrime: the arguments n, U, ab, bc, ac, D, w; the number of primes;
len; K; 2^K; the address of the work area of countPrime; the number of the prime; the prime; its
count; the best prime so far; its count. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Bound : ℕ := 1
@[inherit_doc Num] abbrev ListAB : ℕ := 2
@[inherit_doc Num] abbrev ListBC : ℕ := 3
@[inherit_doc Num] abbrev ListAC : ℕ := 4
@[inherit_doc Num] abbrev Range : ℕ := 5
@[inherit_doc Num] abbrev Work : ℕ := 6
@[inherit_doc Num] abbrev Primes : ℕ := 7
@[inherit_doc Num] abbrev Len : ℕ := 8
@[inherit_doc Num] abbrev Level : ℕ := 9
@[inherit_doc Num] abbrev Rows : ℕ := 10
@[inherit_doc Num] abbrev Area : ℕ := 11
@[inherit_doc Num] abbrev Idx : ℕ := 12
@[inherit_doc Num] abbrev Prime : ℕ := 13
@[inherit_doc Num] abbrev Count : ℕ := 14
@[inherit_doc Num] abbrev Best : ℕ := 15
@[inherit_doc Num] abbrev BestCount : ℕ := 16

end ChoosePrime

open ChoosePrime in
/-- K = ⌈log₂ n⌉ and 2^K, by doubling. -/
def chLevel : Stmt :=
  (Light.Stmt.seq (.set Level (k 0))
    (Light.Stmt.seq (.set Rows (k 1))
      (.while (Light.Cond.lt (v Rows) (v Num))
        (Light.Stmt.seq (.set Rows ((Light.Expr.op Light.Op.add) (v Rows) (v Rows)))
          (.set Level ((Light.Expr.op Light.Op.add) (v Level) (k 1)))))))

open ChoosePrime in
/-- The prime is kept if it is the first one or its count is smaller than the best so far. -/
def chKeep : Stmt :=
  .ite ((Light.Cond.eq (v Idx) (k 0))) ((Light.Stmt.seq (.set Best (v Prime)) (.set BestCount (v Count))))
    (.ite ((Light.Cond.lt (v Count) (v BestCount))) ((Light.Stmt.seq (.set Best (v Prime)) (.set BestCount (v Count)))) .skip)

open ChoosePrime in
/-- One round: the count for the prime number i. -/
def chRound (ν : ChNums) : Stmt :=
  (Light.Stmt.seq (.set Prime (M ((Light.Expr.op Light.Op.add) (v Work) (v Idx))))
    (Light.Stmt.seq
      (.call ν.pCountPrime [v Num, v ListAB, v ListBC, v ListAC, v Prime, v Len, v Level, v Rows, v Area] Count) chKeep))

open ChoosePrime in
/-- choosePrime(n, U, ab, bc, ac, D, w). -/
def choosePrimeBody (ν : ChNums) : Stmt :=
  (Light.Stmt.seq (.call ν.pPrimes [v Work, v Range] Primes)
    (Light.Stmt.seq (.call ν.pBitLen [v Bound] Len)
      (Light.Stmt.seq chLevel
        (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.add) (v Work) (v Primes)))
          (Light.Stmt.seq (.set Best (k 0))
            (Light.Stmt.seq (.set BestCount (k 0))
              (Light.Stmt.seq (.for Idx (v Primes) (chRound ν)) (.set Num (v Best)))))))))

/-- The number of cells that choosePrime may change, from w on: the list of the primes and the work
area of countPrime for the largest possible prime. -/
def chooseCells (n U D : ℕ) : ℕ :=
  Nat.sqrt D + countCells n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n)

/-- An upper bound on the number of steps of choosePrime. -/
def chooseTime (n U D : ℕ) : ℕ :=
  tPrimes D + tBitLen U + 12 * Nat.clog 2 n +
    Nat.sqrt D * (countTime n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n) + 50) + 60

/-- What choosePrime needs: the three lists of n² weights of absolute value at most U lie below w,
the cells from w on lie in the memory, and the numbers that are formed fit in a word. -/
structure ChoosePrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (D w : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  cells : w + chooseCells x.n x.U D ≤ lim.space
  wordD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word
  wordU : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word
  wordN : ((2 * x.n + 1 : ℕ) : ℤ) ≤ lim.word
  wordDbl : ((Nat.sqrt D * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * Nat.clog 2 x.n + 3 ≤ lim.depth

/-! ## The pure side: the best prime so far -/







/-- What the locals best and cnt hold after i primes: nothing yet, or the best prime so far and its
count c, where c q is the count for the prime q. -/
def BestSoFar (c : ℕ → ℤ) (L : List ℕ) (i : ℕ) (best cnt : ℤ) : Prop :=
  (i = 0 ∧ best = 0) ∨
    (1 ≤ i ∧ best = (bestOf (fun q => (c q).toNat) L i : ℕ) ∧
      cnt = c (bestOf (fun q => (c q).toNat) L i) ∧ 0 ≤ cnt)

















/-! ## The parts of the program -/

/-- The local variables of choosePrime during the loop over the primes. -/
@[simp] def chFrame (n U ab bc ac D w nP len K : ℕ) (i q c best cnt : ℤ) : List ℤ :=
  [n, U, ab, bc, ac, D, w, nP, len, K, (2 ^ K : ℕ), (w + nP : ℕ), i, q, c, best, cnt]

section parts

variable {ν : ChNums} {μ μ' : ℕ → ℤ} {n U ab bc ac D w nP len K : ℕ} {AB BC AC : List ℤ}







































variable {x : TriInst}




























/-- The state of choosePrime before round i: the best prime so far and its count are in their
locals, the list of the primes stands at w, and only cells from w on have changed. -/
def ChInv (μ : ℕ → ℤ) (x : TriInst) (D w i : ℕ) (σ : State) : Prop :=
  ∃ (q c best cnt : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (chFrame x.n x.U x.ab x.bc x.ac D w (primesList D).length (bitLen x.U)
      (Nat.clog 2 x.n) i q c best cnt), μ'⟩ ∧
    BestSoFar (fun p => countOf x.n p x.AB x.BC x.AC) (primesList D) i best cnt ∧
    SegN μ' w (primesList D) ∧ SameOutside μ μ' w (chooseCells x.n x.U D)



















































































































end parts

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Witnesses_Scan


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Scanning a piece (the proof of Theorem 17)

"For every query pair that the oracle accepts, scan the piece C_k of its instance for a c with
S(a,b,c) = 0".  The procedure scan (`scanBody`) goes through an interval of vertices `c` for a fixed
pair `(a, b)` (`scan_spec`, `scan_meets`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- A truth value as a number: 1 for true, 0 for false. -/
def bit (b : Bool) : ℤ := if b then 1 else 0






/-! ## The three arrays of weights -/

/-- What `scan` assumes: the three arrays of `n²` weights of absolute value at most `U` lie in the
memory, an address fits in a word, and so does a sum of three weights. -/
structure Weights (lim : Limits) (μ : ℕ → ℤ) (ab bc ac n U : ℕ) (AB BC AC : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  hU : 3 * (U : ℤ) + 1 ≤ lim.word
  arrAB : ArrayAt μ ab AB (n * n) U lim.space
  arrBC : ArrayAt μ bc BC (n * n) U lim.space
  arrAC : ArrayAt μ ac AC (n * n) U lim.space

/-! ## Scanning an interval of vertices -/

namespace Scan

/-- The locals of `scan`.  The arguments: the addresses of the three arrays, `n`, the pair `(a, b)`,
the first vertex `c0` and the number `len` of vertices of the interval.  Then the counter `c`, the
result so far, the weight `w(a,b)`, and the addresses of `w(b, c0)` and of `w(a, c0)`. -/
abbrev AdrAB : ℕ := 0
@[inherit_doc AdrAB] abbrev AdrBC : ℕ := 1
@[inherit_doc AdrAB] abbrev AdrAC : ℕ := 2
@[inherit_doc AdrAB] abbrev Size : ℕ := 3
@[inherit_doc AdrAB] abbrev VtxA : ℕ := 4
@[inherit_doc AdrAB] abbrev VtxB : ℕ := 5
@[inherit_doc AdrAB] abbrev First : ℕ := 6
@[inherit_doc AdrAB] abbrev Len : ℕ := 7
@[inherit_doc AdrAB] abbrev Cnt : ℕ := 8
@[inherit_doc AdrAB] abbrev Hit : ℕ := 9
@[inherit_doc AdrAB] abbrev Wab : ℕ := 10
@[inherit_doc AdrAB] abbrev RowB : ℕ := 11
@[inherit_doc AdrAB] abbrev RowA : ℕ := 12

end Scan

open Scan in
/-- One round of `scan`: if `w(a,b) + w(b, c0 + c) + w(a, c0 + c) = 0` then hit := 1; c := c + 1. -/
def scanRound : Stmt :=
  (Light.Stmt.seq
    (.ite
      (Light.Cond.eq
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v Wab) (M ((Light.Expr.op Light.Op.add) (v RowB) (v Cnt))))
          (M ((Light.Expr.op Light.Op.add) (v RowA) (v Cnt))))
        (k 0))
      (.set Hit (k 1)) .skip)
    (.set Cnt ((Light.Expr.op Light.Op.add) (v Cnt) (k 1))))

open Scan in
/-- scan(ab, bc, ac, n, a, b, c0, len). -/
def scanBody : Stmt :=
  (Light.Stmt.seq (.set Hit (k 0))
    (Light.Stmt.seq
      (.set Wab
        (M
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v AdrAB) ((Light.Expr.op Light.Op.mul) (v VtxA) (v Size))) (v VtxB))))
      (Light.Stmt.seq
        (.set RowB
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v AdrBC) ((Light.Expr.op Light.Op.mul) (v VtxB) (v Size))) (v First)))
        (Light.Stmt.seq
          (.set RowA
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v AdrAC) ((Light.Expr.op Light.Op.mul) (v VtxA) (v Size))) (v First)))
          (Light.Stmt.seq (.set Cnt (k 0))
            (Light.Stmt.seq (.while (Light.Cond.lt (v Cnt) (v Len)) scanRound) (.set 0 (v Hit))))))))

/-- The time of scan. -/
def tScan (len : ℕ) : ℕ := 24 * len + 35













































































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Witnesses_ScanPairs


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Reading the answers of one instance and scanning for witnesses

Proof of Theorem 17: "For every query pair that the oracle accepts, scan the piece C_k of its
instance for a c with S(a,b,c) = 0 [...].  We stop as soon as a zero triangle is found."

scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the
pair `(qa[i], qb[i])`, as long as none has been found (`f = 0`).  The result is the new value of `f`
(`scanPairs_spec`).  No scan is made after the first successful one, so the number of scans is at
most the number of failed scans plus one (`execsUpto_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- Whether a zero triangle has been found before the pair number i; acc j: the answer for the pair
j is not 0; hit j: its scan succeeds. -/
def foundAt (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) : Bool :=
  f || (List.range i).any fun j => acc j && hit j

/-- Whether the pair number i is scanned. -/
def execAt (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) : Bool := acc i && !foundAt acc hit f i

/-- The number of scans among the first w pairs. -/
def execsUpto (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter (execAt acc hit f)).length

/-- The number of accepted pairs among the first w whose scan would fail. -/
def failsUpto (acc hit : ℕ → Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter fun i => acc i && !hit i).length






























/-! ## The routine -/

namespace ScanPairs

/-- The locals of `scanPairs`.  The arguments: the addresses of the answers and of the rows and the
columns of the query pairs, their number `w`, the flag `f`, the addresses of the three arrays of
weights, `n`, and the first vertex and the number of vertices of the piece.  Then the counter. -/
abbrev Out : ℕ := 0
@[inherit_doc Out] abbrev Rows : ℕ := 1
@[inherit_doc Out] abbrev Cols : ℕ := 2
@[inherit_doc Out] abbrev Num : ℕ := 3
@[inherit_doc Out] abbrev Found : ℕ := 4
@[inherit_doc Out] abbrev AdrAB : ℕ := 5
@[inherit_doc Out] abbrev AdrBC : ℕ := 6
@[inherit_doc Out] abbrev AdrAC : ℕ := 7
@[inherit_doc Out] abbrev Size : ℕ := 8
@[inherit_doc Out] abbrev First : ℕ := 9
@[inherit_doc Out] abbrev Len : ℕ := 10
@[inherit_doc Out] abbrev Cnt : ℕ := 11

end ScanPairs

open ScanPairs in
/-- One query pair: if out[i] ≠ 0 and f = 0 then f := scan(ab, bc, ac, n, qa[i], qb[i], c0, len). -/
def scanPairsStep (pScan : ℕ) : Stmt :=
  .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v Out) (v Cnt))) (k 0))) .skip
    (.ite ((Light.Cond.eq (v Found) (k 0)))
      (.call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, M (((Light.Expr.op Light.Op.add) (v Rows) (v Cnt))), M (((Light.Expr.op Light.Op.add) (v Cols) (v Cnt))),
        v First, v Len] Found) .skip)

open ScanPairs in
/-- scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len); the parameter is the procedure number of
`scan`. -/
def scanPairsBody (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Cnt (k 0))
    (Light.Stmt.seq
      (.while (Light.Cond.lt (v Cnt) (v Num))
        (Light.Stmt.seq (scanPairsStep pScan) (.set Cnt ((Light.Expr.op Light.Op.add) (v Cnt) (k 1)))))
      (.set 0 (v Found))))

/-- The time for reading w answers. -/
def tAnswers (w : ℕ) : ℕ := 19 * w + 8

/-- The time of one scan of a piece of len vertices, with its call. -/
def tScanCall (len : ℕ) : ℕ := tScan len + 16

/-- The time of scanPairs, given the number of scans. -/
def tScanPairs (w len execs : ℕ) : ℕ := tAnswers w + tScanCall len * execs

/-- What `scanPairs` assumes about the answers of the solver and the `w` query pairs of an instance:
three arrays in the memory, and the query pairs are pairs of vertices. -/
structure Answers (lim : Limits) (μ : ℕ → ℤ) (out qa qb w n : ℕ) (OUT : List ℤ) (QA QB : List ℕ) :
    Prop where
  arrOUT : ListAt μ out OUT w lim.space
  arrQA : IndexAt μ qa QA w n lim.space
  arrQB : IndexAt μ qb QB w n lim.space
  w_lt : w < lim.space

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {f : Bool}

/-- The answer for the query pair number `i` is not 0. -/
abbrev accOf (OUT : List ℤ) (i : ℕ) : Bool := decide (OUT.getD i 0 ≠ 0)

/-- The scan for the query pair number `i` succeeds. -/
abbrev hitOf (n : ℕ) (AB BC AC : List ℤ) (QA QB : List ℕ) (c0 len i : ℕ) : Bool :=
  scanHit n AB BC AC (QA.getD i 0) (QB.getD i 0) c0 len

/-- The state of `scanPairs` when `i` query pairs have been treated and the counter is `j`. -/
def scanPairsState (μ : ℕ → ℤ) (out qa qb w ab bc ac n c0 len : ℕ) (OUT AB BC AC : List ℤ)
    (QA QB : List ℕ) (f : Bool) (i j : ℕ) : State :=
  ⟨frame [out, qa, qb, w, bit (foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i), ab, bc, ac,
    n, c0, len, j], μ⟩




















































































end

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_InstanceData


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: the list of its instances, as pure data

Proof of Theorem 17, "For each chunk 𝒬 ⊆ W_ϱ and each piece C_k form the instance".  After the prime
has been chosen, the host runs one loop over all instances: instance number `t` belongs to the piece
number `t / chunkCount` of `C` and to the chunk number `t % chunkCount` of the table of chunks.
This file defines what the host writes (`matX`, `matY`, `WI`, `WJ`), what the solver answers
(`ans`), which query pairs are accepted and which scans succeed (`acc`, `hit`), and whether a zero
triangle has been found before instance `t` (`found`).  The class of a residue `ϱ < p` is the
paper's `W_ϱ`: the pairs `(a, b)` whose weight is congruent to `ϱ` modulo `p`.  The pairs are listed
class after class, in the order of the residues, and a chunk is a segment of a class.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The hypotheses of Theorem 17 on its parameters, in natural numbers: "Let 16 ≤ D ≤ n, and let
1 ≤ g ≤ √D be an integer." -/
structure BigCase (n D g : ℕ) : Prop where
  sixteen_le : 16 ≤ D
  le_n : D ≤ n
  one_le_g : 1 ≤ g
  g_le_sqrt : g ≤ Nat.sqrt D

/-- The data on which the loop over the instances depends. -/
structure HostData : Type where
  /-- The number of vertices of each part. -/
  n : ℕ
  /-- The bound on the number of middle vertices of an instance of Lop-AE-SparseTri, that is, the
  inner dimension of its matrices `X` and `Y`. -/
  D : ℕ
  /-- The prime. -/
  p : ℕ
  /-- The number of vertices of a piece of `C`. -/
  q : ℕ
  /-- The largest number of query pairs of an instance. -/
  cap : ℕ
  /-- The weights of the edges `(a, b)`, row by row. -/
  AB : List ℤ
  /-- The weights of the edges `(b, c)`, row by row. -/
  BC : List ℤ
  /-- The weights of the edges `(a, c)`, row by row. -/
  AC : List ℤ

namespace HostData

variable (X : HostData)

/-- The residues modulo `p` of the weights of the edges `(a, b)`. -/
def RAB : List ℕ := residList X.p X.AB
/-- The residues modulo `p` of the weights of the edges `(b, c)`. -/
def RBC : List ℕ := residList X.p X.BC
/-- The residues modulo `p` of the weights of the edges `(a, c)`. -/
def RAC : List ℕ := residList X.p X.AC
/-- The rows `a` of all pairs `(a, b)`, class after class. -/
def QI : List ℕ := queryRows X.n X.p X.RAB
/-- The columns `b` of all pairs `(a, b)`, class after class. -/
def QJ : List ℕ := queryCols X.n X.p X.RAB
/-- The table of the chunks. -/
def CT : List Chunk := chunkTab X.n X.p X.cap X.RAB
/-- The number of chunks. -/
def chunkCount : ℕ := X.CT.length
/-- The number of pieces. -/
def h : ℕ := X.n ⌈/⌉ X.q
/-- The number of instances. -/
def m : ℕ := X.h * X.chunkCount

/-- The first vertex of the piece of instance t. -/
def c0 (t : ℕ) : ℕ := t / X.chunkCount * X.q
/-- The number of vertices of the piece of instance t. -/
def len (t : ℕ) : ℕ := min X.q (X.n - X.c0 t)
/-- The chunk of instance t. -/
def chunk (t : ℕ) : Chunk := X.CT.getD (t % X.chunkCount) ⟨0, 0, 0⟩
/-- The residue `ϱ` of the chunk of instance t. -/
def rho (t : ℕ) : ℕ := (X.chunk t).residue
/-- The first place of the chunk of instance t in the list of all pairs. -/
def lo (t : ℕ) : ℕ := (X.chunk t).start
/-- The number of query pairs of instance t. -/
def w (t : ℕ) : ℕ := (X.chunk t).len

/-- The matrix `X` of instance t. -/
def matX (t : ℕ) : List ℤ := xList X.n X.D X.p (X.c0 t) (X.len t) (X.rho t) X.RAC
/-- The matrix `Y` of instance t. -/
def matY (t : ℕ) : List ℤ := yList X.n X.D X.p (X.c0 t) (X.len t) X.RBC
/-- The rows of the query pairs of instance t. -/
def WI (t : ℕ) : List ℕ := (X.QI.drop (X.lo t)).take (X.w t)
/-- The columns of the query pairs of instance t. -/
def WJ (t : ℕ) : List ℕ := (X.QJ.drop (X.lo t)).take (X.w t)

/-- The answers of a solver of Lop-AE-SparseTri to instance t. -/
def ans (t : ℕ) : List ℤ :=
  (thinOut X.n X.D (X.matX t) (X.matY t) (X.WI t) (X.WJ t)).map fun v => if v = 0 then 0 else 1

/-- The query pair number i of instance t is accepted. -/
def acc (t i : ℕ) : Bool := decide ((X.ans t).getD i 0 ≠ 0)
/-- The scan for the query pair number i of instance t succeeds. -/
def hit (t i : ℕ) : Bool :=
  scanHit X.n X.AB X.BC X.AC ((X.WI t).getD i 0) ((X.WJ t).getD i 0) (X.c0 t) (X.len t)

/-- A zero triangle has been found before instance t. -/
def found : ℕ → Bool
  | 0 => false
  | t + 1 => foundAt (X.acc t) (X.hit t) (found t) (X.w t)

/-- The number of scans made for instance t. -/
def execs (t : ℕ) : ℕ := execsUpto (X.acc t) (X.hit t) (X.found t) (X.w t)
/-- The number of accepted query pairs of instance t whose scan fails or would fail. -/
def fails (t : ℕ) : ℕ := failsUpto (X.acc t) (X.hit t) (X.w t)

end HostData

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_InstanceFacts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: what is true of the list of its instances

Proof of Theorem 17.  A `HostData` describes the instances that the host forms after the prime has
been chosen, the answers of the solver, and the scans.  This file proves, without any program in
sight:

* the instances are well formed: pieces, chunks, query pairs and matrices have the sizes that the
  solver asks for (`Valid.piece_le`, `Valid.lo_add_le`, `Valid.length_WI`, `length_matX`, …);
* the query pair number `i` of instance `t` is `(rowOf t i, colOf t i)`, read off its place
  `a n + b` (`getD_WI`, `getD_WJ`), which is the entry at position `lo t + i` of the list of all
  pairs; every pair meets every vertex of `C` in some instance (`Valid.exists_query`);
* a query pair `(a, b)` is accepted if and only if the piece has a vertex `c` with `p ∣ S(a,b,c)`,
  where `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` is `sumAt` (`acc_iff`), and its scan succeeds if and
  only if the piece has a `c` with `S(a,b,c) = 0` (`hit_iff`);
* a zero triangle is found if and only if there is one (`found_m`; for the reduction on finite sets,
  of which `theorem_17` speaks, the same sentence is `TriangleInstance.exists_mem_acceptedPairs`,
  and neither proof uses the other);
* all scans but one fail (`sum_execs_le`);
* the parameters of Theorem 17 give valid data (`valid_of_params`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostData

/-- What is assumed about the data: positive sizes, a piece with its labels fits into the middle
part, and three lists of `n²` weights. -/
structure Valid (X : HostData) : Prop where
  n_pos : 1 ≤ X.n
  p_pos : 1 ≤ X.p
  q_pos : 1 ≤ X.q
  cap_pos : 1 ≤ X.cap
  qp_le : X.q * X.p ≤ X.D
  lenAB : X.AB.length = X.n * X.n
  lenBC : X.BC.length = X.n * X.n
  lenAC : X.AC.length = X.n * X.n

variable {X : HostData}

/-! ## Residues, pieces and chunks -/

































































/-! ## The query pairs of an instance -/

/-- The place `a n + b` of the query pair `(a, b)` number `i` of instance `t`: the entry at position
`lo t + i` of the list of all pairs. -/
def place (X : HostData) (t i : ℕ) : ℕ := (sortedIdx X.n X.p X.RAB).getD (X.lo t + i) 0

/-- The vertex `a` of the query pair number `i` of instance `t`. -/
def rowOf (X : HostData) (t i : ℕ) : ℕ := X.place t i / X.n

/-- The vertex `b` of the query pair number `i` of instance `t`. -/
def colOf (X : HostData) (t i : ℕ) : ℕ := X.place t i % X.n
















































































/-! ## The two matrices of an instance -/


























































/-! ## Acceptance -/

/-- The weight `S(a,b,c) = w(a,b) + w(b,c) + w(a,c)` of the triangle `(a, b, c)`, read from the
three lists. -/
def sumAt (X : HostData) (a b c : ℕ) : ℤ :=
  X.AB.getD (a * X.n + b) 0 + X.BC.getD (b * X.n + c) 0 + X.AC.getD (a * X.n + c) 0












































































































/-! ## Correctness -/



















































































end HostData

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Instances_WriteMatrices


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The two matrices of an instance (proof of Theorem 17)

"a ∼ (c, σ) ⟺ σ ≡ w(a,c) + ϱ, (c, σ) ∼ b ⟺ σ ≡ -w(b,c) (mod p)."

writeY(y, rbc, n, D, p, c0, len) writes the D × n matrix Y of the instances for the piece
{c0, …, c0 + len - 1} of C: the middle vertex (c, σ) is the row (c - c0) p + σ.  The n² cells from
rbc hold the residues of the weights w(b,c) mod p, that of (b, c) at place b n + c.
writeX(x, rac, n, D, p, c0, len, rho) writes the n × D matrix X for the residue rho; the cells from
rac hold the residues of the weights w(a,c), that of (a, c) at place a n + c.  In the statements and
docstrings below, c counts from 0 within the piece: the c-th member of the piece is the vertex
c0 + c.

Both clear the matrix and then run through the pairs of a vertex and a member of the piece; each
pair marks one cell with a 1.  So both are instances of one pair of loops:

* `markVal` says what a cell holds when the pairs before (u, w) have been handled, and `Marked` says
  it of the memory;
* `markPairs` runs the two loops, given what the body does for one pair (`MarkCtx`);
* `writeYCell_spec` and `writeXCell_spec` treat the bodies: read a residue, form the label, mark the
  cell;
* `getElem_yList` and `getElem_xList` identify the marks of all pairs with the matrices.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Marking cells: the pure side -/

section marks

/-- The cell i has been marked when the pairs (u', w'), w' < W, before (u, w) in lexicographic order
have been handled; the pair (u', w') marks the cell pos u' w'. -/
def CellMarked (pos : ℕ → ℕ → ℕ) (W u w i : ℕ) : Prop :=
  ∃ u' w', (u' < u ∨ (u' = u ∧ w' < w)) ∧ w' < W ∧ pos u' w' = i

open Classical in
/-- The content of the cell i when the pairs before (u, w) have been handled: 1 if it has been
marked, else 0. -/
noncomputable def markVal (pos : ℕ → ℕ → ℕ) (W u w i : ℕ) : ℤ :=
  if CellMarked pos W u w i then 1 else 0

variable {pos : ℕ → ℕ → ℕ} {W u w i : ℕ}


















































end marks

/-! ## Marking cells: the memory -/

/-- The m cells from base hold the marks of the pairs before (u, w), and no other cell has
changed. -/
structure Marked (μ μ' : ℕ → ℤ) (base m : ℕ) (pos : ℕ → ℕ → ℕ) (W u w : ℕ) : Prop where
  cells : ∀ i < m, μ' (base + i) = markVal pos W u w i
  rest : SameOutside μ μ' base m

namespace Marked

variable {μ μ' : ℕ → ℤ} {base m : ℕ} {pos : ℕ → ℕ → ℕ} {U W u w : ℕ}

























end Marked

/-! ## Marking cells: the two loops -/

/-- What the two loops `for u < U: for w < W: cell` need.  L u w t is the list of the locals: u and
w are the counters, in the locals cu and cw, and t is a temporary of the body.  The body takes at
most b steps and marks the cell of the pair (u, w). -/
structure MarkCtx (lim : Limits) (P : Program) (d : ℕ) (μ : ℕ → ℤ) (base m U W b : ℕ)
    (pos : ℕ → ℕ → ℕ) (cu cw : ℕ) (hiU hiW : Expr) (cell : Stmt) (L : ℤ → ℤ → ℤ → List ℤ) :
    Prop where
  wordU : (U : ℤ) ≤ lim.word
  wordW : (W : ℤ) ≤ lim.word
  atU : ∀ u w t, frame (L u w t) cu = u
  atW : ∀ u w t, frame (L u w t) cw = w
  setU : ∀ u w t z, setLocal (L u w t) cu z = L z w t
  setW : ∀ u w t z, setLocal (L u w t) cw z = L u z t
  boundU : ∀ u w t μ', hiU.Gives lim ⟨frame (L u w t), μ'⟩ U
  boundW : ∀ u w t μ', hiW.Gives lim ⟨frame (L u w t), μ'⟩ W
  pos_lt : ∀ u w, u < U → w < W → pos u w < m
  cell_spec : ∀ (u w : ℕ) (t : ℤ) (μ' : ℕ → ℤ), u < U → w < W → SameOutside μ μ' base m →
    Ends lim P d cell ⟨frame (L u w t), μ'⟩ b fun σ' =>
      ∃ t', σ' = ⟨frame (L u w t'), Function.update μ' (base + pos u w) 1⟩

section loops

variable {μ μ' : ℕ → ℤ} {base m U W b : ℕ} {pos : ℕ → ℕ → ℕ} {cu cw : ℕ} {hiU hiW : Expr}
  {cell : Stmt} {L : ℤ → ℤ → ℤ → List ℤ}















































end loops

/-! ## Clearing the matrix -/
















/-! ## What both routines assume -/

/-- The residues R of the n² weights, all below p, stand at res.  The matrix has m = D n cells at
base, apart from the residues.  The piece {c0, …, c0 + len - 1} lies within the n vertices, and its
len p labels within the D middle vertices. -/
structure WritePre (lim : Limits) (μ : ℕ → ℤ) (base m res n D p c0 len : ℕ) (R : List ℕ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  seg : SegN μ res R
  length : R.length = n * n
  lt : ∀ r ∈ R, r < p
  fits : len * p ≤ D
  piece : c0 + len ≤ n
  size : m = D * n
  spaceM : base + m < lim.space
  spaceR : res + n * n < lim.space
  spaceP : 2 * p < lim.space
  apart : Apart base m res (n * n)

namespace WritePre

variable {μ μ' : ℕ → ℤ} {base m res n D p c0 len : ℕ} {R : List ℕ}









































end WritePre

/-! ## The matrix Y -/

namespace WriteY

/-- The local variables of writeY: the arguments y, rbc, n, D, p, c0, len; the number c of the
member of the piece (before that, the counter of the clearing); the vertex b; the residue, then the
label, r; the number D n of cells. -/
abbrev Y : ℕ := 0
@[inherit_doc Y] abbrev RES : ℕ := 1
@[inherit_doc Y] abbrev N : ℕ := 2
@[inherit_doc Y] abbrev DD : ℕ := 3
@[inherit_doc Y] abbrev PR : ℕ := 4
@[inherit_doc Y] abbrev C0 : ℕ := 5
@[inherit_doc Y] abbrev LEN : ℕ := 6
@[inherit_doc Y] abbrev C : ℕ := 7
@[inherit_doc Y] abbrev B : ℕ := 8
@[inherit_doc Y] abbrev R : ℕ := 9
@[inherit_doc Y] abbrev SZ : ℕ := 10

end WriteY

open WriteY in
/-- The pair (c, b) marks its cell: r := rbc[b n + c0 + c]; if r ≠ 0 then r := p - r;
y[(c p + r) n + b] := 1. -/
def writeYCell : Stmt :=
  (Light.Stmt.seq
    (.set R
      (M
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v RES) ((Light.Expr.op Light.Op.mul) (v B) (v N)))
            (v C0))
          (v C))))
    (Light.Stmt.seq (.ite (Light.Cond.eq (v R) (k 0)) .skip (.set R ((Light.Expr.op Light.Op.sub) (v PR) (v R))))
      (.store
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v Y)
            ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v C) (v PR)) (v R))
              (v N)))
          (v B))
        (k 1))))

open WriteY in
/-- writeY(y, rbc, n, D, p, c0, len). -/
def writeYBody : Stmt :=
  (Light.Stmt.seq (.set SZ ((Light.Expr.op Light.Op.mul) (v DD) (v N)))
    (Light.Stmt.seq (.for C (v SZ) (.store ((Light.Expr.op Light.Op.add) (v Y) (v C)) (k 0)))
      (.for C (v LEN) (.for B (v N) writeYCell))))

/-- The time of writeY. -/
def tWriteY (n D len : ℕ) : ℕ := 13 * (D * n) + len * (40 * n + 14) + 16

/-- The label of the row that the pair (c, b) marks. -/
def labY (n p c0 : ℕ) (RBC : List ℕ) (c b : ℕ) : ℕ := (p - RBC.getD (b * n + c0 + c) 0) % p

/-- The cell that the pair (c, b) marks. -/
def posY (n p c0 : ℕ) (RBC : List ℕ) (c b : ℕ) : ℕ := (c * p + labY n p c0 RBC c b) * n + b






















section writeY

variable {μ μ' : ℕ → ℤ} {y rbc n D p c0 len : ℕ} {RBC : List ℕ}



























































































end writeY

/-! ## The matrix X -/

namespace WriteX

/-- The local variables of writeX: the arguments x, rac, n, D, p, c0, len, rho; the vertex a (before
that, the counter of the clearing); the number c of the member of the piece; the label t; the number
n D of cells. -/
abbrev X : ℕ := 0
@[inherit_doc X] abbrev RES : ℕ := 1
@[inherit_doc X] abbrev N : ℕ := 2
@[inherit_doc X] abbrev DD : ℕ := 3
@[inherit_doc X] abbrev PR : ℕ := 4
@[inherit_doc X] abbrev C0 : ℕ := 5
@[inherit_doc X] abbrev LEN : ℕ := 6
@[inherit_doc X] abbrev RHO : ℕ := 7
@[inherit_doc X] abbrev A : ℕ := 8
@[inherit_doc X] abbrev C : ℕ := 9
@[inherit_doc X] abbrev T : ℕ := 10
@[inherit_doc X] abbrev SZ : ℕ := 11

end WriteX

open WriteX in
/-- The pair (a, c) marks its cell: t := rac[a n + c0 + c] + rho; if p ≤ t then t := t - p;
x[a D + c p + t] := 1. -/
def writeXCell : Stmt :=
  (Light.Stmt.seq
    (.set T
      ((Light.Expr.op Light.Op.add)
        (M
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add)
              ((Light.Expr.op Light.Op.add) (v RES) ((Light.Expr.op Light.Op.mul) (v A) (v N))) (v C0))
            (v C)))
        (v RHO)))
    (Light.Stmt.seq (.ite (Light.Cond.lt (v T) (v PR)) .skip (.set T ((Light.Expr.op Light.Op.sub) (v T) (v PR))))
      (.store
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v X) ((Light.Expr.op Light.Op.mul) (v A) (v DD)))
            ((Light.Expr.op Light.Op.mul) (v C) (v PR)))
          (v T))
        (k 1))))

open WriteX in
/-- writeX(x, rac, n, D, p, c0, len, rho). -/
def writeXBody : Stmt :=
  (Light.Stmt.seq (.set SZ ((Light.Expr.op Light.Op.mul) (v N) (v DD)))
    (Light.Stmt.seq (.for A (v SZ) (.store ((Light.Expr.op Light.Op.add) (v X) (v A)) (k 0)))
      (.for A (v N) (.for C (v LEN) writeXCell))))

/-- The time of writeX. -/
def tWriteX (n D len : ℕ) : ℕ := 13 * (n * D) + n * (42 * len + 14) + 16

/-- The label of the column that the pair (a, c) marks. -/
def labX (n p c0 rho : ℕ) (RAC : List ℕ) (a c : ℕ) : ℕ := (RAC.getD (a * n + c0 + c) 0 + rho) % p

/-- The cell that the pair (a, c) marks. -/
def posX (n D p c0 rho : ℕ) (RAC : List ℕ) (a c : ℕ) : ℕ :=
  a * D + (c * p + labX n p c0 rho RAC a c)






















section writeX

variable {μ μ' : ℕ → ℤ} {x rac n D p c0 len rho : ℕ} {RAC : List ℕ}

















































































end writeX

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_Loop


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: the loop over the instances

Proof of Theorem 17.  After the prime has been chosen and the query pairs have been sorted into
classes and cut into chunks, the host runs through all instances: instance number t belongs to the
piece number t / chunkCount of the third part of the vertices and to the chunk number t % chunkCount
of the table of chunks.  For each instance it writes the two biadjacency matrices, calls the solver
of Lop-AE-SparseTri on the chunk (a segment of the sorted arrays of query pairs, so nothing is
copied), and scans the piece for every accepted query pair, as long as no zero triangle has been
found.

The solver is arbitrary.  The facts about the data that the loop relies on are collected in the
structure `HostOk`.

* What the four calls assume is proved without any program: `HostSetting.writeX`,
  `HostSetting.writeY`, `HostSetting.solver`, `HostSetting.weights`, `HostSetting.answers`.
* The program has one lemma for each part of a round: `hostParams_spec` (the parameters of the
  instance), `hostCalls_spec` (the four calls) and `hostNext_spec` (the counters).
  `hostRound_spec` puts them together, and `hostLoop_spec` is the loop: hostLoop returns 1 if a scan
  has found a zero triangle (`X.found X.m`) and 0 if not, changes no cell below x, and takes at most
  `tHostLoop` steps, the sum over the instances of the times of the four calls.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace HostLocal

/-- The number n of vertices of a part. -/
abbrev Size : ℕ := 0
/-- The inner dimension D. -/
abbrev ParD : ℕ := 1
/-- The prime p. -/
abbrev ThePrime : ℕ := 2
/-- The number q of vertices of a piece. -/
abbrev PieceLen : ℕ := 3
/-- The number chunkCount of chunks. -/
abbrev NumChunks : ℕ := 4
/-- The number m of instances. -/
abbrev NumInst : ℕ := 5
/-- The weights w(a,b). -/
abbrev AdrAB : ℕ := 6
/-- The weights w(b,c). -/
abbrev AdrBC : ℕ := 7
/-- The weights w(a,c). -/
abbrev AdrAC : ℕ := 8
/-- The residues of the weights w(a,c). -/
abbrev ResAC : ℕ := 9
/-- The residues of the weights w(b,c). -/
abbrev ResBC : ℕ := 10
/-- The rows of the sorted query pairs. -/
abbrev Rows : ℕ := 11
/-- The columns of the sorted query pairs. -/
abbrev Cols : ℕ := 12
/-- The classes of the chunks. -/
abbrev TabR : ℕ := 13
/-- The first places of the chunks. -/
abbrev TabL : ℕ := 14
/-- The numbers of query pairs of the chunks. -/
abbrev TabW : ℕ := 15
/-- The matrix X. -/
abbrev MatX : ℕ := 16
/-- The matrix Y. -/
abbrev MatY : ℕ := 17
/-- The answers of the solver. -/
abbrev AdrOut : ℕ := 18
/-- The free pointer. -/
abbrev SolverFree : ℕ := 19
/-- The number t of the instance. -/
abbrev Inst : ℕ := 20
/-- The number ch of its chunk. -/
abbrev ChunkNo : ℕ := 21
/-- The first vertex c0 of its piece. -/
abbrev PieceStart : ℕ := 22
/-- 1 if a zero triangle has been found. -/
abbrev Found : ℕ := 23
/-- The number len of vertices of the piece. -/
abbrev Len : ℕ := 24
/-- The class rho of the chunk. -/
abbrev Residue : ℕ := 25
/-- The first place lo of the chunk. -/
abbrev Start : ℕ := 26
/-- The number w of query pairs of the chunk. -/
abbrev NumPairs : ℕ := 27
/-- Results that are not used. -/
abbrev Unused : ℕ := 28

end HostLocal

open HostLocal

/-- The four calls for one instance: the two matrices, the solver, the scans. -/
def hostCalls (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pWriteX [v MatX, v ResAC, v Size, v ParD, v ThePrime, v PieceStart, v Len, v Residue] Unused)
    (Light.Stmt.seq (.call pWriteY [v MatY, v ResBC, v Size, v ParD, v ThePrime, v PieceStart, v Len] Unused)
      (Light.Stmt.seq
        (.call pS
          [v Size, v ParD, v NumPairs, k 1, v MatX, v MatY, (Light.Expr.op Light.Op.add) (v Rows) (v Start),
            (Light.Expr.op Light.Op.add) (v Cols) (v Start), v AdrOut, v SolverFree]
          Unused)
        (.call pScanPairs
          [v AdrOut, (Light.Expr.op Light.Op.add) (v Rows) (v Start), (Light.Expr.op Light.Op.add) (v Cols) (v Start),
            v NumPairs, v Found, v AdrAB, v AdrBC, v AdrAC, v Size, v PieceStart, v Len]
          Found))))

/-- The numbers of the next instance, of its chunk, and the first vertex of its piece. -/
def hostNext : Stmt :=
  (Light.Stmt.seq (.set ChunkNo ((Light.Expr.op Light.Op.add) (v ChunkNo) (k 1)))
    (Light.Stmt.seq
      (.ite (Light.Cond.eq (v ChunkNo) (v NumChunks))
        (Light.Stmt.seq (.set ChunkNo (k 0)) (.set PieceStart ((Light.Expr.op Light.Op.add) (v PieceStart) (v PieceLen))))
        .skip)
      (.set Inst ((Light.Expr.op Light.Op.add) (v Inst) (k 1)))))

/-- The parameters of the instance: the number of vertices of its piece, and the class, the first
place and the number of query pairs of its chunk. -/
def hostParams : Stmt :=
  (Light.Stmt.seq (.set Len (v PieceLen))
    (Light.Stmt.seq
      (.ite (Light.Cond.lt ((Light.Expr.op Light.Op.sub) (v Size) (v PieceStart)) (v PieceLen))
        (.set Len ((Light.Expr.op Light.Op.sub) (v Size) (v PieceStart))) .skip)
      (Light.Stmt.seq (.set Residue (M ((Light.Expr.op Light.Op.add) (v TabR) (v ChunkNo))))
        (Light.Stmt.seq (.set Start (M ((Light.Expr.op Light.Op.add) (v TabL) (v ChunkNo))))
          (.set NumPairs (M ((Light.Expr.op Light.Op.add) (v TabW) (v ChunkNo))))))))

/-- One round of hostLoop. -/
def hostRound (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  (Light.Stmt.seq hostParams (Light.Stmt.seq (hostCalls pS pWriteX pWriteY pScanPairs) hostNext))

/-- hostLoop(n, D, p, q, chunkCount, m, ab, bc, ac, rac, rbc, qi, qj, cr, cl, cw, x, y, out, fr). -/
def hostLoopBody (pS pWriteX pWriteY pScanPairs : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Inst (k 0))
    (Light.Stmt.seq (.set ChunkNo (k 0))
      (Light.Stmt.seq (.set PieceStart (k 0))
        (Light.Stmt.seq (.set Found (k 0))
          (Light.Stmt.seq (.while (Light.Cond.lt (v Inst) (v NumInst)) (hostRound pS pWriteX pWriteY pScanPairs))
            (.set 0 (v Found)))))))

/-- The time for writing the two matrices of an instance whose piece has len vertices, with the
calls and the bookkeeping of a round. -/
def tWrites (n D len : ℕ) : ℕ := 101 + tWriteX n D len + tWriteY n D len

/-- The number of steps of hostLoop, if the solver takes Tn. -/
def tHostLoop (Tn : List ℕ → ℕ) (X : HostData) : ℕ :=
  (∑ t ∈ Finset.range X.m, (tWrites X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairs (X.w t) (X.len t) (X.execs t))) + 14

/-! ## What the loop relies on -/

/-- The facts about the data that the loop relies on; U is a bound on the weights. -/
structure HostOk (X : HostData) (U : ℕ) : Prop where
  valid : X.Valid
  leAB : AbsLe X.AB U
  leBC : AbsLe X.BC U
  leAC : AbsLe X.AC U

/-- The addresses of the arrays. -/
structure HostAddr : Type where
  ab : ℕ
  bc : ℕ
  ac : ℕ
  rac : ℕ
  rbc : ℕ
  qi : ℕ
  qj : ℕ
  cr : ℕ
  cl : ℕ
  cw : ℕ
  x : ℕ
  y : ℕ
  out : ℕ
  fr : ℕ

/-- What the memory holds: the weights, the residues of w(a,c) and w(b,c), the sorted query pairs,
and the three components of the table of chunks. -/
structure HostMem (X : HostData) (A : HostAddr) (μ : ℕ → ℤ) : Prop where
  segAB : Seg μ A.ab X.AB
  segBC : Seg μ A.bc X.BC
  segAC : Seg μ A.ac X.AC
  segRAC : SegN μ A.rac X.RAC
  segRBC : SegN μ A.rbc X.RBC
  segQI : SegN μ A.qi X.QI
  segQJ : SegN μ A.qj X.QJ
  segCR : SegN μ A.cr (X.CT.map fun c => c.residue)
  segCL : SegN μ A.cl (X.CT.map fun c => c.start)
  segCW : SegN μ A.cw (X.CT.map fun c => c.len)

/-- Where the arrays lie: everything that is read lies below x; then come the two matrices, the
answers, and the free pointer. -/
structure HostLay (X : HostData) (A : HostAddr) : Prop where
  bAB : A.ab + X.n * X.n ≤ A.x
  bBC : A.bc + X.n * X.n ≤ A.x
  bAC : A.ac + X.n * X.n ≤ A.x
  bRAC : A.rac + X.n * X.n ≤ A.x
  bRBC : A.rbc + X.n * X.n ≤ A.x
  bQI : A.qi + X.n * X.n ≤ A.x
  bQJ : A.qj + X.n * X.n ≤ A.x
  bCR : A.cr + X.chunkCount ≤ A.x
  bCL : A.cl + X.chunkCount ≤ A.x
  bCW : A.cw + X.chunkCount ≤ A.x
  xy : A.x + X.n * X.D ≤ A.y
  yo : A.y + X.D * X.n ≤ A.out
  ofr : ∀ t < X.m, A.out + X.w t ≤ A.fr

/-- What the limits have to allow for; need is the need of the solver. -/
structure HostLim (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr)
    (need : List ℕ → Need) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  fr : A.fr < lim.space
  prime : 2 * X.p < lim.space
  count : (X.m : ℤ) ≤ lim.word
  step : ((X.n + X.q : ℕ) : ℤ) ≤ lim.word
  weights : ((3 * U + 1 : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  solver : ∀ t < X.m, (need [X.n, X.D, X.w t]).Ok lim A.fr (d + 1)

/-- The context of hostLoop: a solver of Lop-AE-SparseTri, and the procedures writeX, writeY,
scanPairs, scan in the program. -/
structure HostCtx (P₀ R : Program) (pS pWriteX pWriteY pScanPairs pScan : ℕ) (Tn : List ℕ → ℕ)
    (need : List ℕ → Need) : Prop where
  sol : SolvesN lopDetectTask P₀ pS Tn need
  writeX : (P₀ ++ R)[pWriteX]? = some writeXBody
  writeY : (P₀ ++ R)[pWriteY]? = some writeYBody
  scanPairs : (P₀ ++ R)[pScanPairs]? = some (scanPairsBody pScan)
  scan : (P₀ ++ R)[pScan]? = some scanBody

/-- The arguments of hostLoop. -/
def hostLoopArgs (X : HostData) (A : HostAddr) : List ℤ :=
  [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr, A.cl,
    A.cw, A.x, A.y, A.out, A.fr]

/-! ## What the calls assume -/

/-- Everything that hostLoop assumes, and a memory μ' that agrees with the first memory μ below
x. -/
structure HostSetting (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr)
    (need : List ℕ → Need) (μ μ' : ℕ → ℤ) : Prop where
  ok : HostOk X U
  mem : HostMem X A μ
  lay : HostLay X A
  fits : HostLim lim d X U A need
  kept : Kept μ μ' A.x







namespace HostSetting

variable {X : HostData} {U : ℕ} {A : HostAddr} {need : List ℕ → Need} {μ μ' μ'' : ℕ → ℤ} {t : ℕ}


































































































/-- The instance number t, as the solver gets it. -/
def inst (X : HostData) (A : HostAddr) (t : ℕ) : ThinInst :=
  { N := X.n, D := X.D, w := X.w t, U := 1, x := A.x, y := A.y, wi := A.qi + X.lo t,
    wj := A.qj + X.lo t, out := A.out, X := X.matX t, Y := X.matY t, WI := X.WI t, WJ := X.WJ t }

































































end HostSetting

/-! ## The parts of a round -/

variable {P₀ R : Program} {pS pWriteX pWriteY pScanPairs pScan : ℕ} {Tn : List ℕ → ℕ}
  {need : List ℕ → Need} {X : HostData} {U : ℕ} {A : HostAddr} {μ μ' : ℕ → ℤ} {t : ℕ}

/-- The state of hostLoop: the arguments, the numbers t, ch and c0 of the instance, and what the
locals Found, Len, Residue, Start, NumPairs and Unused hold. -/
abbrev hostState (X : HostData) (A : HostAddr) (t ch c0 : ℕ) (fnd len rho lo w res : ℤ)
    (μ' : ℕ → ℤ) : State :=
  ⟨frame [X.n, X.D, X.p, X.q, X.chunkCount, X.m, A.ab, A.bc, A.ac, A.rac, A.rbc, A.qi, A.qj, A.cr,
    A.cl, A.cw, A.x, A.y, A.out, A.fr, t, ch, c0, fnd, len, rho, lo, w, res], μ'⟩
































/-- The time of the four calls. -/
def tCalls (Tn : List ℕ → ℕ) (X : HostData) (t : ℕ) : ℕ :=
  tWriteX X.n X.D (X.len t) + tWriteY X.n X.D (X.len t) + Tn [X.n, X.D, X.w t] +
    tScanPairs (X.w t) (X.len t) (X.execs t) + 52












































































































/-! ## The loop -/

/-- The invariant of the loop, before instance t. -/
def HostInv (lim : Limits) (d : ℕ) (X : HostData) (U : ℕ) (A : HostAddr) (need : List ℕ → Need)
    (μ : ℕ → ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ (len rho lo w res : ℤ) (μ' : ℕ → ℤ),
    σ = hostState X A t (t % X.chunkCount) (X.c0 t) (bit (X.found t)) len rho lo w res μ' ∧
    HostSetting lim d X U A need μ μ'




















































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Instances_Chunks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The table of the chunks

Proof of Theorem 17: "cut it into chunks of at most n²/√D query pairs".  chunks(cls, p, cap, cr, cl,
cw) goes through the `p` classes, whose starts are in the `p + 1` cells from `cls`, cuts each of
them into chunks of at most `cap` places, and writes the residues, the starts and the lengths of the
chunks to `cr`, `cl` and `cw`; the residue of a chunk is the number `rho < p` of its class.  It
returns the number of chunks (`chunks_meets`).  The proof follows the program: one chunk
(`chunksRound_runs`), the chunks of one class (`chunksClass_ends`), all classes.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Chunks

/-- The locals of `chunks`.  The arguments: the address of the starts of the classes, the number `p`
of classes, the largest size `cap` of a chunk, and the addresses of the three tables.  Then the
residue, the start of the next chunk, the end of the class, the number of chunks so far, and the
length of the chunk. -/
abbrev Cls : ℕ := 0
@[inherit_doc Cls] abbrev Num : ℕ := 1
@[inherit_doc Cls] abbrev Cap : ℕ := 2
@[inherit_doc Cls] abbrev TabR : ℕ := 3
@[inherit_doc Cls] abbrev TabL : ℕ := 4
@[inherit_doc Cls] abbrev TabW : ℕ := 5
@[inherit_doc Cls] abbrev Rho : ℕ := 6
@[inherit_doc Cls] abbrev Pos : ℕ := 7
@[inherit_doc Cls] abbrev End : ℕ := 8
@[inherit_doc Cls] abbrev Cnt : ℕ := 9
@[inherit_doc Cls] abbrev Len : ℕ := 10

end Chunks

open Chunks in
/-- One chunk: len := min(cap, end - pos); the three tables get (rho, pos, len) at place cnt;
cnt := cnt + 1; pos := pos + len. -/
def chunksRound : Stmt :=
  (Light.Stmt.seq (.set Len ((Light.Expr.op Light.Op.sub) (v End) (v Pos)))
    (Light.Stmt.seq (.ite (Light.Cond.lt (v Cap) (v Len)) (.set Len (v Cap)) .skip)
      (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v TabR) (v Cnt)) (v Rho))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v TabL) (v Cnt)) (v Pos))
          (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v TabW) (v Cnt)) (v Len))
            (Light.Stmt.seq (.set Cnt ((Light.Expr.op Light.Op.add) (v Cnt) (k 1)))
              (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (v Len)))))))))

open Chunks in
/-- The chunks of the class rho: pos := cls[rho]; end := cls[rho + 1]; while pos < end: one
chunk. -/
def chunksClass : Stmt :=
  (Light.Stmt.seq (.set Pos (M ((Light.Expr.op Light.Op.add) (v Cls) (v Rho))))
    (Light.Stmt.seq (.set End (M ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Cls) (v Rho)) (k 1))))
      (.while (Light.Cond.lt (v Pos) (v End)) chunksRound)))

open Chunks in
/-- chunks(cls, p, cap, cr, cl, cw). -/
def chunksBody : Stmt :=
  (Light.Stmt.seq (.set Rho (k 0))
    (Light.Stmt.seq (.set Cnt (k 0))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v Rho) (v Num))
          (Light.Stmt.seq chunksClass (.set Rho ((Light.Expr.op Light.Op.add) (v Rho) (k 1)))))
        (.set 0 (v Cnt)))))

/-- The time of chunks, for p classes and nCh chunks. -/
def tChunks (p nCh : ℕ) : ℕ := 37 * nCh + 24 * p + 10

/-- The arguments of chunks; the room `R` of each of the three tables; the list `C` of the starts of
the classes, which stands at `cls`, and a bound `B` on them. -/
structure ChunksArgs : Type where
  (cls p cap cr cl cw : ℕ)
  (R B : ℕ) (C : List ℕ)

/-- The values of the arguments of chunks. -/
abbrev ChunksArgs.vals (x : ChunksArgs) : List ℤ := [x.cls, x.p, x.cap, x.cr, x.cl, x.cw]

/-- The locals of chunks: the arguments and the five locals that change. -/
abbrev ChunksArgs.locals (x : ChunksArgs) (rho pos hi cnt len : ℤ) : List ℤ :=
  [x.cls, x.p, x.cap, x.cr, x.cl, x.cw, rho, pos, hi, cnt, len]

/-- The table that chunks writes. -/
abbrev ChunksArgs.table (x : ChunksArgs) : List Chunk := chunkTabOf x.p x.cap x.C

/-- Only cells of the three tables have changed. -/
abbrev ChunksArgs.Same (x : ChunksArgs) (μ μ' : ℕ → ℤ) : Prop :=
  SameOutside3 μ μ' x.cr x.R x.cl x.R x.cw x.R

/-- What chunks assumes: the starts, at most B, at cls; room for R chunks in each of the three
tables; the areas lie apart and inside the memory. -/
structure ChunksPre (lim : Limits) (μ : ℕ → ℤ) (x : ChunksArgs) : Prop where
  seg : SegN μ x.cls x.C
  len : x.C.length = x.p + 1
  le : ∀ s ∈ x.C, s ≤ x.B
  room : (chunkTabOf x.p x.cap x.C).length ≤ x.R
  hcap : 1 ≤ x.cap := by first
                           | omega
                           | ( (try have := Light.Std.space_le (by assumption))
                               (try have := Light.Std.const_le (by assumption))
                               simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  hB : x.B < lim.space := by first
                             | omega
                             | ( (try have := Light.Std.space_le (by assumption))
                                 (try have := Light.Std.const_le (by assumption))
                                 simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cls_le : x.cls + (x.p + 1) < lim.space := by first
                                               | omega
                                               | ( (try have := Light.Std.space_le (by assumption))
                                                   (try have := Light.Std.const_le (by assumption))
                                                   simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cr_le : x.cr + x.R < lim.space := by first
                                       | omega
                                       | ( (try have := Light.Std.space_le (by assumption))
                                           (try have := Light.Std.const_le (by assumption))
                                           simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cl_le : x.cl + x.R < lim.space := by first
                                       | omega
                                       | ( (try have := Light.Std.space_le (by assumption))
                                           (try have := Light.Std.const_le (by assumption))
                                           simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cw_le : x.cw + x.R < lim.space := by first
                                       | omega
                                       | ( (try have := Light.Std.space_le (by assumption))
                                           (try have := Light.Std.const_le (by assumption))
                                           simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cls_cr : Apart x.cls (x.p + 1) x.cr x.R := by first
                                                | omega
                                                | ( (try have := Light.Std.space_le (by assumption))
                                                    (try have := Light.Std.const_le (by assumption))
                                                    simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cls_cl : Apart x.cls (x.p + 1) x.cl x.R := by first
                                                | omega
                                                | ( (try have := Light.Std.space_le (by assumption))
                                                    (try have := Light.Std.const_le (by assumption))
                                                    simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cls_cw : Apart x.cls (x.p + 1) x.cw x.R := by first
                                                | omega
                                                | ( (try have := Light.Std.space_le (by assumption))
                                                    (try have := Light.Std.const_le (by assumption))
                                                    simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cr_cl : Apart x.cr x.R x.cl x.R := by first
                                        | omega
                                        | ( (try have := Light.Std.space_le (by assumption))
                                            (try have := Light.Std.const_le (by assumption))
                                            simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cr_cw : Apart x.cr x.R x.cw x.R := by first
                                        | omega
                                        | ( (try have := Light.Std.space_le (by assumption))
                                            (try have := Light.Std.const_le (by assumption))
                                            simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cl_cw : Apart x.cl x.R x.cw x.R := by first
                                        | omega
                                        | ( (try have := Light.Std.space_le (by assumption))
                                            (try have := Light.Std.const_le (by assumption))
                                            simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

/-! ## The pure side -/

section pure






/-- The chunks of the class number rho. -/
def chunkRow (cap : ℕ) (C : List ℕ) (rho : ℕ) : List Chunk :=
  chunksOf cap (C.getD rho 0) (C.getD (rho + 1) 0) rho





/-- The table when the classes before rho and i chunks of the class rho have been handled. -/
def tabAt (cap : ℕ) (C : List ℕ) (rho i : ℕ) : List Chunk :=
  (List.range rho).flatMap (chunkRow cap C) ++ (chunkRow cap C rho).take i























































end pure

/-! ## The tables in the memory -/

variable {μ μ' : ℕ → ℤ} {x : ChunksArgs}

/-- The three tables hold the list T, and nothing else has changed. -/
structure TabInv (μ μ' : ℕ → ℤ) (x : ChunksArgs) (T : List Chunk) : Prop where
  sr : SegN μ' x.cr (T.map (·.residue))
  sl : SegN μ' x.cl (T.map (·.start))
  sw : SegN μ' x.cw (T.map (·.len))
  same : x.Same μ μ'


































/-! ## The program -/

variable (hw : (lim.space : ℤ) ≤ lim.word)

include hw



















/-- The state of `chunks` when the residue is `rho` and the three tables hold the list `T`. -/
def ChunksInv (μ : ℕ → ℤ) (x : ChunksArgs) (rho : ℕ) (T : List Chunk) (σ : State) : Prop :=
  ∃ (pos hi len : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (x.locals rho pos hi T.length len), μ'⟩ ∧ TabInv μ μ' x T
































































































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Instances_Classes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The classes W_ϱ of the pairs (proof of Theorem 17)

"For ϱ ∈ ℤ_p let W_ϱ be the set of edges (a,b) ∈ A × B with w(a,b) ≡ ϱ (mod p)".  (The cutting of
the classes into chunks, with which the sentence goes on, is a routine of its own.)

classes(rab, n, p, cls, cur, qi, qj) sorts the n² pairs (a, b) by the residue of w(a,b), which is in
the cell rab + a n + b, keeping the row-major order within a class: a stable counting sort.  It
writes the rows of the sorted pairs to qi, their columns to qj, and the places where the classes
start to cls.  The row and the column of the current pair are kept in two counters, so that no
division is needed.  `classes_meets` proves this, within `tClasses n p` steps, a number linear in
n² + p.

The routine has five phases.  Between them the state is described by `ClsState`:

* `clsZero_ends`: the counters are cleared;
* `clsCount_ends`: the sizes of the classes are counted;
* `clsPrefix_ends`: prefix sums turn the sizes into the starts;
* `clsCopy_ends`: the starts are copied to cur, the next free places;
* `clsPlace_ends`: each pair goes to the next free place of its class (`ClsPlaced.step` for the
  memory, `clsPlaceOne_ends` for the program), and row and column step to the next pair.

The place of a pair is its place `sortPos` in a stable sort; `getD_sortedIdx` and
`segN_map_sortedIdx` identify what stands there with the lists of the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side: the lists of the specification and the places of a stable sort -/

section pure

/-- The key of the pair number i. -/
def clsKey (RAB : List ℕ) : ℕ → ℕ := fun i => RAB.getD i 0


















































end pure

/-! ## The routine -/

namespace Classes

/-- Local 0 of classes: the address of the residues. -/
abbrev Rab : ℕ := 0
/-- Local 1 of classes: the number n of vertices of a part. -/
abbrev Size : ℕ := 1
/-- Local 2 of classes: the prime p. -/
abbrev Prime : ℕ := 2
/-- Local 3 of classes: the address of the starts of the classes. -/
abbrev Cls : ℕ := 3
/-- Local 4 of classes: the address of the next free places. -/
abbrev Cur : ℕ := 4
/-- Local 5 of classes: the address of the rows of the sorted pairs. -/
abbrev Rows : ℕ := 5
/-- Local 6 of classes: the address of their columns. -/
abbrev Cols : ℕ := 6
/-- Local 7 of classes: the number n² of pairs. -/
abbrev Pairs : ℕ := 7
/-- Local 8 of classes: a counter. -/
abbrev Idx : ℕ := 8
/-- Local 9 of classes: an address. -/
abbrev Addr : ℕ := 9
/-- Local 10 of classes: the row of the current pair. -/
abbrev Row : ℕ := 10
/-- Local 11 of classes: its column. -/
abbrev Col : ℕ := 11
/-- Local 12 of classes: its place. -/
abbrev Place : ℕ := 12

end Classes

open Classes in
/-- cls[t] := 0 for t ≤ p. -/
def clsZero : Stmt := .for Idx (((Light.Expr.op Light.Op.add) (v Prime) (k 1))) (.store (((Light.Expr.op Light.Op.add) (v Cls) (v Idx))) (k 0))

open Classes in
/-- cls[rab[i] + 1] += 1 for i < n². -/
def clsCount : Stmt :=
  .for Idx (v Pairs) (
    (Light.Stmt.seq
      (.set Addr
        ((Light.Expr.op Light.Op.add)
          ((Light.Expr.op Light.Op.add) (v Cls) (M ((Light.Expr.op Light.Op.add) (v Rab) (v Idx)))) (k 1)))
      (.store (v Addr) ((Light.Expr.op Light.Op.add) (M (v Addr)) (k 1)))))

open Classes in
/-- cls[t] += cls[t - 1] for t = 1, …, p. -/
def clsPrefix : Stmt :=
  (Light.Stmt.seq (.set Idx (k 1))
    (.while (Light.Cond.le (v Idx) (v Prime))
      (Light.Stmt.seq
        (.store ((Light.Expr.op Light.Op.add) (v Cls) (v Idx))
          ((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Cls) (v Idx)))
            (M ((Light.Expr.op Light.Op.sub) ((Light.Expr.op Light.Op.add) (v Cls) (v Idx)) (k 1)))))
        (.set Idx ((Light.Expr.op Light.Op.add) (v Idx) (k 1))))))

open Classes in
/-- cur[t] := cls[t] for t < p. -/
def clsCopy : Stmt := pass Idx (v Prime) (v Cur) (M (((Light.Expr.op Light.Op.add) (v Cls) (v Idx))))

open Classes in
/-- The pair number i, which is (row, col), goes to the next free place of its class. -/
def clsPlaceOne : Stmt :=
  (Light.Stmt.seq (.set Addr ((Light.Expr.op Light.Op.add) (v Cur) (M ((Light.Expr.op Light.Op.add) (v Rab) (v Idx)))))
    (Light.Stmt.seq (.set Place (M (v Addr)))
      (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Rows) (v Place)) (v Row))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Cols) (v Place)) (v Col))
          (.store (v Addr) ((Light.Expr.op Light.Op.add) (v Place) (k 1)))))))

open Classes in
/-- All pairs go to their places. -/
def clsPlace : Stmt :=
  (Light.Stmt.seq (.set Row (k 0))
    (Light.Stmt.seq (.set Col (k 0)) (.for Idx (v Pairs) (Light.Stmt.seq clsPlaceOne (nextPair Row Col Size)))))

open Classes in
/-- classes(rab, n, p, cls, cur, qi, qj). -/
def classesBody : Stmt :=
  (Light.Stmt.seq (.set Pairs ((Light.Expr.op Light.Op.mul) (v Size) (v Size)))
    (Light.Stmt.seq clsZero (Light.Stmt.seq clsCount (Light.Stmt.seq clsPrefix (Light.Stmt.seq clsCopy clsPlace)))))

/-- The time of classes. -/
def tClasses (n p : ℕ) : ℕ := 70 * (n * n) + 56 * p + 57

/-- The arguments of classes, and the list `RAB` of the residues, which stands at `rab`. -/
structure ClassesArgs : Type where
  (rab n p cls cur qi qj : ℕ)
  (RAB : List ℕ)

/-- The values of the arguments of classes. -/
abbrev ClassesArgs.vals (x : ClassesArgs) : List ℤ := [x.rab, x.n, x.p, x.cls, x.cur, x.qi, x.qj]

/-- The locals of classes: the arguments, the number n² of pairs, and the five that change. -/
abbrev ClassesArgs.locals (x : ClassesArgs) (i ad row col pl : ℤ) : List ℤ :=
  [x.rab, x.n, x.p, x.cls, x.cur, x.qi, x.qj, (x.n * x.n : ℕ), i, ad, row, col, pl]

/-- Only cells of the four areas that classes writes have changed. -/
abbrev ClassesArgs.Same (x : ClassesArgs) (μ μ' : ℕ → ℤ) : Prop :=
  SameOutside μ μ' x.cls (x.qj + x.n * x.n - x.cls)

/-- What classes assumes: the residues, below p, stand at rab; behind them lie, in this order, the
four areas cls, cur, qi and qj that it writes; everything is inside the memory. -/
structure ClassesPre (lim : Limits) (μ : ℕ → ℤ) (x : ClassesArgs) : Prop where
  seg : SegN μ x.rab x.RAB
  len : x.RAB.length = x.n * x.n
  lt : ∀ r ∈ x.RAB, r < x.p
  rab_le : x.rab + x.n * x.n ≤ x.cls := by first
                                             | omega
                                             | ( (try have := Light.Std.space_le (by assumption))
                                                 (try have := Light.Std.const_le (by assumption))
                                                 simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cls_le : x.cls + (x.p + 1) ≤ x.cur := by first
                                             | omega
                                             | ( (try have := Light.Std.space_le (by assumption))
                                                 (try have := Light.Std.const_le (by assumption))
                                                 simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  cur_le : x.cur + x.p ≤ x.qi := by first
                                      | omega
                                      | ( (try have := Light.Std.space_le (by assumption))
                                          (try have := Light.Std.const_le (by assumption))
                                          simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  qi_le : x.qi + x.n * x.n ≤ x.qj := by first
                                          | omega
                                          | ( (try have := Light.Std.space_le (by assumption))
                                              (try have := Light.Std.const_le (by assumption))
                                              simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  qj_le : x.qj + x.n * x.n < lim.space := by first
                                             | omega
                                             | ( (try have := Light.Std.space_le (by assumption))
                                                 (try have := Light.Std.const_le (by assumption))
                                                 simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

section phases

variable {μ μ' : ℕ → ℤ} {x : ClassesArgs}
















/-- A state of classes between two phases: the locals hold the arguments and n², only the four areas
have been written, and R holds of the memory. -/
def ClsState (μ : ℕ → ℤ) (x : ClassesArgs) (R : (ℕ → ℤ) → Prop) (σ : State) : Prop :=
  ∃ (i ad row col pl : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (x.locals i ad row col pl), μ'⟩ ∧ x.Same μ μ' ∧ R μ'

/-- After the first phase: the counters are 0. -/
def ClsZeroed (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop := ∀ t ≤ x.p, μ' (x.cls + t) = 0

/-- After the second phase: the cell t + 1 holds the size of the class t. -/
def ClsCounted (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop :=
  μ' x.cls = 0 ∧ ∀ t < x.p, μ' (x.cls + (t + 1)) = (cntEq (clsKey x.RAB) t (x.n * x.n) : ℕ)

/-- After the third phase: the cell t holds the start of the class t. -/
def ClsStarts (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop :=
  ∀ t ≤ x.p, μ' (x.cls + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)

variable {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)

include hw




































































































/-- After the fourth phase: cur holds the starts as well. -/
def ClsCopied (x : ClassesArgs) (μ' : ℕ → ℤ) : Prop :=
  ClsStarts x μ' ∧ ∀ t < x.p, μ' (x.cur + t) = (cntLt (clsKey x.RAB) t (x.n * x.n) : ℕ)



















/-- While the pairs are placed, before the pair number i: cls holds the starts, cur the next free
place of each class, and the pairs before i stand at their places. -/
structure ClsPlaced (x : ClassesArgs) (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  keep : ClsStarts x μ'
  next : ∀ t < x.p,
    μ' (x.cur + t) = ((cntLt (clsKey x.RAB) t (x.n * x.n) + cntEq (clsKey x.RAB) t i : ℕ) : ℤ)
  done : ∀ j < i, μ' (x.qi + sortPos (clsKey x.RAB) (x.n * x.n) j) = (j / x.n : ℕ) ∧
    μ' (x.qj + sortPos (clsKey x.RAB) (x.n * x.n) j) = (j % x.n : ℕ)



































































































end phases






























end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Witnesses_BruteForce


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}












/-- Some `b` below `b'` gives a zero triangle with `a`. -/
def bruteRow (n : ℕ) (AB BC AC : List ℤ) (a b' : ℕ) : Bool :=
  (List.range b').any fun b => scanHit n AB BC AC a b 0 n

/-- Some `a` below `a'` is in a zero triangle. -/
def bruteAll (n : ℕ) (AB BC AC : List ℤ) (a' : ℕ) : Bool :=
  (List.range a').any fun a => bruteRow n AB BC AC a n









namespace Brute

/-- The locals of `brute`.  The arguments: `n`, `U`, the addresses of the three arrays, and the free
pointer.  Then the vertices `a` and `b`, the result so far, and the result of a scan. -/
abbrev Size : ℕ := 0

@[inherit_doc Size] abbrev AdrAB : ℕ := 2
@[inherit_doc Size] abbrev AdrBC : ℕ := 3
@[inherit_doc Size] abbrev AdrAC : ℕ := 4

@[inherit_doc Size] abbrev VtxA : ℕ := 6
@[inherit_doc Size] abbrev VtxB : ℕ := 7
@[inherit_doc Size] abbrev Hit : ℕ := 8
@[inherit_doc Size] abbrev Res : ℕ := 9

end Brute

open Brute in
/-- One pair `(a, b)`: res := scan(ab, bc, ac, n, a, b, 0, n); if res = 1 then hit := 1. -/
def brutePair (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, v VtxA, v VtxB, k 0, v Size] Res)
    (.ite (Light.Cond.eq (v Res) (k 1)) (.set Hit (k 1)) .skip))

open Brute in
/-- The inner loop of brute: all `b` for one `a`. -/
def bruteInner (pScan : ℕ) : Stmt := Stmt.for VtxB (v Size) (brutePair pScan)

open Brute in
/-- brute(n, U, ab, bc, ac, fr); the parameter is the procedure number of `scan`. -/
def bruteBody (pScan : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Hit (k 0)) (Light.Stmt.seq (Stmt.for VtxA (v Size) (bruteInner pScan)) (.set 0 (v Hit))))

/-- The time of brute. -/
def tBrute (n : ℕ) : ℕ := 100 * n ^ 3 + 100

/-- What brute needs: sums of three weights, no cells, one call. -/
def bruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩











section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}











































end





























































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_Text


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: the top procedure

The host procedure et17(n, U, ab, bc, ac, fr) decides Exact Triangle with the help of an arbitrary
solver of Lop-AE-SparseTri (proof of Theorem 17).  It computes the parameters `D` and `g` by two
procedures that are parameters of the construction, and `s = ⌊√D⌋`.  For small `n`
(`D < 16`, `n < D`, `g < 1` or `s < g`) it runs the brute force.  Otherwise it chooses the prime,
computes the largest number of query pairs, the number of vertices of a piece and the number of
pieces, lays out its arrays from the free pointer on, computes the residues of the weights, sorts
the pairs `(a, b)` into classes, cuts the classes into chunks, and runs the loop over the instances.

This file holds the program (`et17Body`), its time and its need (`hostTime`, `hostNeed`), what it
assumes about the program around it (`Et17Ctx`), and the data, the addresses and the local variables
of a run.

**The way through the files on the host**, each named by its main result.

1. The instances as data, with no program in sight: what the host writes, what the solver answers
   and which scans succeed (`HostData`); a zero triangle is found if and only if there is one
   (`HostData.found_m`); a failed scan belongs to a false positive of its own
   (`HostData.sum_fails_le`); there are at most 4ng instances (`HostData.m_le`).
2. The loop over the instances (`hostLoop_spec`).
3. The text of the top procedure (this file), in three parts and the small case.
4. The parts: the parameters and the small case (`et17Params_spec`, `et17Small_spec`); the prime,
   the sizes and the addresses (`et17Sizes_spec`, `et17Addr_spec`); the arrays and the call of the
   loop (`et17Tables_spec`).
5. What the parts need: the limits cover what the called procedures ask for (`choosePre_of_ok`,
   `hostLim_of_ok`), and the time of a run is within the worst case (`hostRunTime_le`).
6. The parts together: et17 decides Exact Triangle (`et17_spec`).
7. The list of the procedures with their numbers; with a solver it is a solver (`et17Procs`,
   `et17_solves`).
8. For the claim: the need is polynomially bounded (`hostNeed_poly`), the time obeys the bound of
   Theorem 17 (`obeysBound17_hostTime`), and so the claim holds for programs of the light language
   (`claim17_of_host`, `claim_theorem_17₅`, `claim_theorem_17₂₆`).

The layout, from the free pointer `fr` on: the table of doubles (`len + 1` cells, where
`len = bitLen U` is the number of binary digits of `U`; cell `j` holds `2^j p`, for residues without
division); the residues of `w(a,b)`, `w(b,c)`, `w(a,c)` (`n²` each); the starts of the classes
(`p + 1`); running places (`p`; while the pairs are sorted, cell `ϱ` holds the next free place of
the class `ϱ`); rows and columns of the sorted pairs (`n²` each); the three components of the table
of chunks (`n² + p` each); `X` (`n D`); `Y` (`D n`); the answers (`cap`); the solver's free pointer.

Notation: `κ` is the exponent in `|w(e)| ≤ n^κ`, the paper's ν; as in the paper, `F(p)` is the
number of false positives of `p`, that is, of triples with `S(a,b,c) = w(a,b) + w(b,c) + w(a,c) ≠ 0`
and `p ∣ S(a,b,c)`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The procedure -/

/-- The numbers of the procedures that et17 calls, directly or through the procedures that it
calls: the two parameter procedures, sqrt, brute, scan, choosePrime, queryCapNat, ceilDiv, bitLen,
dblTable, resid, residues, classes, chunks, hostLoop, the solver, writeX, writeY, scanPairs, and
the procedures below choosePrime. -/
structure Et17Nums : Type where
  pD : ℕ
  pG : ℕ
  pSqrt : ℕ
  pBrute : ℕ
  pScan : ℕ
  pChoose : ℕ
  pCap : ℕ
  pCeil : ℕ
  pBitLen : ℕ
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pClasses : ℕ
  pChunks : ℕ
  pLoop : ℕ
  pS : ℕ
  pWriteX : ℕ
  pWriteY : ℕ
  pScanPairs : ℕ
  ch : ChNums

namespace Et17

/-- The locals of `et17`.  The arguments: `n`, `U`, the addresses of the three arrays of weights,
and the free pointer (the table of doubles is there).  Then `D`, `g`, `s = ⌊√D⌋`, the prime `p`,
`cap`, the number `q` of vertices of a piece, the number `h` of pieces, `len = bitLen U`, and `n²`.
Then the addresses of the residues of `w(a,b)`, `w(b,c)`, `w(a,c)`, of the starts of the classes,
the running places, the rows and the columns of the sorted pairs, the three components of the table
of chunks, `X`, `Y`, the answers, and the solver's free pointer.  Then `n² + p`, the number of
chunks, the number of instances, a flag (also the place for results that are not used), and `n D`.
-/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AdrAB : ℕ := 2
@[inherit_doc Size] abbrev AdrBC : ℕ := 3
@[inherit_doc Size] abbrev AdrAC : ℕ := 4
@[inherit_doc Size] abbrev Free : ℕ := 5
@[inherit_doc Size] abbrev ParD : ℕ := 6
@[inherit_doc Size] abbrev ParG : ℕ := 7
@[inherit_doc Size] abbrev RootD : ℕ := 8
@[inherit_doc Size] abbrev ThePrime : ℕ := 9
@[inherit_doc Size] abbrev Cap : ℕ := 10
@[inherit_doc Size] abbrev PieceLen : ℕ := 11
@[inherit_doc Size] abbrev NumPieces : ℕ := 12
@[inherit_doc Size] abbrev Bits : ℕ := 13
@[inherit_doc Size] abbrev SizeSq : ℕ := 14
@[inherit_doc Size] abbrev ResAB : ℕ := 16
@[inherit_doc Size] abbrev ResBC : ℕ := 17
@[inherit_doc Size] abbrev ResAC : ℕ := 18
@[inherit_doc Size] abbrev Cls : ℕ := 19
@[inherit_doc Size] abbrev Cur : ℕ := 20
@[inherit_doc Size] abbrev Rows : ℕ := 21
@[inherit_doc Size] abbrev Cols : ℕ := 22
@[inherit_doc Size] abbrev TabR : ℕ := 23
@[inherit_doc Size] abbrev TabL : ℕ := 24
@[inherit_doc Size] abbrev TabW : ℕ := 25
@[inherit_doc Size] abbrev MatX : ℕ := 26
@[inherit_doc Size] abbrev MatY : ℕ := 27
@[inherit_doc Size] abbrev AdrOut : ℕ := 28
@[inherit_doc Size] abbrev SolverFree : ℕ := 29
@[inherit_doc Size] abbrev Room : ℕ := 30
@[inherit_doc Size] abbrev NumChunks : ℕ := 31
@[inherit_doc Size] abbrev NumInst : ℕ := 32
@[inherit_doc Size] abbrev Small : ℕ := 33
@[inherit_doc Size] abbrev Area : ℕ := 34

end Et17

open Et17 in
/-- The first part of et17: `D`, `g`, `s`, and the flag that says whether `n` is small. -/
def et17Params (ν : Et17Nums) : Stmt :=
  (Light.Stmt.seq (.call ν.pD [v Size] ParD)
    (Light.Stmt.seq (.call ν.pG [v ParD] ParG)
      (Light.Stmt.seq (.call ν.pSqrt [v ParD] RootD)
        (Light.Stmt.seq (.ite (Light.Cond.lt (v ParD) (k 16)) (.set _root_.Light.Sec3.Et17.Small (k 1)) (.set _root_.Light.Sec3.Et17.Small (v _root_.Light.Sec3.Et17.Small)))
          (Light.Stmt.seq (.ite (Light.Cond.lt (v Size) (v ParD)) (.set _root_.Light.Sec3.Et17.Small (k 1)) (.set _root_.Light.Sec3.Et17.Small (v _root_.Light.Sec3.Et17.Small)))
            (Light.Stmt.seq (.ite (Light.Cond.lt (v ParG) (k 1)) (.set _root_.Light.Sec3.Et17.Small (k 1)) (.set _root_.Light.Sec3.Et17.Small (v _root_.Light.Sec3.Et17.Small)))
              (Light.Stmt.seq (.ite (Light.Cond.lt (v RootD) (v ParG)) (.set _root_.Light.Sec3.Et17.Small (k 1)) (.set _root_.Light.Sec3.Et17.Small (v _root_.Light.Sec3.Et17.Small)))
                .skip)))))))

open Et17 in
/-- The end of the second part: the sizes n², nD, n² + p, and the addresses of the arrays. -/
def et17Addr : Stmt :=
  (Light.Stmt.seq (.set SizeSq ((Light.Expr.op Light.Op.mul) (v Size) (v Size)))
    (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Size) (v ParD)))
      (Light.Stmt.seq (.set Room ((Light.Expr.op Light.Op.add) (v SizeSq) (v ThePrime)))
        (Light.Stmt.seq (.set ResAB ((Light.Expr.op Light.Op.add) (v Free) ((Light.Expr.op Light.Op.add) (v Bits) (k 1))))
          (Light.Stmt.seq (.set ResBC ((Light.Expr.op Light.Op.add) (v ResAB) (v SizeSq)))
            (Light.Stmt.seq (.set ResAC ((Light.Expr.op Light.Op.add) (v ResBC) (v SizeSq)))
              (Light.Stmt.seq (.set Cls ((Light.Expr.op Light.Op.add) (v ResAC) (v SizeSq)))
                (Light.Stmt.seq
                  (.set Cur ((Light.Expr.op Light.Op.add) (v Cls) ((Light.Expr.op Light.Op.add) (v ThePrime) (k 1))))
                  (Light.Stmt.seq (.set Rows ((Light.Expr.op Light.Op.add) (v Cur) (v ThePrime)))
                    (Light.Stmt.seq (.set Cols ((Light.Expr.op Light.Op.add) (v Rows) (v SizeSq)))
                      (Light.Stmt.seq (.set TabR ((Light.Expr.op Light.Op.add) (v Cols) (v SizeSq)))
                        (Light.Stmt.seq (.set TabL ((Light.Expr.op Light.Op.add) (v TabR) (v Room)))
                          (Light.Stmt.seq (.set TabW ((Light.Expr.op Light.Op.add) (v TabL) (v Room)))
                            (Light.Stmt.seq (.set MatX ((Light.Expr.op Light.Op.add) (v TabW) (v Room)))
                              (Light.Stmt.seq (.set MatY ((Light.Expr.op Light.Op.add) (v MatX) (v Area)))
                                (Light.Stmt.seq (.set AdrOut ((Light.Expr.op Light.Op.add) (v MatY) (v Area)))
                                  (Light.Stmt.seq (.set SolverFree ((Light.Expr.op Light.Op.add) (v AdrOut) (v Cap)))
                                    .skip)))))))))))))))))

open Et17 in
/-- The second part: the prime, the sizes, and the addresses of the arrays. -/
def et17Sizes (ν : Et17Nums) : Stmt :=
  (Light.Stmt.seq (.call ν.pChoose [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v ParD, v Free] ThePrime)
    (Light.Stmt.seq (.call ν.pCap [v Size, v ParD] Cap)
      (Light.Stmt.seq (.call ν.pCeil [v RootD, v ParG] PieceLen)
        (Light.Stmt.seq (.call ν.pCeil [v Size, v PieceLen] NumPieces)
          (Light.Stmt.seq (.call ν.pBitLen [v Bound] Bits) et17Addr)))))

open Et17 in
/-- The third part: the residues, the classes, the chunks, and the loop over the instances. -/
def et17Tables (ν : Et17Nums) : Stmt :=
  (Light.Stmt.seq (.call ν.pDbl [v Free, v ThePrime, v Bits] _root_.Light.Sec3.Et17.Small)
    (Light.Stmt.seq (.call ν.pResidues [v AdrAB, v ResAB, v SizeSq, v Free, v Bits] _root_.Light.Sec3.Et17.Small)
      (Light.Stmt.seq (.call ν.pResidues [v AdrBC, v ResBC, v SizeSq, v Free, v Bits] _root_.Light.Sec3.Et17.Small)
        (Light.Stmt.seq (.call ν.pResidues [v AdrAC, v ResAC, v SizeSq, v Free, v Bits] _root_.Light.Sec3.Et17.Small)
          (Light.Stmt.seq (.call ν.pClasses [v ResAB, v Size, v ThePrime, v Cls, v Cur, v Rows, v Cols] _root_.Light.Sec3.Et17.Small)
            (Light.Stmt.seq (.call ν.pChunks [v Cls, v ThePrime, v Cap, v TabR, v TabL, v TabW] NumChunks)
              (Light.Stmt.seq (.set NumInst ((Light.Expr.op Light.Op.mul) (v NumPieces) (v NumChunks)))
                (.call ν.pLoop
                  [v Size, v ParD, v ThePrime, v PieceLen, v NumChunks, v NumInst, v AdrAB, v AdrBC, v AdrAC, v ResAC,
                    v ResBC, v Rows, v Cols, v TabR, v TabL, v TabW, v MatX, v MatY, v AdrOut, v SolverFree]
                  0))))))))

open Et17 in
/-- et17(n, U, ab, bc, ac, fr). -/
def et17Body (ν : Et17Nums) : Stmt :=
  (Light.Stmt.seq (et17Params ν)
    (.ite (Light.Cond.eq (v _root_.Light.Sec3.Et17.Small) (k 1)) (.call ν.pBrute [v Size, v Bound, v AdrAB, v AdrBC, v AdrAC, v Free] 0)
      (Light.Stmt.seq (et17Sizes ν) (et17Tables ν))))

/-! ## Time and need

The additive constants in the time functions are upper bounds for the cost of evaluating arguments,
of calls and of tests.  They are not meant to be tight. -/

/-- n is small for the parameters D and g: the host runs the brute force. -/
def SmallCase (n D g : ℕ) : Prop := D < 16 ∨ n < D ∨ g < 1 ∨ Nat.sqrt D < g

instance (n D g : ℕ) : Decidable (SmallCase n D g) := by unfold SmallCase; infer_instance

/-- The largest time of the solver on an instance with at most cap query pairs. -/
def supTime (Tn : List ℕ → ℕ) (n D cap : ℕ) : ℕ :=
  (Finset.range (cap + 1)).sup fun w => Tn [n, D, w]

/-- The largest need of the solver on an instance with at most cap query pairs. -/
def supNeed (need : List ℕ → Need) (n D cap : ℕ) : Need :=
  ⟨(Finset.range (cap + 1)).sup fun w => (need [n, D, w]).word,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).cells,
    (Finset.range (cap + 1)).sup fun w => (need [n, D, w]).depth⟩

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)" for the selected prime.
Here the second form, with the constant `Hashing.falsePositiveConst` and with κ = kappaOf n U =
max(1, log U / log n), so that U ≤ n^κ. -/
noncomputable def falsePositiveBound (n U D : ℕ) : ℕ :=
  ⌊Hashing.falsePositiveConst * (kappaOf n U * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D)⌋₊

/-- The time of the parameter procedures, of the square root and of the tests. -/
def hostSetup (tD tG : ℕ → ℕ) (n D : ℕ) : ℕ := tD n + tG D + (18 * Nat.sqrt D + 12) + 60

/-- A bound on the time of the loop over the instances: at most 4ng instances, with pieces of at
most q vertices and at most cap query pairs, and at most falsePositiveBound + 1 scans. -/
noncomputable def hostLoopBound (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  4 * n * g *
      (tWrites n D (pieceSizeNat D g) + supTime Tn n D (queryCapNat n D)
        + tAnswers (queryCapNat n D))
    + tScanCall (pieceSizeNat D g) * (falsePositiveBound n U D + 1) + 14

/-- The time of et17 after the tests, if n is not small. -/
noncomputable def hostMain (Tn : List ℕ → ℕ) (n U D g : ℕ) : ℕ :=
  chooseTime n U D + tQueryCapNat n D + tCeilDiv (Nat.sqrt D) g + tCeilDiv n (pieceSizeNat D g)
    + tBitLen U + tDblTable (bitLen U) + 3 * tResidues (n * n) (bitLen U) + tClasses n (Nat.sqrt D)
    + tChunks (Nat.sqrt D) (4 * n * g) + hostLoopBound Tn n U D g + 300

/-- **A bound on the time of the host in the worst case**, for the parameter functions Dfun, Gfun
with the times tD, tG, over a solver with the time Tn. -/
noncomputable def hostTime (Dfun Gfun tD tG : ℕ → ℕ) (Tn : List ℕ → ℕ) (n U : ℕ) : ℕ :=
  hostSetup tD tG n (Dfun n) +
    if SmallCase n (Dfun n) (Gfun (Dfun n)) then tBrute n + 20
    else hostMain Tn n U (Dfun n) (Gfun (Dfun n))

/-- The cells of the arrays of et17, with s in place of the prime. -/
def hostLayout (n U D : ℕ) : ℕ :=
  (bitLen U + 1) + 3 * (n * n) + (Nat.sqrt D + 1) + Nat.sqrt D + 2 * (n * n)
    + 3 * (n * n + Nat.sqrt D) + 2 * (n * D) + queryCapNat n D

/-- The largest number that et17 and the procedures below it form, apart from the solver; a and b
bound the numbers that the two parameter procedures form. -/
def hostWord (a b n U D g : ℕ) : ℕ :=
  a + b                                                     -- the two parameter procedures
    + (4 * D + 4)                                           -- the square root, the primes up to √D
    + (3 * U + 1)                                           -- a sum of three weights
    + (2 * U + 2)                                           -- the number of binary digits of U
    + (2 * n + 1)                                           -- the power of two above n
    + Nat.sqrt D * 2 ^ (bitLen U + 1)                       -- the table of doubles
    + 4 * (16 ^ Nat.clog 2 n * Nat.sqrt D)                  -- the entries in Strassen's algorithm
    + n * n * (16 ^ Nat.clog 2 n * Nat.sqrt D)              -- the count for a prime
    + (4 * n ^ 4 + D + 2)                                   -- cap
    + (Nat.sqrt D + g + 1)                                  -- the size of a piece
    + (n + pieceSizeNat D g + 1)                                -- the number of pieces
    + 4 * n * g                                             -- the number of instances
    + 100

/-- The need of the host for given parameters D and g. -/
def hostNeedAt (a b : ℕ) (need : List ℕ → Need) (n U D g : ℕ) : Need :=
  ⟨hostWord a b n U D g + (supNeed need n D (queryCapNat n D)).word,
    chooseCells n U D + hostLayout n U D + (supNeed need n D (queryCapNat n D)).cells + 2,
    2 * Nat.clog 2 n + 8 + (supNeed need n D (queryCapNat n D)).depth⟩

/-- **The need of the host**, over a solver with the need `need`; wD and wG bound the numbers that
the parameter procedures form. -/
def hostNeed (Dfun Gfun wD wG : ℕ → ℕ) (need : List ℕ → Need) (n U : ℕ) : Need :=
  hostNeedAt (wD n) (wG (Dfun n)) need n U (Dfun n) (Gfun (Dfun n))

/-! ## The context -/

/-- A procedure that computes a function of one number and changes no cell; t is its time, w bounds
the numbers it forms, and it nests calls at most three deep. -/
def ParamProc (P : Program) (p : ℕ) (f t w : ℕ → ℕ) : Prop :=
  ∀ (lim : Limits) (d x : ℕ) (μ : ℕ → ℤ), 1 ≤ x → (lim.space : ℤ) ≤ lim.word →
    ((w x : ℕ) : ℤ) ≤ lim.word → d + 4 ≤ lim.depth →
    Meets lim P p (d + 1) [(x : ℤ)] μ (t x) fun r μ' => r = (f x : ℕ) ∧ μ' = μ

/-- The context of et17: the solver and what hostLoop calls; the procedures of the host; the
two parameter procedures. -/
structure Et17Ctx (P₀ R : Program) (ν : Et17Nums) (Tn : List ℕ → ℕ) (need : List ℕ → Need)
    (Dfun Gfun tD tG wD wG : ℕ → ℕ) : Prop where
  loop : HostCtx P₀ R ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs ν.pScan Tn need
  hLoop : (P₀ ++ R)[ν.pLoop]? = some (hostLoopBody ν.pS ν.pWriteX ν.pWriteY ν.pScanPairs)
  hSqrt : (P₀ ++ R)[ν.pSqrt]? = some sqrtBody
  hBrute : (P₀ ++ R)[ν.pBrute]? = some (bruteBody ν.pScan)
  hChoose : (P₀ ++ R)[ν.pChoose]? = some (choosePrimeBody ν.ch)
  ch : ChCtx (P₀ ++ R) ν.ch
  hCap : (P₀ ++ R)[ν.pCap]? = some queryCapNatBody
  hCeil : (P₀ ++ R)[ν.pCeil]? = some ceilDivBody
  hBitLen : (P₀ ++ R)[ν.pBitLen]? = some bitLenBody
  hDbl : (P₀ ++ R)[ν.pDbl]? = some dblTableBody
  hResid : (P₀ ++ R)[ν.pResid]? = some residBody
  hResidues : (P₀ ++ R)[ν.pResidues]? = some (residuesBody ν.pResid)
  hClasses : (P₀ ++ R)[ν.pClasses]? = some classesBody
  hChunks : (P₀ ++ R)[ν.pChunks]? = some chunksBody
  dProc : ParamProc (P₀ ++ R) ν.pD Dfun tD wD
  gProc : ParamProc (P₀ ++ R) ν.pG Gfun tG wG
  D_pos : ∀ n, 1 ≤ n → 1 ≤ Dfun n

/-! ## The data, the addresses and the local variables of a run -/

/-- The data of the loop over the instances, for the parameters D and g. -/
def hostData (x : TriInst) (D g : ℕ) : HostData :=
  ⟨x.n, D, chosenPrime x.n D x.AB x.BC x.AC, pieceSizeNat D g, queryCapNat x.n D, x.AB, x.BC, x.AC⟩

/-- The address of the residues of `w(a,b)`; the table of doubles is at fr. -/
def aRab (_X : HostData) (U fr : ℕ) : ℕ := fr + (bitLen U + 1)
/-- The address of the residues of `w(b,c)`. -/
def aRbc (X : HostData) (U fr : ℕ) : ℕ := aRab X U fr + X.n * X.n
/-- The address of the residues of `w(a,c)`. -/
def aRac (X : HostData) (U fr : ℕ) : ℕ := aRbc X U fr + X.n * X.n
/-- The address of the starts of the classes. -/
def aCls (X : HostData) (U fr : ℕ) : ℕ := aRac X U fr + X.n * X.n
/-- The address of the running places. -/
def aCur (X : HostData) (U fr : ℕ) : ℕ := aCls X U fr + (X.p + 1)
/-- The address of the rows of the sorted pairs. -/
def aQi (X : HostData) (U fr : ℕ) : ℕ := aCur X U fr + X.p
/-- The address of the columns of the sorted pairs. -/
def aQj (X : HostData) (U fr : ℕ) : ℕ := aQi X U fr + X.n * X.n
/-- The address of the residues of the chunks. -/
def aCr (X : HostData) (U fr : ℕ) : ℕ := aQj X U fr + X.n * X.n
/-- The address of the starts of the chunks. -/
def aCl (X : HostData) (U fr : ℕ) : ℕ := aCr X U fr + (X.n * X.n + X.p)
/-- The address of the lengths of the chunks. -/
def aCw (X : HostData) (U fr : ℕ) : ℕ := aCl X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matX` of an instance. -/
def aX (X : HostData) (U fr : ℕ) : ℕ := aCw X U fr + (X.n * X.n + X.p)
/-- The address of the matrix `matY` of an instance. -/
def aY (X : HostData) (U fr : ℕ) : ℕ := aX X U fr + X.n * X.D
/-- The address of the answers. -/
def aOut (X : HostData) (U fr : ℕ) : ℕ := aY X U fr + X.n * X.D
/-- The free pointer that is handed to the solver. -/
def aFr (X : HostData) (U fr : ℕ) : ℕ := aOut X U fr + X.cap












/-- The addresses that hostLoop gets. -/
def hostAddr (x : TriInst) (X : HostData) (fr : ℕ) : HostAddr :=
  ⟨x.ab, x.bc, x.ac, aRac X x.U fr, aRbc X x.U fr, aQi X x.U fr, aQj X x.U fr, aCr X x.U fr,
    aCl X x.U fr, aCw X x.U fr, aX X x.U fr, aY X x.U fr, aOut X x.U fr, aFr X x.U fr⟩

/-- The locals at the start: the arguments, then zeros. -/
def et17Loc0 (x : TriInst) (fr : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The locals after the first part. -/
def et17LocA (x : TriInst) (fr D g : ℕ) : List ℤ :=
  [(x.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (D : ℤ), (g : ℤ),
    ((Nat.sqrt D : ℕ) : ℤ), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    (if SmallCase x.n D g then 1 else 0), 0]

/-- The locals of the third part, for the data X of the loop: those after the second part, with the
number of chunks in NumChunks and the result of the last call in Small.  ParG and RootD are not
read. -/
abbrev Et17.locals (x : TriInst) (X : HostData) (fr : ℕ) (g s nch res : ℤ) : List ℤ :=
  [(X.n : ℤ), (x.U : ℤ), (x.ab : ℤ), (x.bc : ℤ), (x.ac : ℤ), (fr : ℤ), (X.D : ℤ), g, s, (X.p : ℤ),
    (X.cap : ℤ), (X.q : ℤ), (X.h : ℤ), ((bitLen x.U : ℕ) : ℤ), ((X.n * X.n : ℕ) : ℤ), 0,
    ((aRab X x.U fr : ℕ) : ℤ), ((aRbc X x.U fr : ℕ) : ℤ), ((aRac X x.U fr : ℕ) : ℤ),
    ((aCls X x.U fr : ℕ) : ℤ), ((aCur X x.U fr : ℕ) : ℤ), ((aQi X x.U fr : ℕ) : ℤ),
    ((aQj X x.U fr : ℕ) : ℤ), ((aCr X x.U fr : ℕ) : ℤ), ((aCl X x.U fr : ℕ) : ℤ),
    ((aCw X x.U fr : ℕ) : ℤ), ((aX X x.U fr : ℕ) : ℤ), ((aY X x.U fr : ℕ) : ℤ),
    ((aOut X x.U fr : ℕ) : ℤ), ((aFr X x.U fr : ℕ) : ℤ), ((X.n * X.n + X.p : ℕ) : ℤ), nch, 0, res,
    ((X.n * X.D : ℕ) : ℤ)]

/-- The locals after the second part (n is not small, so the flag is 0). -/
def et17LocB (x : TriInst) (fr D g : ℕ) : List ℤ :=
  Et17.locals x (hostData x D g) fr g (Nat.sqrt D : ℕ) 0 0

/-- The time of the third part in a run: it depends on the data. -/
def hostRunTime (Tn : List ℕ → ℕ) (X : HostData) (U : ℕ) : ℕ :=
  tDblTable (bitLen U) + 3 * tResidues (X.n * X.n) (bitLen U) + tClasses X.n X.p
    + tChunks X.p X.chunkCount + tHostLoop Tn X + 80

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_Arrays


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: the arrays and the loop

The third part of the host procedure `et17` (Exact Triangle by Theorem 17) fills the table of
doubles and the three lists of residues (`resid_then`), sorts the pairs into classes and cuts the
classes into chunks (`classes_then`), and calls the loop over the instances.

`et17Tables_spec` is the specification of the whole part: within `hostRunTime` steps, local 0 holds
the bit `found m` of the loop over the instances, and the cells below the free pointer are
unchanged.  Three lemmas connect the calls to the loop: `ready_of` (a run of et17 provides what this
part needs), `hostMem_of` (the arrays that the loop reads are in the memory) and `hostLay_of` (they
lie where the loop expects them).
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec3

open ThreeSumApsp

namespace Et17





/-- What the third part needs, for the data X of the loop: the limits, the prime, and the three
matrices below the free pointer. -/
structure Ready (lim : Limits) (d : ℕ) (x : TriInst) (X : HostData) (μ : ℕ → ℤ) (fr : ℕ) :
    Prop where
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + 2 ≤ lim.depth
  prime : 1 ≤ X.p
  word : ((X.p * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  top : aFr X x.U fr < lim.space
  segAB : Seg μ x.ab X.AB
  segBC : Seg μ x.bc X.BC
  segAC : Seg μ x.ac X.AC
  lenAB : X.AB.length = X.n * X.n
  lenBC : X.BC.length = X.n * X.n
  lenAC : X.AC.length = X.n * X.n
  leAB : AbsLe X.AB x.U
  leBC : AbsLe X.BC x.U
  leAC : AbsLe X.AC x.U
  belowAB : x.ab + X.n * X.n ≤ fr
  belowBC : x.bc + X.n * X.n ≤ fr
  belowAC : x.ac + X.n * X.n ≤ fr

variable {lim : Limits} {P : Program} {d : ℕ} {x : TriInst} {X : HostData} {μ : ℕ → ℤ} {fr : ℕ}























/-- The memory after the first four calls: the three lists of residues; only cells between the free
pointer and the array of the classes have changed. -/
structure ResidMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  rab : SegN μ' (aRab X x.U fr) X.RAB
  rbc : SegN μ' (aRbc X x.U fr) X.RBC
  rac : SegN μ' (aRac X x.U fr) X.RAC
  same : SameOn (fun c => c < fr ∨ aCls X x.U fr ≤ c) μ μ'

/-- The memory after the next two calls: the pairs, class after class, and the table of the chunks;
only cells between the array of the classes and aX, the first matrix of the instance that is handed
to the solver, have changed. -/
structure ClassMem (x : TriInst) (X : HostData) (fr : ℕ) (μ μ' : ℕ → ℤ) : Prop where
  qi : SegN μ' (aQi X x.U fr) X.QI
  qj : SegN μ' (aQj X x.U fr) X.QJ
  cr : SegN μ' (aCr X x.U fr) (X.CT.map fun c => c.residue)
  cl : SegN μ' (aCl X x.U fr) (X.CT.map fun c => c.start)
  cw : SegN μ' (aCw X x.U fr) (X.CT.map fun c => c.len)
  same : SameOn (fun c => c < aCls X x.U fr ∨ aX X x.U fr ≤ c) μ μ'




































































































































































































end Et17














































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_PrimeStage


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: the prime, the sizes, the addresses

This file proves the specification of the second part of the host procedure `et17` (Exact Triangle
by Theorem 17), which chooses the prime and computes the sizes and the addresses of the arrays:
five calls (`et17Sizes_spec`) and then seventeen assignments (`et17Addr_spec`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}







































/-- What the second part uses: the parameters are not small, and the limits allow for one more
level of calls, for the arrays and for the numbers that the four small procedures form. -/
structure SizesReady (lim : Limits) (d : ℕ) (x : TriInst) (fr D g : ℕ) : Prop where
  one_le_D : 1 ≤ D
  one_le_g : 1 ≤ g
  one_le_piece : 1 ≤ pieceSizeNat D g
  depth : d < lim.depth
  top : aFr (hostData x D g) x.U fr ≤ lim.space
  wordCap : ((4 * x.n ^ 4 + D + 2 : ℕ) : ℤ) ≤ lim.word
  wordPiece : ((Nat.sqrt D + g + 1 : ℕ) : ℤ) ≤ lim.word
  wordPieces : ((x.n + pieceSizeNat D g + 1 : ℕ) : ℤ) ≤ lim.word
  wordBits : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word





















































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_Host_Program


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The host of Theorem 17: the program, assembled

The procedures of the host are appended to a program `P₀` that already holds a solver of
Lop-AE-SparseTri and the two procedures that compute the parameters `D` and `g`.  This file has the
list of the procedures (`et17Procs`), their numbers (`et17NumsAt`), the proof that the program so
obtained is the context that the top procedure assumes (`et17Ctx_assembled`), and the
result: the host solves Exact Triangle (`et17_solves`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The numbers of the procedures of Strassen's algorithm, if the list of the procedures of the host
starts at the number `o`. -/
def strNumsAt (o : ℕ) : StrNums := ⟨o + 12, o + 13, o + 14, o + 15, o + 16⟩

/-- The numbers of the procedures that countPrime calls. -/
def cpNumsAt (o : ℕ) : CpNums := ⟨o + 5, o + 6, o + 7, o + 8, o + 9, o + 10, o + 11, strNumsAt o⟩

/-- The numbers of the procedures that choosePrime calls. -/
def chNumsAt (o : ℕ) : ChNums := ⟨o + 3, o + 4, o + 17, cpNumsAt o, o, o + 28⟩

/-- The numbers of the procedures that the top procedure calls: `pS` is the solver, `pD` and `pG`
compute the parameters. -/
def et17NumsAt (pS pD pG o : ℕ) : Et17Nums where
  pD := pD
  pG := pG
  pSqrt := o
  pBrute := o + 2
  pScan := o + 1
  pChoose := o + 18
  pCap := o + 19
  pCeil := o + 20
  pBitLen := o + 4
  pDbl := o + 5
  pResid := o + 6
  pResidues := o + 7
  pClasses := o + 21
  pChunks := o + 22
  pLoop := o + 26
  pS := pS
  pWriteX := o + 23
  pWriteY := o + 24
  pScanPairs := o + 25
  ch := chNumsAt o

/-- The procedures of the host: procedure number `i` of this list gets the number `o + i`.  The top
procedure has the number `o + 27`; behind it stands the sieve of Eratosthenes, which `primes`
calls. -/
def et17Procs (pS pD pG o : ℕ) : Program :=
  let ν := et17NumsAt pS pD pG o
  [sqrtBody,                                                -- 0
    scanBody,                                               -- 1
    bruteBody ν.pScan,                                      -- 2
    primesBody ν.ch.pSqrt ν.ch.pSieve,                      -- 3
    bitLenBody,                                             -- 4
    dblTableBody,                                           -- 5
    residBody,                                              -- 6
    residuesBody ν.pResid,                                  -- 7
    spreadTableBody,                                        -- 8
    szTableBody,                                            -- 9
    buildZBody,                                             -- 10
    countZeroBody,                                          -- 11
    vlinBody,                                               -- 12
    cconvBody,                                              -- 13
    fillBody,                                               -- 14
    phaseBody ν.ch.cp.str,                                  -- 15
    strBody ν.ch.cp.str,                                    -- 16
    countPrimeBody ν.ch.cp,                                 -- 17
    choosePrimeBody ν.ch,                                   -- 18
    queryCapNatBody,                                              -- 19
    ceilDivBody,                                            -- 20
    classesBody,                                            -- 21
    chunksBody,                                             -- 22
    writeXBody,                                             -- 23
    writeYBody,                                             -- 24
    scanPairsBody ν.pScan,                                  -- 25
    hostLoopBody pS ν.pWriteX ν.pWriteY ν.pScanPairs,       -- 26
    et17Body ν,                                             -- 27
    sieveBody]                                              -- 28

variable {P₀ : Program} {pS pD pG : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
  {Dfun Gfun tD tG wD wG : ℕ → ℕ}


















































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_TimeBound_Terms


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 17: the time of each routine, up to a constant

The running time of the reduction of Theorem 17 is a sum of the time functions of its routines.  The
theorem bounds the additional time by "O(ν n³ log n/g + n^{ω+o(1)} D^{3/2} + n² D g)", where ν is
the exponent in `|w(e)| ≤ n^ν`; it is `κ` below.  The form for programs, `Claim.Theorem_17`, has,
here, Strassen's exponent `log₂ 7` in the second term.  This file bounds each
routine by a monomial in `n`, `√D` and `κ log n`, uniformly in `n`, `D`, `g`, `U` and `κ` under the
hypotheses of the theorem, and says which monomials are within which of the three terms.  No
constant is computed.

* `Steps t B` says that the number `t` of steps is `O(B)`, uniformly in the parameters.  Such bounds
  can be added and multiplied, and they absorb constant factors.
* Every time function is a polynomial in a few quantities, and each of these is at most a monomial
  `mon a b c = n^a (√D)^b (κ log n)^c`: `⌊√D⌋`, `g` and the size `⌈s/g⌉` of a piece are at most
  `√D`; `2^⌈log₂ n⌉ ≤ 2n`; the number of binary digits of `U ≤ n^κ` is `O(κ log n)` (section "The
  basic quantities").  So a routine takes `O(mon a b c)` steps (`StepsMon t a b c`), and the
  exponents are read off its time function, in the calculus `Scale.SoftO` on the scale `costScale`.
* All three bases are at least 1.  So a monomial is within the first term if its exponents are at
  most `(2, 1, 1)`, within the second if they are at most `(2, 3, 0)`, within the third if they are
  at most `(2, 2, 0)` (`Scale.SoftO.withinScans`, `Scale.SoftO.withinPrime`,
  `Scale.SoftO.withinBuild`).
* The choice of the prime runs through at most `√D` primes (`steps_chooseTime`).  The product of the
  two matrices is within the second term, as in the paper: Strassen's recursion makes
  `7^⌈log₂ n⌉ = O(n^{log₂ 7})` products of polynomials of degree below `p ≤ √D`
  (`steps_sqrt_mul_strSteps`).  The residues of the weights, computed bit by bit for each prime,
  take `O(√D n² κ log n)` steps, which is within the first term.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The hypotheses -/

/-- The parameters of Theorem 17 as one record, so that a bound up to a constant can be stated
uniformly in all of them. -/
structure CostParams where
  /-- The number of vertices per part. -/
  n : ℕ
  /-- The parameter `D` of the reduction. -/
  D : ℕ
  /-- The parameter `g` of the reduction. -/
  g : ℕ
  /-- The bound on the absolute values of the weights. -/
  U : ℕ
  /-- The exponent in `U ≤ n^κ`. -/
  κ : ℝ

/-- The hypotheses of Theorem 17, with the bound `U` on the weights.  The claim for
programs adds `κ ≥ 1`, as in Theorem 19. -/
structure CostParams.Hyp (θ : CostParams) : Prop where
  /-- `D ≥ 16`. -/
  hD16 : 16 ≤ θ.D
  /-- `D ≤ n`. -/
  hDn : θ.D ≤ θ.n
  /-- `g ≥ 1`. -/
  hg : 1 ≤ θ.g
  /-- `g ≤ √D`. -/
  hgD : (θ.g : ℝ) ≤ Real.sqrt θ.D
  /-- `κ ≥ 1`. -/
  hκ : 1 ≤ θ.κ
  /-- The weights are at most `n^κ` in absolute value. -/
  hUn : (θ.U : ℝ) ≤ (θ.n : ℝ) ^ θ.κ

namespace CostParams.Hyp

variable {θ : CostParams} (h : θ.Hyp)
include h




/-- `n ≥ 16`. -/
theorem sixteen_le_n : 16 ≤ θ.n := h.hD16.trans h.hDn

/-- `n ≥ 1`, as a natural number. -/
theorem one_le_n_nat : 1 ≤ θ.n := (by norm_num : 1 ≤ 16).trans h.sixteen_le_n

/-- `n ≥ 1`. -/
theorem one_le_n : (1 : ℝ) ≤ θ.n := Nat.one_le_cast.2 h.one_le_n_nat

/-- `g ≥ 1`. -/
theorem one_le_g : (1 : ℝ) ≤ θ.g := Nat.one_le_cast.2 h.hg




/-- `√D ≥ g ≥ 1`. -/
theorem one_le_sqrt : 1 ≤ Real.sqrt θ.D := h.one_le_g.trans h.hgD




/-- `log n ≥ 1`, because `n ≥ 16`. -/
theorem one_le_log : 1 ≤ Real.log θ.n :=
  Real.one_le_log_natCast_of_three_le ((by norm_num : 3 ≤ 16).trans h.sixteen_le_n)

/-- `κ log n ≥ 1`. -/
theorem one_le_κ_mul_log : 1 ≤ θ.κ * Real.log θ.n :=
  one_le_mul_of_one_le_of_one_le h.hκ h.one_le_log













end CostParams.Hyp

/-! ## Numbers of steps up to a constant -/

/-- The number `t` of steps is `O(B)`, uniformly in the parameters, under the hypotheses of
Theorem 17. -/
def Steps (t : CostParams → ℕ) (B : CostParams → ℝ) : Prop :=
  Dominated CostParams.Hyp (fun θ => (t θ : ℝ)) B

namespace Steps

variable {t t₁ t₂ : CostParams → ℕ} {B B₁ B₂ : CostParams → ℝ}



























end Steps

/-! ## Monomials -/

/-- The scale of Theorem 17: monomials in `n`, `√D` and `κ log n`, under the hypotheses of the
theorem. -/
noncomputable def costScale : Scale CostParams (Fin 3) :=
  .ofBases CostParams.Hyp ![fun θ => θ.n, fun θ => Real.sqrt θ.D, fun θ => θ.κ * Real.log θ.n]
    fun i θ h => by
      fin_cases i
      exacts [h.one_le_n, h.one_le_sqrt, h.one_le_κ_mul_log]

/-- The monomial `n^a (√D)^b (κ log n)^c`. -/
noncomputable abbrev mon (a b c : ℕ) : CostParams → ℝ := costScale.mon ![a, b, c]





/-- The number `t` of steps is `O(n^a (√D)^b (κ log n)^c)`. -/
abbrev StepsMon (t : CostParams → ℕ) (a b c : ℕ) : Prop := costScale.SoftO t ![a, b, c]






/-! ## The basic quantities -/






























































/-! ## The routines -/














































































/-! ## The three terms of the bound dominate the monomials -/




































/-- The sum of the three terms of the bound of Theorem 17. -/
noncomputable def budget (θ : CostParams) : ℝ :=
  termScans θ.n θ.g θ.κ + termPrime strassen θ.n θ.D + termBuild θ.n θ.D θ.g






































section within

variable {t : CostParams → ℕ} {e : Fin 3 → ℕ}



















end within

namespace Steps

variable {t₁ t₂ m : CostParams → ℕ} {B : CostParams → ℝ}






end Steps

/-! ## The choice of the prime -/







































































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem17_TimeBound_Total


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The time of the host of Theorem 17 obeys the bound of Theorem 17

Theorem 17 reduces Exact Triangle to at most `4ng` instances "plus O(ν n³ log n/g + n^{ω+o(1)}
D^{3/2} + n² D g) additional time".  The form for programs, `Claim.Theorem_17`, has, here,
Strassen's exponent in the second term; its right side is `bound17`.  The time
function of the host is the time of `4ng` calls of the solver plus a rest, its time over a solver
that takes no time (`hostTime_eq`), and the rest is bounded term by term, up to a constant.

* The parameters, the choice of the prime, the residues, the classes and the chunks are within the
  three terms of the bound (`steps_hostSetup`, `steps_chooseTime`, `steps_tResidues`,
  `steps_tClasses`, `steps_tChunks`).
* Writing the matrices of the instances takes `O(ng) · O(nD)` steps, the third term
  (`steps_instances_mul_tWrites`).
* Reading the answers takes a constant number of steps for each of the at most `n²/√D` query pairs
  of an instance (`steps_tAnswers`).  This is the term `C n²/√D` beside the time of the solver.
* There are at most `F(p) + 1 = O(κ n³ log n/√D)` scans, where `F(p)` is the number of false
  positives of the chosen prime, of `O(√D/g)` steps each: the first term
  (`steps_falsePositiveBound`, `steps_tScanCall`, `steps_scans`).

The sum is `steps_hostRest`, and `obeysBound17_hostTime` puts it into the form of `bound17`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The scans -/























































/-! ## What is done for each instance -/





























/-! ## The sum -/

/-- The time of the host without the calls of the solver: its time over a solver that takes no time.
-/
 noncomputable def hostRest (tD tG : ℕ → ℕ) (θ : CostParams) : ℕ :=
  hostSetup tD tG θ.n θ.D + hostMain (fun _ => 0) θ.n θ.U θ.D θ.g
























/-- What bounds the time of the host without the calls of the solver: `ng · n²/√D`, for reading the
answers of the instances, plus the three terms of the bound of Theorem 17. -/
 noncomputable def restBound (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ



















































































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem19_ChooseBySize


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-- choose(n, U, ab, bc, ac, fr): calls procedure p₁ if n < n₀, and procedure p₂ if not, on the same
arguments: the number n of vertices in a part, the bound U on the weights, the addresses ab, bc, ac
of the three matrices of weights, and the free pointer fr. -/
def bySizeBody (n₀ p₁ p₂ : ℕ) : Stmt :=
  .ite ((Light.Cond.lt (v 0) (k n₀))) (.call p₁ [v 0, v 1, v 2, v 3, v 4, v 5] 0)
    (.call p₂ [v 0, v 1, v 2, v 3, v 4, v 5] 0)

/-- The number of steps of choose. -/
def bySizeTime (n₀ : ℕ) (T₁ T₂ : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := (if n < n₀ then T₁ n U else T₂ n U) +
    12

/-- What choose needs: a word for the threshold, one more level of calls, and what the two solvers
need. -/
def bySizeNeed (n₀ : ℕ) (r₁ r₂ : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨n₀ + (r₁ n U).word + (r₂ n U).word, (r₁ n U).cells + (r₂ n U).cells, 1 + (r₁ n U).depth +
    (r₂ n U).depth⟩

namespace ChooseHost












































end ChooseHost

open ChooseHost




















end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21a_ChanHe_Contracts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.ChanHe
end ThreeSumApsp.ChanHe


/-!
# The reduction from 3SUM to Convolution-3SUM after Chan and He, as a program.  Specifications

Theorem 21(a), after [CH20, Theorem 5.1].  This file contains no program
and no proof.  It states the specifications of the routines of the reduction: the general library,
the routines below the recursion tree, the tree, and the routines that prepare the splittings.  The
proof of a routine uses only the specifications of the routines that it calls.

* The pure models are the definitions of the reduction themselves (`ChanHe.coll`, `heavy`,
  `modulus`, `Node.oneArray`, `nodes`, …), applied to finite sets.  A set lies in the memory as a
  list without repetitions, in any order, with its length passed beside its address (`SetAt`).
* The specification of a routine is a proposition `XSpec lim P p …`: "procedure number `p` of the
  program `P`, run on these arguments in a memory that satisfies this, ends within `tX` steps with
  this result in a memory that satisfies that" (`Meets`).  It is proved for every program that holds
  the body of X at the number `p` and meets the specifications of the routines that X calls.
* The last argument of most routines is the free pointer `fr`; such a routine writes only its output
  segments, the count table (which it leaves as it found it), and cells from `fr` on.
* The count table: `cap` cells from `cnt`, below every free pointer, all zeros between calls
  (`ZeroAt`).  A routine that uses it clears what it wrote.
* Time functions are definitions.  The time function of a caller is written in terms of those of its
  callees.
* Limits: one hypothesis `(xNeed …).Ok lim fr d`, or a field of the structure that collects the
  hypotheses of the routine.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-! ## Vocabulary -/








/-! ## Time functions and needs -/











































/-! ## The generic library

The logarithms, the remainder, the sieve and sorting of the general library meet these
specifications (`EmodSpec` is below). -/








































/-! ## Remainders, counts, collisions, heavy elements -/






























































/-! ## The modulus of a node -/





/-- A set in the memory: the address and the length of its list, and the set. -/
structure Slot : Type where
  (addr len : ℕ)
  set : Finset ℤ

/-- What the routines below the recursion tree share: the free pointer `fr`; the bounds `n` on the
sizes of the sets and `V` on their elements; the bound `m` on the primes, their number `np` and the
address `pr` of their list; the address `cnt` of the count table of `m²` cells. -/
structure Env : Type where
  (fr n V m np pr cnt : ℕ)


















/-- A node of the recursion tree in the memory: its three sets, and what the routines share. -/
structure NodeArgs : Type extends Env where
  (X₁ X₂ X₃ : Slot)












/-- The arguments of search: a node, the factor `mult` of the moduli, and a bound for each set. -/
structure SearchArgs : Type extends NodeArgs where
  (mult b₁ b₂ b₃ : ℕ)





/-- A candidate `q` is good: each of the three sets has at most `bᵢ / np` colliding pairs modulo
`mult · q`. -/
def SearchArgs.Good (x : SearchArgs) (q : ℕ) : Prop :=
  coll x.X₁.set (x.mult * q) * x.np ≤ x.b₁ ∧ coll x.X₂.set (x.mult * q) * x.np ≤ x.b₂ ∧
    coll x.X₃.set (x.mult * q) * x.np ≤ x.b₃

instance (x : SearchArgs) : DecidablePred x.Good := fun q => by
  unfold SearchArgs.Good
  infer_instance
























/-! ## The array of a node -/






















/-! ## The recursion tree -/







































































/-! ## The front: distinct values, multiplicities, binary digits, the splittings -/


































































































































end Light.Sec3.ChanHe

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_Apsp_Passes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# APSP by repeated squaring: the three passes over the matrix

For Theorem 21(b).  The host for APSP keeps the current matrix as a list of
`n²` integers, in which a large number `INF` stands for `+∞`.  This file has its three simple
passes, each with its specification (`clip_meets`, `apInit_meets`, `apOut_meets`).

* clip(len, thr, INF, src, dst) copies `len` cells from `src` to `dst` and replaces every number
  above `thr` by `INF`.
* apInit(n, INF, adj, w, A) writes the weight matrix of the graph to `A`: 0 on the diagonal, the
  weight where there is an edge, `INF` elsewhere.
* apOut(len, INF, A, out) writes two cells for each cell of `A`: (0, 0) for `INF`, and (1, x) for
  any other number `x`.

In each proof the memory after j rounds is written down (`wrote`, `zeroedDiag`), one lemma says what
a round does to the state, and the loop rule does the rest.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## clip -/

namespace Clip

/-- The number of cells. -/
abbrev Len : ℕ := 0
/-- The threshold. -/
abbrev Thresh : ℕ := 1
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 2
/-- The address of the source. -/
abbrev Src : ℕ := 3
/-- The address of the destination. -/
abbrev Dst : ℕ := 4
/-- The counter q. -/
abbrev Idx : ℕ := 5

end Clip

open Clip in
/-- clip(len, thr, INF, src, dst): for q < len, dst[q] := INF if src[q] > thr, and src[q]
otherwise. -/
def clipBody : Stmt :=
  .for Idx (v Len) (
    .ite ((Light.Cond.lt (v Thresh) (M ((Light.Expr.op Light.Op.add) (v Src) (v Idx)))))
      (.store (((Light.Expr.op Light.Op.add) (v Dst) (v Idx))) (v Big))
      (.store (((Light.Expr.op Light.Op.add) (v Dst) (v Idx))) (M (((Light.Expr.op Light.Op.add) (v Src) (v Idx))))))




































/-! ## apInit -/

namespace ApInit

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The address of A. -/
abbrev Mat : ℕ := 4
/-- The counter of both passes. -/
abbrev Idx : ℕ := 5
/-- n², in the first pass. -/
abbrev Cells : ℕ := 6
/-- The address of the diagonal cell, in the second pass. -/
abbrev Diag : ℕ := 6

end ApInit

open ApInit in
/-- The round of the first pass: A[q] := w[q] if adj[q] = 1, and INF otherwise. -/
def apInitFill : Stmt :=
  .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v AdjAt) (v Idx))) (k 1))) (.store (((Light.Expr.op Light.Op.add) (v Mat) (v Idx))) (M (((Light.Expr.op Light.Op.add) (v WtsAt) (v Idx)))))
    (.store (((Light.Expr.op Light.Op.add) (v Mat) (v Idx))) (v Big))

open ApInit in
/-- The round of the second pass: the diagonal cell becomes 0; the next one is n + 1 cells on. -/
def apInitDiag : Stmt := (Light.Stmt.seq (.store (v Diag) (k 0))
                           (.set Diag ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Diag) (v Verts)) (k 1))))

open ApInit in
/-- apInit(n, INF, adj, w, A): the first pass fills the n² cells of A, the second pass puts 0 on the
diagonal. -/
def apInitBody : Stmt :=
  (Light.Stmt.seq (.set Cells ((Light.Expr.op Light.Op.mul) (v Verts) (v Verts)))
    (Light.Stmt.seq (.for Idx (v Cells) apInitFill) (Light.Stmt.seq (.set Diag (v Mat)) (.for Idx (v Verts) apInitDiag))))

/-- The entry number q of the weight matrix, the diagonal apart. -/
def apInitCell (INF : ℤ) (ADJ W : List ℤ) (q : ℕ) : ℤ :=
  if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The memory μ after the first j diagonal cells of the matrix at A have become 0. -/
def zeroedDiag (μ : ℕ → ℤ) (A n j : ℕ) : ℕ → ℤ :=
  fun a => if ∃ i < j, a = A + i * (n + 1) then 0 else μ a








































/-- The invariant of the second pass of apInit before round j; μ is the memory after the first
pass. -/
def ApInitInv (μ : ℕ → ℤ) (n adj w A : ℕ) (INF : ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [n, INF, adj, w, A, j, (A + j * (n + 1) : ℕ)], zeroedDiag μ A n j⟩




























































































/-! ## apOut -/

namespace ApOut

/-- The number of cells of A. -/
abbrev Len : ℕ := 0
/-- The number that stands for +∞. -/
abbrev Big : ℕ := 1
/-- The address of A. -/
abbrev Mat : ℕ := 2
/-- The address of the output. -/
abbrev Out : ℕ := 3
/-- The counter q. -/
abbrev Idx : ℕ := 4
/-- The address out + 2q. -/
abbrev Pos : ℕ := 5

end ApOut

open ApOut in
/-- The two cells of the output for the cell A[q]. -/
def apOutWrite : Stmt :=
  .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v Mat) (v Idx))) (v Big)))
    ((Light.Stmt.seq (.store (v Pos) (k 0)) (.store ((Light.Expr.op Light.Op.add) (v Pos) (k 1)) (k 0))))
    ((Light.Stmt.seq (.store (v Pos) (k 1))
       (.store ((Light.Expr.op Light.Op.add) (v Pos) (k 1)) (M ((Light.Expr.op Light.Op.add) (v Mat) (v Idx))))))

open ApOut in
/-- The round of apOut for the cell A[q]. -/
def apOutRound : Stmt := (Light.Stmt.seq apOutWrite (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 2))))

open ApOut in
/-- apOut(len, INF, A, out): for q < len, the cells out[2q], out[2q + 1] become 0, 0 if A[q] = INF,
and 1, A[q] otherwise. -/
def apOutBody : Stmt := (Light.Stmt.seq (.set Pos (v Out)) (.for Idx (v Len) apOutRound))

/-- Cell number c of the output: cells 2q and 2q + 1 are 0, 0 if L[q] = INF, and 1, L[q]
otherwise. -/
def apOutCell (INF : ℤ) (L : List ℤ) (c : ℕ) : ℤ :=
  if L.getD (c / 2) 0 = INF then 0 else if c % 2 = 0 then 1 else L.getD (c / 2) 0















/-- The invariant of the loop of apOut before round j. -/
def ApOutInv (μ : ℕ → ℤ) (A out : ℕ) (INF : ℤ) (L : List ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩












































/-- What apOut leaves from the address `out` on: for each number of the list `L` a pair of cells.
Its first cell holds 0 if the number is `INF`; otherwise the pair holds 1 and the number. -/
def PairsAt (μ' : ℕ → ℤ) (out : ℕ) (INF : ℤ) (L : List ℤ) : Prop :=
  ∀ i (hi : i < L.length), (L[i] = INF → μ' (out + 2 * i) = 0) ∧
    (L[i] ≠ INF → μ' (out + 2 * i) = 1 ∧ μ' (out + 2 * i + 1) = L[i])




































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_Apsp_Host


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# APSP from the (min,+)-product

For Theorem 21(b): if no closed walk has negative weight, then squaring the weight matrix ⌈log₂ n⌉
times in the (min,+)-product yields the distance matrix, and all finite entries that occur have
absolute value at most nU, where U bounds the edge weights.  The host below does this over an
arbitrary solver of the (min,+)-product.

ap(n, U, adj, w, out, fr) keeps the current matrix in the `n²` cells from `fr`, with `3nU` for `+∞`;
the product is written to the next `n²` cells, and the solver gets the free pointer `fr + 2n²`.
After each product the entries above `nU` are set back to `3nU` while the matrix is copied back.
The rounds are counted by doubling a number that starts at 1, as long as it is below `n`: these are
`⌈log₂ n⌉` rounds.

The proof follows the text: one round squares the matrix (`ApspHost.round_spec`), the last call
writes the answer (`ApspHost.out_spec`, `ApspHost.answer_correct`), and `ap_spec` puts the parts
together.  The result is `isHost_ap : IsHost mpTask apTask apTime apNeed`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace ApspHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the weights. -/
abbrev Bound : ℕ := 1
/-- The address of the adjacency matrix. -/
abbrev AdjAt : ℕ := 2
/-- The address of the weights. -/
abbrev WtsAt : ℕ := 3
/-- The address of the answer. -/
abbrev Out : ℕ := 4
/-- The free pointer, where the current matrix is kept. -/
abbrev Free : ℕ := 5
/-- n². -/
abbrev Cells : ℕ := 6
/-- nU. -/
abbrev Thresh : ℕ := 7
/-- 3nU, which stands for +∞. -/
abbrev Big : ℕ := 8
/-- fr + n², where the product is written. -/
abbrev ProdAt : ℕ := 10
/-- fr + 2n², the free pointer of the solver. -/
abbrev SolverFree : ℕ := 11
/-- The power of two that counts the rounds. -/
abbrev Power : ℕ := 12
/-- Takes the results of the calls. -/
abbrev Res : ℕ := 13

end ApspHost

open ApspHost in
/-- One round: the product of the matrix with itself, clipped and copied back. -/
def apRound (pMP pClip : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pMP [v Verts, v Big, v Free, v Free, v ProdAt, v SolverFree] Res)
    (Light.Stmt.seq (.call pClip [v Cells, v Thresh, v Big, v ProdAt, v Free] Res)
      (.set Power ((Light.Expr.op Light.Op.add) (v Power) (v Power)))))

open ApspHost in
/-- ap(n, U, adj, w, out, fr), over the procedures number pMP (a solver of the (min,+)-product),
pInit, pClip and pOut (the three passes). -/
def apBody (pMP pInit pClip pOut : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Cells ((Light.Expr.op Light.Op.mul) (v Verts) (v Verts)))
    (Light.Stmt.seq (.set Thresh ((Light.Expr.op Light.Op.mul) (v Verts) (v Bound)))
      (Light.Stmt.seq (.set Big ((Light.Expr.op Light.Op.mul) (k 3) (v Thresh)))
        (Light.Stmt.seq (.set ProdAt ((Light.Expr.op Light.Op.add) (v Free) (v Cells)))
          (Light.Stmt.seq (.set SolverFree ((Light.Expr.op Light.Op.add) (v ProdAt) (v Cells)))
            (Light.Stmt.seq (.call pInit [v Verts, v Big, v AdjAt, v WtsAt, v Free] Res)
              (Light.Stmt.seq (.set Power (k 1))
                (Light.Stmt.seq (.while (Light.Cond.lt (v Power) (v Verts)) (apRound pMP pClip))
                  (.call pOut [v Cells, v Big, v Free, v Out] Res)))))))))

/-- The time of the host, given the time of the solver: `⌈log₂ n⌉` products at the bound `3nU`, and
`O(n²)` steps for each product and at both ends. -/
def apTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  Nat.clog 2 n * (T n (3 * (n * U)) + 23 * (n * n) + 29) + 53 * (n * n) + 17 * n + 65

/-- The need of the host, given the need of the solver. -/
def apNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := max (r n (3 * (n * U))).word (3 * (n * U))
  cells := 2 * (n * n) + (r n (3 * (n * U))).cells
  depth := (r n (3 * (n * U))).depth + 1

namespace ApspHost

/-- The locals of the host during the loop; pw is the power of two that counts the rounds, res the
result of the last call.  Local 9 is not used and stays 0. -/
abbrev locals (x : GraphInst) (fr : ℕ) (pw res : ℤ) : List ℤ :=
  [x.n, x.U, x.adj, x.w, x.out, fr, (x.n * x.n : ℕ), (x.n * x.U : ℕ), 3 * (x.n * x.U : ℕ), 0,
    (fr + x.n * x.n : ℕ), (fr + 2 * (x.n * x.n) : ℕ), pw, res]

/-- The invariant of the loop before round t: the matrix after t squarings stands at the free
pointer, and nothing below it has changed. -/
def Inv (x : GraphInst) (μ : ℕ → ℤ) (fr t : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals x fr (2 ^ t : ℕ) res), μ'⟩ ∧
    Seg μ' fr (squareList x.n x.U x.ADJ x.W t) ∧ Kept μ μ' fr

/-- The program has the solver and the three passes, the instance is as the task prescribes, and the
limits allow for the need of the host. -/
structure Ctx (P₀ R₀ : Program) (pMP pInit pClip pOut : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves mpTask P₀ pMP T r
  init : (P₀ ++ R₀)[pInit]? = some apInitBody
  clip : (P₀ ++ R₀)[pClip]? = some clipBody
  out : (P₀ ++ R₀)[pOut]? = some apOutBody
  pre : x.Pre μ fr
  ok : (apNeed r x.n x.U).Ok lim fr d

variable {P₀ R₀ : Program} {pMP pInit pClip pOut : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : GraphInst} {μ : ℕ → ℤ} {fr : ℕ}































































































end ApspHost





























































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_CopyBlock


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Copying a block of a matrix

A routine for the hosts of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
subCopy(s, h, src, r0, c0, dst) copies the h × h block with upper left corner (r0,
c0) of the s × s matrix at src (row major) to dst (row major), one row at a time, with the routine
copy.  The destination lies behind the matrix.

The specification is subCopy_meets: afterwards the list subMat s h r0 c0 L stands at dst, and no
other cell has changed.  The proof is a loop over the rows with the invariant SubCopy.Inv; that
row i of the block is a piece of row r0 + i of the matrix is SubCopy.row_eq.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace SubCopy

/-- The local variables of subCopy: the arguments s (Side), h (Block), src, r0, c0, dst; the row i;
and the result of copy, which is not used. -/
abbrev Side : ℕ := 0
@[inherit_doc Side] abbrev Block : ℕ := 1
@[inherit_doc Side] abbrev Source : ℕ := 2
@[inherit_doc Side] abbrev Row0 : ℕ := 3
@[inherit_doc Side] abbrev Col0 : ℕ := 4
@[inherit_doc Side] abbrev Dest : ℕ := 5
@[inherit_doc Side] abbrev Row : ℕ := 6
@[inherit_doc Side] abbrev Unused : ℕ := 7

end SubCopy

open SubCopy in
/-- subCopy(s, h, src, r0, c0, dst): for i < h, copy the h cells from src + (r0 + i) s + c0 to
dst + i h.  pCopy is the number of the procedure copy. -/
def subCopyBody (pCopy : ℕ) : Stmt :=
  .for Row (v Block) (
    .call pCopy [((Light.Expr.op Light.Op.add)
                   ((Light.Expr.op Light.Op.add) (v Source)
                     ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v Row0) (v Row)) (v Side)))
                   (v Col0)), ((Light.Expr.op Light.Op.add) (v Dest) ((Light.Expr.op Light.Op.mul) (v Row) (v Block))),
      v Block] Unused)

/-- The number of steps of subCopy. -/
def subCopyTime (h : ℕ) : ℕ := h * (16 * h + 31) + 6

/-! ## The specification -/

namespace SubCopy











/-- The state before row i is copied: the first i rows of the block B stand at dst, and no cell
outside the h² cells from dst has changed. -/
def Inv (μ : ℕ → ℤ) (s h src r0 c0 dst : ℕ) (B : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [s, h, src, r0, c0, dst, i, r], μ'⟩ ∧
    (∀ q < i * h, μ' (dst + q) = B.getD q 0) ∧ SameOutside μ μ' dst (h * h)

end SubCopy
















































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_Tasks


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The two tasks between Negative Triangle and the (min,+)-product

[VW18, Theorem 4.2], one of the reductions behind Theorem 21(b), goes from
deciding Negative Triangle to the (min,+)-product in three steps: finding a negative triangle
([VW18, Lemma 4.1]), finding for all pairs `(i, j)` at once whether some `k` has `X[i,k] + Y[k,j] <
V[i,j]`, and a search for all entries of the product at once.  Each step is a host over an arbitrary
solver of the task below it (isHost_find, isHost_pairs, isHost_mp).  This file fixes the two tasks
in the middle, findTask and pairsTask.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-- Three matrices of weights, and the place for the three vertices of a triangle. -/
structure FindInst : Type extends TriInst where
  res : ℕ

/-- The place for the answer lies below the free pointer and does not meet the three matrices. -/
structure FindInst.Pre (x : FindInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop
    extends TriInst.Pre x.toTriInst μ fr where
  belowRes : x.res + 3 ≤ fr
  apartAB : Apart x.ab (x.n * x.n) x.res 3
  apartBC : Apart x.bc (x.n * x.n) x.res 3
  apartAC : Apart x.ac (x.n * x.n) x.res 3














/-- **Finding a negative triangle**: find(n, U, ab, bc, ac, res, fr) returns 1 if there is a
negative triangle, and then the cells res, res + 1, res + 2 hold the vertices `a`, `b`, `c` of one;
it returns 0 if there is none. -/
noncomputable def findTask : Task where
  Inst := FindInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac, x.res]
  Pre := FindInst.Pre
  Post x μ fr r μ' :=
    r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧
    (r = 1 → ∃ a b c : Fin x.n, μ' x.res = a.val ∧ μ' (x.res + 1) = b.val ∧ μ' (x.res + 2) = c.val ∧
      (triOf x.n x.AB x.BC x.AC).S a b c < 0) ∧
    KeptBut μ μ' fr x.res 3

/-- Three `n × n` matrices, and the place for `n²` flags. -/
structure PairsInst : Type where
  n : ℕ
  U : ℕ
  x : ℕ
  y : ℕ
  v : ℕ
  out : ℕ
  X : List ℤ
  Y : List ℤ
  V : List ℤ

/-- The three matrices and the place for the flags lie below the free pointer; the place for the
flags does not meet the matrices. -/
structure PairsInst.Pre (q : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ q.n
  U_pos : 1 ≤ q.U
  lenX : q.X.length = q.n * q.n
  lenY : q.Y.length = q.n * q.n
  lenV : q.V.length = q.n * q.n
  segX : Seg μ q.x q.X
  segY : Seg μ q.y q.Y
  segV : Seg μ q.v q.V
  leX : AbsLe q.X q.U
  leY : AbsLe q.Y q.U
  leV : AbsLe q.V q.U
  belowX : q.x + q.n * q.n ≤ fr
  belowY : q.y + q.n * q.n ≤ fr
  belowV : q.v + q.n * q.n ≤ fr
  belowOut : q.out + q.n * q.n ≤ fr
  apartX : Apart q.x (q.n * q.n) q.out (q.n * q.n)
  apartY : Apart q.y (q.n * q.n) q.out (q.n * q.n)
  apartV : Apart q.v (q.n * q.n) q.out (q.n * q.n)







/-- The flags: cell `i n + j` holds 1 if `X[i,k] + Y[k,j] < V[i,j]` for some `k < n`, and 0 if
not. -/
noncomputable def pairFlags (n : ℕ) (X Y V : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q =>
    flag (∃ k < n, X.getD (q / n * n + k) 0 + Y.getD (k * n + q % n) 0 < V.getD q 0)

/-- **All pairs**: allPairs(n, U, x, y, v, out, fr) writes the `n²` flags to out. -/
noncomputable def pairsTask : Task where
  Inst := PairsInst
  size q := q.n
  bound q := q.U
  args q := [q.n, q.U, q.x, q.y, q.v, q.out]
  Pre := PairsInst.Pre
  Post q μ fr _ μ' := Seg μ' q.out (pairFlags q.n q.X q.Y q.V) ∧ KeptBut μ μ' fr q.out (q.n * q.n)

end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_AllPairs


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# All pairs with a witness, with an algorithm that finds a negative triangle

The middle step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).  Given three n ×
n matrices X, Y, V, the host marks all pairs (i, j) for which some k has X[i,k] + Y[k,j] < V[i,j].
It cuts the three ranges into p = ⌈n/s⌉ blocks of s = ⌈n^{1/3}⌉ indices and visits the p³ triples of
blocks.  In each round it forms the s × s × s instance of the current triple, with the weights
X[i,k], Y[k,j], and -V[i,j], or 2U + 1 if (i, j) is already marked, and asks the solver for a
negative triangle.  A triangle that comes back marks a new pair; if there is none, the host goes on
to the next triple. So there are at most p³ + n² rounds.  The last block of a range is moved back so
that it ends at n (blocks may overlap), so there are no padding vertices.

The result is isHost_pairs : IsHost findTask pairsTask pairsTime pairsNeed.  The proof goes from the
inside to the outside: the third matrix of an instance (mask_meets); one question (ask_meets, with
the instance askInst and the meaning AskPost of the answer); the parts of a round (off_spec,
mark_spec, advance_spec); what a round achieves (Progress.mark and Progress.next: less is left to
do); a round (round_spec, with the invariant PairsInv); the host (pairs_spec; when nothing is left
to do the marks are the answer, Progress.complete).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedures -/

namespace Mask

/-- The local variables of mask: the arguments len, F (Large), ac (Mat), tmp (Flags), and the
counter q (Index). -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Large : ℕ := 1
@[inherit_doc Len] abbrev Mat : ℕ := 2
@[inherit_doc Len] abbrev Flags : ℕ := 3
@[inherit_doc Len] abbrev Index : ℕ := 4

end Mask

open Mask in
/-- mask(len, F, ac, tmp): for q < len, ac[q] := F if tmp[q] = 1, and ac[q] := -ac[q] otherwise. -/
def maskBody : Stmt :=
  .for Index (v Len) (
    .ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v Flags) (v Index))) (k 1)))
      (.store (((Light.Expr.op Light.Op.add) (v Mat) (v Index))) (v Large))
      (.store (((Light.Expr.op Light.Op.add) (v Mat) (v Index))) (((Light.Expr.op Light.Op.sub) (k 0) (M ((Light.Expr.op Light.Op.add) (v Mat) (v Index)))))))

namespace Ask

/-- The local variables of ask: the arguments n, s (Side), F (Large), x, y, v, out, the offsets oI,
oK, oJ, and fr (Free); then s² (Area), and results that are not used. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev Side : ℕ := 1
@[inherit_doc N] abbrev Large : ℕ := 2
@[inherit_doc N] abbrev X : ℕ := 3
@[inherit_doc N] abbrev Y : ℕ := 4
@[inherit_doc N] abbrev V : ℕ := 5
@[inherit_doc N] abbrev Out : ℕ := 6
@[inherit_doc N] abbrev OffI : ℕ := 7
@[inherit_doc N] abbrev OffK : ℕ := 8
@[inherit_doc N] abbrev OffJ : ℕ := 9
@[inherit_doc N] abbrev Free : ℕ := 10
@[inherit_doc N] abbrev Area : ℕ := 11
@[inherit_doc N] abbrev Unused : ℕ := 12

end Ask

open Ask in
/-- ask(n, s, F, x, y, v, out, oI, oK, oJ, fr): forms the instance of the triple of blocks at the
offsets oI, oK, oJ in the cells from fr (three matrices of s² cells; the block of marks is copied
behind them for a moment), and asks the solver for a negative triangle, with the place for the
answer at fr + 3s² and the free pointer fr + 3s² + 3.  The answer goes to local 0 and so is the
result. -/
def askBody (pFind pSub pMask : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Side) (v Side)))
    (Light.Stmt.seq (.call pSub [v N, v Side, v X, v OffI, v OffK, v Free] Unused)
      (Light.Stmt.seq
        (.call pSub [v N, v Side, v Y, v OffK, v OffJ, (Light.Expr.op Light.Op.add) (v Free) (v Area)] Unused)
        (Light.Stmt.seq
          (.call pSub
            [v N, v Side, v V, v OffI, v OffJ,
              (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)]
            Unused)
          (Light.Stmt.seq
            (.call pSub
              [v N, v Side, v Out, v OffI, v OffJ,
                (Light.Expr.op Light.Op.add)
                  ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)) (v Area)]
              Unused)
            (Light.Stmt.seq
              (.call pMask
                [v Area, v Large, (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area),
                  (Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)) (v Area)]
                Unused)
              (.call pFind
                [v Side, v Large, v Free, (Light.Expr.op Light.Op.add) (v Free) (v Area),
                  (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area),
                  (Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)) (v Area),
                  (Light.Expr.op Light.Op.add)
                    ((Light.Expr.op Light.Op.add)
                      ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)) (v Area))
                    (k 3)]
                0)))))))

namespace Pairs

/-- The local variables of allPairs: the arguments n, U, x, y, v, out, fr (Free); the side s of a
block and the number p of blocks; the numbers I, K, J of the three blocks and their offsets oI, oK,
oJ; F = 2U + 1 (Large); the address fr + 3s² of the solver's answer; the last result (Reply). -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev X : ℕ := 2
@[inherit_doc N] abbrev Y : ℕ := 3
@[inherit_doc N] abbrev V : ℕ := 4
@[inherit_doc N] abbrev Out : ℕ := 5
@[inherit_doc N] abbrev Free : ℕ := 6
@[inherit_doc N] abbrev Side : ℕ := 7
@[inherit_doc N] abbrev Blocks : ℕ := 8
@[inherit_doc N] abbrev BlockI : ℕ := 9
@[inherit_doc N] abbrev BlockK : ℕ := 10
@[inherit_doc N] abbrev BlockJ : ℕ := 11
@[inherit_doc N] abbrev OffI : ℕ := 12
@[inherit_doc N] abbrev OffK : ℕ := 13
@[inherit_doc N] abbrev OffJ : ℕ := 14
@[inherit_doc N] abbrev Large : ℕ := 15
@[inherit_doc N] abbrev Answer : ℕ := 16
@[inherit_doc N] abbrev Reply : ℕ := 17

end Pairs

open Pairs in
/-- The offset of the block whose number is in the local src, into the local dst: I s, or n - s if
n < I s + s. -/
def offStmt (dst src : ℕ) : Stmt :=
  (Light.Stmt.seq (.set dst ((Light.Expr.op Light.Op.mul) (v src) (v Side)))
    (.ite (Light.Cond.lt (v N) ((Light.Expr.op Light.Op.add) (v dst) (v Side)))
      (.set dst ((Light.Expr.op Light.Op.sub) (v N) (v Side))) .skip))

open Pairs in
/-- The next triple of blocks. -/
def advanceStmt : Stmt :=
  (Light.Stmt.seq (.set BlockJ ((Light.Expr.op Light.Op.add) (v BlockJ) (k 1)))
    (.ite (Light.Cond.eq (v BlockJ) (v Blocks))
      (Light.Stmt.seq (.set BlockJ (k 0))
        (Light.Stmt.seq (.set BlockK ((Light.Expr.op Light.Op.add) (v BlockK) (k 1)))
          (.ite (Light.Cond.eq (v BlockK) (v Blocks))
            (Light.Stmt.seq (.set BlockK (k 0)) (.set BlockI ((Light.Expr.op Light.Op.add) (v BlockI) (k 1)))) .skip)))
      .skip))

open Pairs in
/-- The pair that the solver has found is marked: out[(oI + a) n + (oJ + c)] := 1, where a and c
stand in the first and the third cell of the solver's answer. -/
def markStmt : Stmt :=
  .store (((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v Out)
              ((Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.add) (v OffI) (M (v Answer))) (v N)))
            ((Light.Expr.op Light.Op.add) (v OffJ) (M ((Light.Expr.op Light.Op.add) (v Answer) (k 2)))))) (k 1)

open Pairs in
/-- One round of allPairs: the offsets of the three blocks, the question, and then either a new mark
or the next triple of blocks. -/
def pairsRound (pAsk : ℕ) : Stmt :=
  (Light.Stmt.seq (offStmt OffI BlockI)
    (Light.Stmt.seq (offStmt OffK BlockK)
      (Light.Stmt.seq (offStmt OffJ BlockJ)
        (Light.Stmt.seq (.call pAsk [v N, v Side, v Large, v X, v Y, v V, v Out, v OffI, v OffK, v OffJ, v Free] Reply)
          (.ite (Light.Cond.eq (v Reply) (k 1)) markStmt advanceStmt)))))

open Pairs in
/-- p := ⌈n/s⌉, by counting up. -/
def countStmt : Stmt :=
  (Light.Stmt.seq (.set Blocks (k 0))
    (.while (Light.Cond.lt ((Light.Expr.op Light.Op.mul) (v Blocks) (v Side)) (v N))
      (.set Blocks ((Light.Expr.op Light.Op.add) (v Blocks) (k 1)))))

open Pairs in
/-- allPairs(n, U, x, y, v, out, fr): s, p, F and the address of the solver's answer; no pair is
marked; then the rounds, from the first triple of blocks on. -/
def pairsBody (pCbrt pFill pAsk : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pCbrt [v N] Side)
    (Light.Stmt.seq countStmt
      (Light.Stmt.seq (.set Large ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v U) (v U)) (k 1)))
        (Light.Stmt.seq
          (.set Answer
            ((Light.Expr.op Light.Op.add) (v Free)
              ((Light.Expr.op Light.Op.mul) (k 3) ((Light.Expr.op Light.Op.mul) (v Side) (v Side)))))
          (Light.Stmt.seq (.call pFill [v Out, (Light.Expr.op Light.Op.mul) (v N) (v N), k 0] Reply)
            (Light.Stmt.seq (.set BlockI (k 0))
              (Light.Stmt.seq (.set BlockK (k 0))
                (Light.Stmt.seq (.set BlockJ (k 0))
                  (.while (Light.Cond.lt (v BlockI) (v Blocks)) (pairsRound pAsk))))))))))

/-! ## Time and need -/

/-- The number of steps of mask. -/
def maskTime (len : ℕ) : ℕ := 25 * len + 6

/-- The number of steps of ask, if the solver takes T. -/
def askTime (T : ℕ → ℕ → ℕ) (s U : ℕ) : ℕ :=
  4 * subCopyTime s + maskTime (s * s) + T s (2 * U + 1) + 100

/-- The number of steps of one round of allPairs: three offsets, the question, and a mark or the
next triple of blocks. -/
def Pairs.roundTime (T : ℕ → ℕ → ℕ) (s U : ℕ) : ℕ := askTime T s U + 83

/-- **The number of steps of allPairs**, if the solver that finds negative triangles takes T: at
most p³ + n² rounds, with s = ⌈n^{1/3}⌉ (see cbrtLeast_eq_cbrtCeil) and p = ⌈n/s⌉, each with one
question at size s and bound 2U + 1. -/
def pairsTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  40 * n ^ 2 + 80 +
    (blockCount n (cbrtLeast n) ^ 3 + n ^ 2) *
        (220 * cbrtLeast n ^ 2 + 250 + T (cbrtLeast n) (2 * U + 1))

/-- **What allPairs needs**, if the solver needs r: the numbers up to 8n + 2U + 4, room for four
blocks and the solver's answer, three more levels of calls, and what the solver needs at the size
⌈n^{1/3}⌉ and the bound 2U + 1. -/
def pairsNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 8 * n + 2 * U + 4 + (r (cbrtLeast n) (2 * U + 1)).word
  cells := 4 * (cbrtLeast n * cbrtLeast n) + 3 + (r (cbrtLeast n) (2 * U + 1)).cells
  depth := 3 + (r (cbrtLeast n) (2 * U + 1)).depth

/-- The procedures that the host appends to the program of a solver whose program has o procedures
and whose procedure number is p: copy, fill, subCopy, cbrtCeil, mask, ask, allPairs, with the
numbers o, …, o + 6. -/
def pairsProcs (o p : ℕ) : Program :=
  [copyBody, fillBody, subCopyBody o, cbrtCeilBody, maskBody, askBody p (o + 2) (o + 4),
    pairsBody (o + 3) (o + 1) (o + 5)]

namespace Pairs

variable {P₀ R : Program} {p₀ pCbrt pFill pAsk pSub pCopy pMask : ℕ} {T : ℕ → ℕ → ℕ}
  {r : ℕ → ℕ → Need}

/-- The surroundings of allPairs: a solver that finds negative triangles, and the procedures that
the host adds. -/
structure Ctx (P₀ R : Program) (p pCbrt pFill pAsk pSub pCopy pMask : ℕ) (T : ℕ → ℕ → ℕ)
    (r : ℕ → ℕ → Need) : Prop where
  sol : Solves findTask P₀ p T r
  sub : (P₀ ++ R)[pSub]? = some (subCopyBody pCopy)
  copy : (P₀ ++ R)[pCopy]? = some copyBody
  mask : (P₀ ++ R)[pMask]? = some maskBody
  cbrt : (P₀ ++ R)[pCbrt]? = some cbrtCeilBody
  fill : (P₀ ++ R)[pFill]? = some fillBody
  ask : (P₀ ++ R)[pAsk]? = some (askBody p pSub pMask)

/-! ## The third matrix of an instance -/










































/-! ## One question -/

/-- The instance of the triple of blocks at the offsets oI, oK, oJ, with its three matrices at fr,
fr + s², fr + 2s² and the place for the answer behind them: the weights X[i,k], Y[k,j], and -V[i,j],
or 2U + 1 if the pair (i, j) is marked in O. -/
def askInst (q : PairsInst) (O : List ℤ) (fr s oI oK oJ : ℕ) : FindInst where
  n := s
  U := 2 * q.U + 1
  ab := fr
  bc := fr + s * s
  ac := fr + s * s + s * s
  AB := subMat q.n s oI oK q.X
  BC := subMat q.n s oK oJ q.Y
  AC := maskNeg (2 * (q.U : ℤ) + 1) (subMat q.n s oI oJ O) (subMat q.n s oI oJ q.V)
  res := fr + s * s + s * s + s * s






























/-- What ask returns: 0, and in the triple of blocks every pair with a witness is marked; or 1, and
the cells res and res + 2 hold a and c such that (oI + a, oJ + c) is an unmarked pair with a
witness. -/
def AskPost (q : PairsInst) (O : List ℤ) (s oI oK oJ res : ℕ) (z : ℤ) (μ' : ℕ → ℤ) : Prop :=
  (z = 0 ∧ BlockDone q.n s q.X q.Y q.V O oI oK oJ) ∨
  (z = 1 ∧ ∃ a < s, ∃ b < s, ∃ c < s, μ' res = a ∧ μ' (res + 2) = c ∧
    entry q.n O (oI + a) (oJ + c) ≠ 1 ∧ Witness q.n q.X q.Y q.V (oI + a) (oK + b) (oJ + c))



























































/-! ## The parts of a round -/

variable {q : PairsInst} {s p I K J : ℕ} {O : List ℤ}

/-- The local variables of allPairs during the rounds, as a list. -/
abbrev locals (q : PairsInst) (fr s p I K J : ℕ) (oI oK oJ z : ℤ) : List ℤ :=
  [q.n, q.U, q.x, q.y, q.v, q.out, fr, s, p, I, K, J, oI, oK, oJ, 2 * (q.U : ℤ) + 1,
    (fr + 3 * (s * s) : ℕ), z]

/-- (I', K', J') is the triple of blocks after (I, K, J); after the last triple comes (p, 0, 0). -/
structure Next (p I K J I' K' J' : ℕ) : Prop where
  leI : I' ≤ p
  ltK : K' < p
  ltJ : J' < p
  top : I' = p → K' = 0 ∧ J' = 0
  idx : tripleIdx p I' K' J' = tripleIdx p I K J + 1














































































/-! ## The invariant -/

/-- How far the rounds have come: the marks O are right, and in the triples of blocks before
(I, K, J) every pair with a witness is marked. -/
structure Progress (q : PairsInst) (s p I K J : ℕ) (O : List ℤ) : Prop where
  leI : I ≤ p
  ltK : K < p
  ltJ : J < p
  top : I = p → K = 0 ∧ J = 0
  marks : Marks q.n q.X q.Y q.V O
  done : ∀ I' < p, ∀ K' < p, ∀ J' < p, tripleIdx p I' K' J' < tripleIdx p I K J →
    BlockDone q.n s q.X q.Y q.V O (blockOff q.n s I') (blockOff q.n s K') (blockOff q.n s J')

/-- What is left to do: the number of triples of blocks from (I, K, J) on, plus the number of
unmarked pairs. -/
def todo (p I K J : ℕ) (O : List ℤ) : ℕ := (p * p * p - tripleIdx p I K J) + O.count 0






























/-- The state between two rounds: the marks stand at out, and below the free pointer no other cell
has changed. -/
def PairsInv (q : PairsInst) (μ : ℕ → ℤ) (fr s p : ℕ) (σ : State) : Prop :=
  ∃ (I K J : ℕ) (O : List ℤ) (oI oK oJ z : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals q fr s p I K J oI oK oJ z), μ'⟩ ∧ KeptBut μ μ' fr q.out (q.n * q.n) ∧
    Seg μ' q.out O ∧ Progress q s p I K J O

/-- What is left to do, read off the state. -/
def pairsVar (q : PairsInst) (p : ℕ) (σ : State) : ℕ :=
  todo p (σ.loc BlockI).toNat (σ.loc BlockK).toNat (σ.loc BlockJ).toNat
    (readSeg σ.mem q.out (q.n * q.n))







/-- What the limits have to allow for: the need of the solver behind three matrices and its answer,
two levels further down; room for four blocks; the numbers up to 8n + 2U + 4; three levels of
calls. -/
structure Lim (lim : Limits) (d : ℕ) (r : ℕ → ℕ → Need) (q : PairsInst) (fr s : ℕ) : Prop where
  ok : (r s (2 * q.U + 1)).Ok lim (fr + 3 * (s * s) + 3) (d + 2)
  cells : fr + 4 * (s * s) + 3 ≤ lim.space
  word : 8 * (q.n : ℤ) + 2 * (q.U : ℤ) + 4 ≤ lim.word
  depth : d + 3 ≤ lim.depth

/-! ## A round -/





















































/-! ## The host -/




















































































































































/-! ## The need -/






end Pairs

open Pairs


















end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_Passes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Two passes over an array, for the (min,+)-product found bit by bit

Two routines of the host for [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).

addc(len, x, src, dst): dst[i] := src[i] + x, in at most 19 len + 6 steps (addc_meets).
bump(len, x, fl, lo): lo[i] := lo[i] + x (1 − fl[i]), in at most 30 len + 6 steps: where the flag
is 0 the entry grows by x (bump_meets).
Both change no other cell.  Each is one pass, so each proof only says what round j reads.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Pass

/-- The local variables of addc and bump: the arguments len, x (Summand), the array that is only
read (src or fl) and the array that is written (dst or lo), and the counter. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Summand : ℕ := 1
@[inherit_doc Len] abbrev Source : ℕ := 2
@[inherit_doc Len] abbrev Dest : ℕ := 3
@[inherit_doc Len] abbrev Index : ℕ := 4

end Pass

open Pass in
/-- addc(len, x, src, dst): for i < len, dst[i] := src[i] + x. -/
def addcBody : Stmt := pass Index (v Len) (v Dest) (((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Source) (v Index))) (v Summand)))

open Pass in
/-- bump(len, x, fl, lo): for i < len, lo[i] := lo[i] + x (1 − fl[i]). -/
def bumpBody : Stmt :=
  pass Index (v Len) (v Dest)
    (((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Dest) (v Index)))
       ((Light.Expr.op Light.Op.mul) (v Summand)
         ((Light.Expr.op Light.Op.sub) (k 1) (M ((Light.Expr.op Light.Op.add) (v Source) (v Index)))))))
























































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_BitSearch


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The (min,+)-product from "all pairs", bit by bit

Theorem 21(b), after [VW18, Theorem 4.2].  The host below computes the
(min,+)-product over an arbitrary solver of the task "all pairs": for three matrices X, Y, V, which
pairs (i, j) have X[i,k] + Y[k,j] < V[i,j] for some k.

mp(n, U, a, b, c, fr).  All entries of the product lie between −2U and 2U.  The output array starts
as −2U everywhere.  Let R be least with 2^R > 4U; the powers 1, 2, …, 2^(R−1) are written to the R
cells from fr while R is found by doubling.  For t = R − 1, …, 0: V := lo + 2^t (the n² cells from
fr + R), the solver writes its flags to the next n² cells, and lo grows by 2^t where the flag is 0.
Before the round for t, lo ≤ C[i,j] < lo + 2^(t+1): lo is C[i,j] with the lowest t + 1 bits of
C[i,j] + 2U cleared (lows x (t + 1)).  The entries of V have absolute value at most 6U.

The result is isHost_mp : IsHost pairsTask mpTask mpTime mpNeed.  First the lists: the lower bounds
lows x t, which start as −2U (lows_top), end as the product (lows_zero), and change in a round as
bump changes them (lows_round, from bitLo_step).  Then the program: the powers of two (powers_spec),
a round (round_spec, with the invariant Inv), all rounds (rounds_spec), the host (mp_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The program -/

/-- The number of rounds: the least R with 2^R > 4U. -/
def mpRounds (U : ℕ) : ℕ := Nat.log 2 (4 * U) + 1

namespace Mp

/-- The local variables of mp: the arguments n, U, a, b, c, fr (Free); n² (Area), 2U, 4U, −2U (Low)
and 6U; Count counts the powers up and then the rounds down; Power is the power of two; then the
addresses fr + R of V (Asked), fr + R + n² of the flags and fr + R + 2n², the free pointer of the
solver (SolverFree); and the results of the calls, which are not used. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev A : ℕ := 2
@[inherit_doc N] abbrev B : ℕ := 3
@[inherit_doc N] abbrev C : ℕ := 4
@[inherit_doc N] abbrev Free : ℕ := 5
@[inherit_doc N] abbrev Area : ℕ := 6
@[inherit_doc N] abbrev TwoU : ℕ := 7
@[inherit_doc N] abbrev FourU : ℕ := 8
@[inherit_doc N] abbrev Low : ℕ := 9
@[inherit_doc N] abbrev SixU : ℕ := 10
@[inherit_doc N] abbrev Count : ℕ := 11
@[inherit_doc N] abbrev Power : ℕ := 12
@[inherit_doc N] abbrev Asked : ℕ := 13
@[inherit_doc N] abbrev Flags : ℕ := 14
@[inherit_doc N] abbrev SolverFree : ℕ := 15
@[inherit_doc N] abbrev Unused : ℕ := 16

end Mp

open Mp in
/-- The numbers n², 2U, 4U, −2U, 6U. -/
def mpConsts : Stmt :=
  (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v N) (v N)))
    (Light.Stmt.seq (.set TwoU ((Light.Expr.op Light.Op.add) (v U) (v U)))
      (Light.Stmt.seq (.set FourU ((Light.Expr.op Light.Op.add) (v TwoU) (v TwoU)))
        (Light.Stmt.seq (.set Low ((Light.Expr.op Light.Op.sub) (k 0) (v TwoU)))
          (.set SixU ((Light.Expr.op Light.Op.add) (v TwoU) (v FourU)))))))

open Mp in
/-- The powers 1, 2, …, 2^(R−1) are written to the cells from fr, while R is found by doubling. -/
def mpPowers : Stmt :=
  (Light.Stmt.seq (.set Count (k 0))
    (Light.Stmt.seq (.set Power (k 1))
      (.while (Light.Cond.le (v Power) (v FourU))
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Free) (v Count)) (v Power))
          (Light.Stmt.seq (.set Count ((Light.Expr.op Light.Op.add) (v Count) (k 1)))
            (.set Power ((Light.Expr.op Light.Op.add) (v Power) (v Power))))))))

open Mp in
/-- The round for t = Count − 1: V := lo + 2^t, the solver's flags, and lo grows by 2^t where the
flag is 0. -/
def mpRound (pPairs pAddc pBump : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Count ((Light.Expr.op Light.Op.sub) (v Count) (k 1)))
    (Light.Stmt.seq (.set Power (M ((Light.Expr.op Light.Op.add) (v Free) (v Count))))
      (Light.Stmt.seq (.call pAddc [v Area, v Power, v C, v Asked] Unused)
        (Light.Stmt.seq (.call pPairs [v N, v SixU, v A, v B, v Asked, v Flags, v SolverFree] Unused)
          (.call pBump [v Area, v Power, v Flags, v C] Unused)))))

open Mp in
/-- mp(n, U, a, b, c, fr), over the procedures number pPairs (a solver of "all pairs"), pFill, pAddc
and pBump. -/
def mpBody (pPairs pFill pAddc pBump : ℕ) : Stmt :=
  (Light.Stmt.seq mpConsts
    (Light.Stmt.seq mpPowers
      (Light.Stmt.seq (.set Asked ((Light.Expr.op Light.Op.add) (v Free) (v Count)))
        (Light.Stmt.seq (.set Flags ((Light.Expr.op Light.Op.add) (v Asked) (v Area)))
          (Light.Stmt.seq (.set SolverFree ((Light.Expr.op Light.Op.add) (v Flags) (v Area)))
            (Light.Stmt.seq (.call pFill [v C, v Area, v Low] Unused)
              (.while (Light.Cond.lt (k 0) (v Count)) (mpRound pPairs pAddc pBump))))))))

/-- The number of steps of one round, given the time of the solver. -/
def Mp.roundTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := T n (6 * U) + 49 * (n * n) + 42

/-- The time of the host, given the time of the solver: R calls at the bound 6U, and O(n²) steps for
each call. -/
def mpTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  mpRounds U * (T n (6 * U) + 49 * (n * n) + 70) + 13 * (n * n) + 60

/-- The need of the host, given the need of the solver: the numbers up to 8U + 1, room for the R
powers of two, for V and for the flags, and one more level of calls. -/
def mpNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := max (r n (6 * U)).word (8 * U + 1)
  cells := mpRounds U + 2 * (n * n) + (r n (6 * U)).cells
  depth := (r n (6 * U)).depth + 1

namespace Mp

/-! ## The number of rounds -/











/-! ## The lists of a round -/

variable {x : MatInst} {μ : ℕ → ℤ} {fr : ℕ}

/-- The lower bounds when t rounds remain: bitLo U t c for every entry c of the product, that is c
with the lowest t bits of c + 2U cleared.  So lo ≤ c < lo + 2^t. -/
def lows (x : MatInst) (t : ℕ) : List ℤ := (minPlusList x.n x.A x.B).map (bitLo x.U t)

/-- The matrix V of the round for t: the lower bounds plus 2^t. -/
def asked (x : MatInst) (t : ℕ) : List ℤ := (lows x (t + 1)).map (· + (2 : ℤ) ^ t)

/-- The flags that the solver returns in the round for t. -/
noncomputable def flags (x : MatInst) (t : ℕ) : List ℤ := pairFlags x.n x.A x.B (asked x t)



















































































/-! ## The surroundings -/

variable {P₀ R₀ : Program} {pPairs pFill pAddc pBump : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ}

/-- The surroundings of mp: a solver of "all pairs", and the three passes in the program. -/
structure Ctx (P₀ R₀ : Program) (pPairs pFill pAddc pBump : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) :
    Prop where
  sol : Solves pairsTask P₀ pPairs T r
  fill : (P₀ ++ R₀)[pFill]? = some fillBody
  addc : (P₀ ++ R₀)[pAddc]? = some addcBody
  bump : (P₀ ++ R₀)[pBump]? = some bumpBody

/-- What the limits have to allow for: the numbers of the solver and those up to 8U + 1; room for
the powers of two, V, the flags and the solver; one level of calls more than the solver needs. -/
structure Lim (lim : Limits) (d : ℕ) (r : ℕ → ℕ → Need) (x : MatInst) (fr : ℕ) : Prop where
  solver : ((r x.n (6 * x.U)).word : ℤ) ≤ lim.word
  word : 8 * (x.U : ℤ) + 1 ≤ lim.word
  cells : fr + (mpRounds x.U + 2 * (x.n * x.n) + (r x.n (6 * x.U)).cells) ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + ((r x.n (6 * x.U)).depth + 1) ≤ lim.depth








/-- The first eleven local variables, which do not change after mpConsts. -/
abbrev consts (x : MatInst) (fr : ℕ) : List ℤ :=
  [x.n, x.U, x.a, x.b, x.c, fr, (x.n * x.n : ℕ), (2 * x.U : ℕ), (4 * x.U : ℕ), -(2 * (x.U : ℤ)),
    (6 * x.U : ℕ)]

/-- The local variables during the rounds. -/
abbrev locals (x : MatInst) (fr count : ℕ) (power unused : ℤ) : List ℤ :=
  consts x fr ++ [(count : ℤ), power, (fr + mpRounds x.U : ℕ),
    (fr + mpRounds x.U + x.n * x.n : ℕ), (fr + mpRounds x.U + x.n * x.n + x.n * x.n : ℕ), unused]

/-! ## Before the rounds -/







































/-! ## A round -/

/-- The memory when t rounds remain: the lower bounds stand at c, the powers of two at fr, and below
the free pointer no cell outside c has changed. -/
structure Mem (x : MatInst) (μ : ℕ → ℤ) (fr t : ℕ) (μ' : ℕ → ℤ) : Prop where
  lo : Seg μ' x.c (lows x t)
  pows : ∀ i < mpRounds x.U, μ' (fr + i) = 2 ^ i
  kept : KeptBut μ μ' fr x.c (x.n * x.n)

/-- The state when t rounds remain. -/
def Inv (x : MatInst) (μ : ℕ → ℤ) (fr t : ℕ) (σ : State) : Prop :=
  ∃ (power unused : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame (locals x fr t power unused), μ'⟩ ∧ Mem x μ fr t μ'





/-- The instance that the solver gets in the round for t: the two matrices, V at fr + R, and the
place for the flags behind it. -/
def pairsInst (x : MatInst) (fr t : ℕ) : PairsInst :=
  ⟨x.n, 6 * x.U, x.a, x.b, fr + mpRounds x.U, fr + mpRounds x.U + x.n * x.n, x.A, x.B, asked x t⟩




























































































end Mp

/-! ## The host -/





















































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_FindNegativeTriangle


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Finding a negative triangle with an algorithm that decides whether there is one

[VW18, Lemma 4.1], a step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
The host asks the solver of Negative Triangle about the whole instance.  If the answer is yes, it
keeps three offsets and a side length h such that the h × h × h sub-instance at these offsets has a
negative triangle.  While h > 1 it puts h' = ⌈h/2⌉, asks about the eight sub-instances of side h'
made of the lower half [o, o + h') or the upper half [o + h - h', o + h) of each of the three
ranges, and goes on with one for which the answer is yes.  All eight questions are asked, and the
last yes counts.

The result is isHost_find : IsHost ntTask findTask findTime findNeed.  The proof goes from the
inside to the outside: one question (probe_meets: three calls of subCopy, one of the solver); the
questions of a round (try_spec and tries_spec, with the invariant TryInv); a round (round_spec; that
one of the eight answers is yes is NegAt.split); the rounds (loop_spec, with the invariant LoopInv);
the search and the host (search_spec, find_spec).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedures -/

namespace Probe

/-- The local variables of probe: the arguments n, U, ab, bc, ac, the offsets a0, b0, c0, the side
h and fr (Free); then h² (Area), and the results of subCopy, which are not used. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev AB : ℕ := 2
@[inherit_doc N] abbrev BC : ℕ := 3
@[inherit_doc N] abbrev AC : ℕ := 4
@[inherit_doc N] abbrev OffA : ℕ := 5
@[inherit_doc N] abbrev OffB : ℕ := 6
@[inherit_doc N] abbrev OffC : ℕ := 7
@[inherit_doc N] abbrev Side : ℕ := 8
@[inherit_doc N] abbrev Free : ℕ := 9
@[inherit_doc N] abbrev Area : ℕ := 10
@[inherit_doc N] abbrev Unused : ℕ := 11

end Probe

open Probe in
/-- probe(n, U, ab, bc, ac, a0, b0, c0, h, fr): copies the three h × h blocks of the sub-instance at
the offsets a0, b0, c0 to fr, fr + h², fr + 2h², and asks the solver of Negative Triangle about
them, with the free pointer fr + 3h².  The answer goes to local 0 and so is the result. -/
def probeBody (pNT pSub : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Side) (v Side)))
    (Light.Stmt.seq (.call pSub [v N, v Side, v AB, v OffA, v OffB, v Free] Unused)
      (Light.Stmt.seq
        (.call pSub [v N, v Side, v BC, v OffB, v OffC, (Light.Expr.op Light.Op.add) (v Free) (v Area)] Unused)
        (Light.Stmt.seq
          (.call pSub
            [v N, v Side, v AC, v OffA, v OffC,
              (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)]
            Unused)
          (.call pNT
            [v Side, v U, v Free, (Light.Expr.op Light.Op.add) (v Free) (v Area),
              (Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area),
              (Light.Expr.op Light.Op.add)
                ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Free) (v Area)) (v Area)) (v Area)]
            0)))))

namespace Find

/-- The local variables of find: the arguments n, U, ab, bc, ac, res (Answer), fr (Free); the
offsets a0, b0, c0 and the side length h of the current sub-instance; the next side length h' (Half)
and δ = h - h' (Shift); the offsets na, nb, nc of the last sub-instance with the answer yes; the
last answer of probe or of the solver (Reply). -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev U : ℕ := 1
@[inherit_doc N] abbrev AB : ℕ := 2
@[inherit_doc N] abbrev BC : ℕ := 3
@[inherit_doc N] abbrev AC : ℕ := 4
@[inherit_doc N] abbrev Answer : ℕ := 5
@[inherit_doc N] abbrev Free : ℕ := 6
@[inherit_doc N] abbrev OffA : ℕ := 7
@[inherit_doc N] abbrev OffB : ℕ := 8
@[inherit_doc N] abbrev OffC : ℕ := 9
@[inherit_doc N] abbrev Side : ℕ := 10
@[inherit_doc N] abbrev Half : ℕ := 11
@[inherit_doc N] abbrev Shift : ℕ := 12
@[inherit_doc N] abbrev NewA : ℕ := 13
@[inherit_doc N] abbrev NewB : ℕ := 14
@[inherit_doc N] abbrev NewC : ℕ := 15
@[inherit_doc N] abbrev Reply : ℕ := 16

end Find

open Find in
/-- One question of a round of find: about the sub-instance of side h' whose offsets are those of
the round, moved by δ where the triple t has a 1.  If the answer is yes, the offsets are noted in
na, nb, nc. -/
def tryStmt (pProbe : ℕ) (t : ℕ × ℕ × ℕ) : Stmt :=
  (Light.Stmt.seq
    (.call pProbe
      [v N, v U, v AB, v BC, v AC, (Light.Expr.op Light.Op.add) (v OffA) ((Light.Expr.op Light.Op.mul) (k t.1) (v Shift)),
        (Light.Expr.op Light.Op.add) (v OffB) ((Light.Expr.op Light.Op.mul) (k t.2.1) (v Shift)),
        (Light.Expr.op Light.Op.add) (v OffC) ((Light.Expr.op Light.Op.mul) (k t.2.2) (v Shift)), v Half, v Free]
      Reply)
    (.ite (Light.Cond.eq (v Reply) (k 1))
      (Light.Stmt.seq (.set NewA ((Light.Expr.op Light.Op.add) (v OffA) ((Light.Expr.op Light.Op.mul) (k t.1) (v Shift))))
        (Light.Stmt.seq
          (.set NewB ((Light.Expr.op Light.Op.add) (v OffB) ((Light.Expr.op Light.Op.mul) (k t.2.1) (v Shift))))
          (.set NewC ((Light.Expr.op Light.Op.add) (v OffC) ((Light.Expr.op Light.Op.mul) (k t.2.2) (v Shift))))))
      .skip))

/-- The questions for a list of triples, one after the other. -/
def triesStmt (pProbe : ℕ) : List (ℕ × ℕ × ℕ) → Stmt
  | [] => .skip
  | t :: ts => (Light.Stmt.seq (tryStmt pProbe t) (triesStmt pProbe ts))

open Find in
/-- h' := ⌈h/2⌉, by counting up. -/
def halfStmt : Stmt :=
  (Light.Stmt.seq (.set Half (k 0))
    (.while (Light.Cond.lt ((Light.Expr.op Light.Op.add) (v Half) (v Half)) (v Side))
      (.set Half ((Light.Expr.op Light.Op.add) (v Half) (k 1)))))

open Find in
/-- One round of find: h' = ⌈h/2⌉, δ = h - h', the eight questions, the new offsets and the new
side length. -/
def roundStmt (pProbe : ℕ) : Stmt :=
  (Light.Stmt.seq halfStmt
    (Light.Stmt.seq (.set Shift ((Light.Expr.op Light.Op.sub) (v Side) (v Half)))
      (Light.Stmt.seq (.set NewA (v OffA))
        (Light.Stmt.seq (.set NewB (v OffB))
          (Light.Stmt.seq (.set NewC (v OffC))
            (Light.Stmt.seq (triesStmt pProbe octants)
              (Light.Stmt.seq (.set OffA (v NewA))
                (Light.Stmt.seq (.set OffB (v NewB)) (Light.Stmt.seq (.set OffC (v NewC)) (.set Side (v Half)))))))))))

open Find in
/-- The search of find, once it is known that there is a negative triangle: rounds until the side
length is 1; then the offsets are the triangle, and the result is 1. -/
def searchStmt (pProbe : ℕ) : Stmt :=
  (Light.Stmt.seq (.set OffA (k 0))
    (Light.Stmt.seq (.set OffB (k 0))
      (Light.Stmt.seq (.set OffC (k 0))
        (Light.Stmt.seq (.set Side (v N))
          (Light.Stmt.seq (.while (Light.Cond.lt (k 1) (v Side)) (roundStmt pProbe))
            (Light.Stmt.seq (.store (v Answer) (v OffA))
              (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Answer) (k 1)) (v OffB))
                (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Answer) (k 2)) (v OffC)) (.set 0 (k 1))))))))))

open Find in
/-- find(n, U, ab, bc, ac, res, fr): asks about the whole instance; the result is 0 if the answer is
no, and else the search begins. -/
def findBody (pNT pProbe : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pNT [v N, v U, v AB, v BC, v AC, v Free] Reply)
    (.ite (Light.Cond.eq (v Reply) (k 0)) (.set 0 (k 0)) (searchStmt pProbe)))

/-! ## Time and need -/

/-- The number of steps of probe, if the solver takes T. -/
def probeTime (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ := 3 * subCopyTime h + T h U + 54

/-- The number of steps of one question of a round, with the test of the answer. -/
def tryTime (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ := probeTime T h U + 46

/-- A bound on the number of steps of the round that goes to the side length h: eight questions,
each with the copying of three blocks. -/
def roundBound (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ := 8 * (T h U + 150 * h ^ 2 + 130)

/-- **The number of steps of find**, if the solver of Negative Triangle takes T: one question at
size n, and one round for each side length of the chain ⌈n/2⌉, ⌈⌈n/2⌉/2⌉, …, 1. -/
def findTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  40 + T n U + ((halvingChain n).map fun h => roundBound T h U).sum

/-- **What find needs**, if the solver needs r: room for three blocks, three more levels of calls,
and what the solver needs at any size up to n. -/
def findNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := n + 2 + (Finset.range (n + 1)).sup fun h => (r h U).word
  cells := (Finset.range (n + 1)).sup fun h => 3 * (h * h) + (r h U).cells
  depth := 3 + (Finset.range (n + 1)).sup fun h => (r h U).depth

/-- The procedures that the host appends to the program of a solver whose program has o procedures
and whose procedure number is p: copy, subCopy, probe, find, with the numbers o, o + 1, o + 2,
o + 3. -/
def findProcs (o p : ℕ) : Program :=
  [copyBody, subCopyBody o, probeBody p (o + 1), findBody p (o + 2)]

namespace Find

variable {P₀ R : Program} {p pProbe pSub pCopy : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}

/-! ## The surroundings -/

/-- The surroundings of find: a solver of Negative Triangle, and the procedures probe, subCopy, copy
in the program. -/
structure Ctx (P₀ R : Program) (p pProbe pSub pCopy : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) :
    Prop where
  sol : Solves ntTask P₀ p T r
  probe : (P₀ ++ R)[pProbe]? = some (probeBody p pSub)
  sub : (P₀ ++ R)[pSub]? = some (subCopyBody pCopy)
  copy : (P₀ ++ R)[pCopy]? = some copyBody



















/-! ## One question -/

/-- The sub-instance of side h at the offsets a0, b0, c0, with its three blocks at fr, fr + h² and
fr + 2h². -/
def subInst (x : TriInst) (fr a0 b0 c0 h : ℕ) : TriInst :=
  ⟨h, x.U, fr, fr + h * h, fr + 2 * (h * h), subMat x.n h a0 b0 x.AB, subMat x.n h b0 c0 x.BC,
    subMat x.n h a0 c0 x.AC⟩













































/-! ## The questions of a round -/

/-- The state during the questions of a round: na, nb, nc are offsets of a sub-instance of side h',
and if Done holds (one of the questions asked so far had the answer yes), that sub-instance has a
negative triangle.  No cell below the free pointer has changed. -/
def TryInv (x : FindInst) (μ : ℕ → ℤ) (fr a0 b0 c0 h h' : ℕ) (Done : Prop) (σ : State) : Prop :=
  ∃ (na nb nc : ℕ) (reply : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, a0, b0, c0, h, h', (h - h' : ℕ), na, nb, nc,
      reply], μ'⟩ ∧
    Kept μ μ' fr ∧ (na + h' ≤ x.n ∧ nb + h' ≤ x.n ∧ nc + h' ≤ x.n) ∧
    (Done → NegAt x.n x.AB x.BC x.AC na nb nc h')







/-- The sub-instance that the triple t stands for has a negative triangle. -/
def NegOct (x : FindInst) (a0 b0 c0 h h' : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  NegAt x.n x.AB x.BC x.AC (a0 + t.1 * (h - h')) (b0 + t.2.1 * (h - h')) (c0 + t.2.2 * (h - h')) h'























































/-! ## A round, and the search -/

/-- The state between two rounds: the sub-instance of side h at the offsets a0, b0, c0 has a
negative triangle, and no cell below the free pointer has changed.  The six locals that a round uses
hold anything. -/
def LoopInv (x : FindInst) (μ : ℕ → ℤ) (fr h : ℕ) (σ : State) : Prop :=
  ∃ (a0 b0 c0 : ℕ) (z₁ z₂ z₃ z₄ z₅ z₆ : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, x.res, fr, a0, b0, c0, h, z₁, z₂, z₃, z₄, z₅, z₆],
      μ'⟩ ∧
    Kept μ μ' fr ∧ (a0 + h ≤ x.n ∧ b0 + h ≤ x.n ∧ c0 + h ≤ x.n) ∧
    NegAt x.n x.AB x.BC x.AC a0 b0 c0 h



























/-- The number of steps of the round that goes to the side length h'. -/
def roundTime (T : ℕ → ℕ → ℕ) (h' U : ℕ) : ℕ := 8 * tryTime T h' U + 10 * h' + 26










































/-- The number of steps of the search from the side length h on. -/
def loopTime (T : ℕ → ℕ → ℕ) (h U : ℕ) : ℕ :=
  ((halvingChain h).map fun h' => roundBound T h' U).sum + 4



























/-! ## The host -/

























































/-! ## The need -/



















end Find

open Find











end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_MinPlus_TimeBound


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The (min,+)-product from Negative Triangle: the claim

[VW18, Theorem 4.2] in the form needed for Theorem 21(b).  The three hosts
(finding from deciding, all pairs from finding, the product from all pairs) are composed, and their
time functions are bounded with the two properties of a good running time: T(s)/s is nondecreasing,
and T(s) ≥ s² (1 + log u).

Each host has one bound, up to a constant factor: finding costs O(T(n)) (findTime_dominated: the
side lengths of the search add up to at most 2n, and T(h) ≤ (h/n) T(n)); all pairs cost
O(n² T(⌈n^{1/3}⌉)) (pairsTime_dominated: there are O(n²) rounds, rounds_le); the product costs
O(log u) calls (mpTime_dominated, mpRounds_le).  claim_VW18_Theorem_4_2 puts the three together.
-/

@[expose] public section

/-! ## Good running times -/

namespace ThreeSumApsp.GoodTime

variable {T : ℕ → ℝ → ℝ}





















end ThreeSumApsp.GoodTime

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec





















namespace MinPlusFromNeg

/-! ## The parameters of a bound -/

/-- What a bound on the time of a host speaks about: a bound T on the time Tn of the solver, and an
instance of size n with a bound U ≤ u on its numbers. -/
structure Run where
  T : ℕ → ℝ → ℝ
  Tn : ℕ → ℕ → ℕ
  n : ℕ
  U : ℕ
  u : ℝ

/-- The solver keeps to its bound, and the instance is valid. -/
structure Run.Valid (p : Run) : Prop where
  solver : ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (p.Tn n U : ℝ) ≤ p.T n u
  n_pos : 1 ≤ p.n
  U_pos : 1 ≤ p.U
  U_le : (p.U : ℝ) ≤ p.u

/-- The run is valid, and the bound on the time of the solver is a good running time. -/
structure Run.Good (p : Run) : Prop extends p.Valid where
  good : GoodTime p.T

/-- The run is valid, and the bound on the time of the solver is at least n². -/
structure Run.Quadratic (p : Run) : Prop extends p.Valid where
  sq_le : ∀ u, (p.n : ℝ) ^ 2 ≤ p.T p.n u





/-! ## Finding from deciding -/
















































/-! ## All pairs from finding -/
















































/-! ## The product from all pairs -/



















































end MinPlusFromNeg



































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_NegativeTriangle_Passes


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Two loops over arrays for the reduction from Negative Triangle to Exact Triangle

[VW13, Theorem 3.3] in the form needed for Theorem 21(b).  The reduction compares
the binary prefixes of shifted weights; the two loops of this file shift the weights and compute the
prefixes, one more bit at a time.

affine(len, src, m, c, dst) writes m · src[i] + c to dst[i] for i < len, in at most 20 len + 6
steps (`affine_meets`).  prefDown(len, q, r, P) makes one step of the computation of the prefixes on
the arrays q and r: it appends the next bit to q[i] and removes it from r[i], for i < len, in at
most 38 len + 6 steps (`prefDown_meets`).  For prefDown the memory after j rounds is written down
(`prefMem`), `prefDownRound_spec` says what one round does, and the loop rule does the rest.  For
m = ±1 and a list that is bounded by U, `affine_meets_of_absLe` has the side conditions in terms
of U.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ### The locals of affine -/

namespace Aff

/-- The number of cells. -/
abbrev Len : ℕ := 0
/-- The address of the source. -/
abbrev Src : ℕ := 1
/-- The factor m. -/
abbrev Factor : ℕ := 2
/-- The summand c. -/
abbrev Shift : ℕ := 3
/-- The address of the destination. -/
abbrev Dst : ℕ := 4
/-- The counter i. -/
abbrev Idx : ℕ := 5

end Aff

open Aff in
/-- affine(len, src, m, c, dst): for i < len, dst[i] := m · src[i] + c. -/
def affineBody : Stmt := pass Idx (v Len) (v Dst) (((Light.Expr.op Light.Op.add)
                                                     ((Light.Expr.op Light.Op.mul) (v Factor) (M ((Light.Expr.op Light.Op.add) (v Src) (v Idx)))) (v Shift)))

/-! ### The locals of prefDown -/

namespace PrefDown

/-- The number of pairs. -/
abbrev Len : ℕ := 0
/-- The address of the array q. -/
abbrev ArrQ : ℕ := 1
/-- The address of the array r. -/
abbrev ArrR : ℕ := 2
/-- The number P with which 2 r[i] is compared (a power of two in the reduction). -/
abbrev Power : ℕ := 3
/-- The counter i. -/
abbrev Idx : ℕ := 4
/-- 2 r[i]. -/
abbrev Twice : ℕ := 5

end PrefDown

open PrefDown in
/-- One step on the pair (q[i], r[i]). -/
def prefDownRound : Stmt :=
  (Light.Stmt.seq (.set Twice ((Light.Expr.op Light.Op.mul) (k 2) (M ((Light.Expr.op Light.Op.add) (v ArrR) (v Idx)))))
    (.ite (Light.Cond.lt (v Twice) (v Power))
      (Light.Stmt.seq
        (.store ((Light.Expr.op Light.Op.add) (v ArrQ) (v Idx))
          ((Light.Expr.op Light.Op.mul) (k 2) (M ((Light.Expr.op Light.Op.add) (v ArrQ) (v Idx)))))
        (.store ((Light.Expr.op Light.Op.add) (v ArrR) (v Idx)) (v Twice)))
      (Light.Stmt.seq
        (.store ((Light.Expr.op Light.Op.add) (v ArrQ) (v Idx))
          ((Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.mul) (k 2) (M ((Light.Expr.op Light.Op.add) (v ArrQ) (v Idx)))) (k 1)))
        (.store ((Light.Expr.op Light.Op.add) (v ArrR) (v Idx)) ((Light.Expr.op Light.Op.sub) (v Twice) (v Power))))))

open PrefDown in
/-- prefDown(len, q, r, P): for i < len, one step on (q[i], r[i]). -/
def prefDownBody : Stmt := .for Idx (v Len) prefDownRound




























/-! ### prefDown -/

/-- The memory after j rounds of prefDown: the first j pairs have made their step. -/
def prefMem (μ : ℕ → ℤ) (q r : ℕ) (Pw : ℤ) (Q R : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote (wrote μ q (fun i => shiftQ Pw (Q.getD i 0) (R.getD i 0)) j) r
    (fun i => shiftR Pw (R.getD i 0)) j

section prefMem

variable {μ : ℕ → ℤ} {q r : ℕ} {Pw : ℤ} {Q R : List ℤ} {j : ℕ}

























end prefMem

/-- What prefDown needs: the two arrays lie in the memory, apart from each other, and the numbers
that are formed fit in a word. -/
structure PrefPre (lim : Limits) (μ : ℕ → ℤ) (q r : ℕ) (Pw : ℤ) (Q R : List ℤ) : Prop where
  segQ : Seg μ q Q
  segR : Seg μ r R
  len : R.length = Q.length
  space : (lim.space : ℤ) ≤ lim.word
  inQ : q + Q.length ≤ lim.space
  inR : r + Q.length ≤ lim.space
  apart : q + Q.length ≤ r ∨ r + Q.length ≤ q
  two_le : 2 ≤ lim.word
  fitsQ : ∀ x ∈ Q, |2 * x| ≤ lim.word ∧ |2 * x + 1| ≤ lim.word
  fitsR : ∀ x ∈ R, |2 * x| ≤ lim.word ∧ |2 * x - Pw| ≤ lim.word
















































































/-! ## affine with the factor ± 1 on a list with bounded entries -/































end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec3_Theorem21b_NegativeTriangle_Host


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Negative Triangle from Exact Triangle, as a host

[VW13, Theorem 3.3] in the form needed for Theorem 21(b): whether an instance with weights in
[−U, U] has a negative triangle is decided by asking O(log U) times whether there is a zero
triangle, each time after changing the weights, edge by edge, to numbers of absolute value O(U).

nt(n, U, ab, bc, ac, fr) computes L, the least number with 2^L > 6U, writes the shifted and doubled
weights 2(w(a,b) + U), 2(w(b,c) + U), 2(2U − w(a,c)) into an array r of 3n² cells, and zeros into an
array q of 3n² cells.  Then it makes L rounds.  A round moves one more bit of every number from r to
q (prefDown), so that q holds the prefixes of the level ℓ = L − 1, L − 2, …, 0; then, for e = 2 and
for e = 3, it writes e minus the prefixes of the third matrix to an array of n² cells and asks the
solver of Exact Triangle.  The answer is 1 if one of the 2L answers is 1.

The text is cut into parts, and each part has its lemma: `NegHost.init_spec`, `pow_spec`,
`fill_spec`, `probe_spec` (one question), `round_spec`, `rounds_spec`; `NegHost.nt_spec` puts them
together, and `isHost_nt` is the result.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

/-! ## The text -/

namespace NegHost

/-- The number n of vertices. -/
abbrev Verts : ℕ := 0
/-- The bound U on the weights. -/
abbrev Bound : ℕ := 1
/-- The address of the first matrix. -/
abbrev MatAB : ℕ := 2
/-- The address of the second matrix. -/
abbrev MatBC : ℕ := 3
/-- The address of the third matrix. -/
abbrev MatAC : ℕ := 4
/-- The free pointer, where the array q begins: its first part. -/
abbrev PreAB : ℕ := 5
/-- n². -/
abbrev Cells : ℕ := 6
/-- 2^L. -/
abbrev Power : ℕ := 7
/-- The number L of levels. -/
abbrev Levels : ℕ := 8
/-- The number of the round. -/
abbrev Round : ℕ := 9
/-- The answer so far. -/
abbrev Ans : ℕ := 10
/-- The result of a call. -/
abbrev Res : ℕ := 11
/-- 6U. -/
abbrev Bound6 : ℕ := 12
/-- The first part of the array r. -/
abbrev RestAB : ℕ := 14
/-- The array for the third matrix of a question. -/
abbrev Third : ℕ := 15
/-- The free pointer for the solver. -/
abbrev SolverFree : ℕ := 16
/-- The third part of the array q. -/
abbrev PreAC : ℕ := 17
/-- The second part of the array q. -/
abbrev PreBC : ℕ := 18
/-- 3n². -/
abbrev Cells3 : ℕ := 19
/-- The second part of the array r. -/
abbrev RestBC : ℕ := 20
/-- The third part of the array r. -/
abbrev RestAC : ℕ := 21

end NegHost

open NegHost

/-- The beginning of nt: sizes and addresses. -/
def ntInit : Stmt :=
  (Light.Stmt.seq (.set Cells ((Light.Expr.op Light.Op.mul) (v Verts) (v Verts)))
    (Light.Stmt.seq (.set Bound6 ((Light.Expr.op Light.Op.mul) (k 6) (v Bound)))
      (Light.Stmt.seq (.set PreBC ((Light.Expr.op Light.Op.add) (v PreAB) (v Cells)))
        (Light.Stmt.seq (.set PreAC ((Light.Expr.op Light.Op.add) (v PreBC) (v Cells)))
          (Light.Stmt.seq (.set RestAB ((Light.Expr.op Light.Op.add) (v PreAC) (v Cells)))
            (Light.Stmt.seq (.set RestBC ((Light.Expr.op Light.Op.add) (v RestAB) (v Cells)))
              (Light.Stmt.seq (.set RestAC ((Light.Expr.op Light.Op.add) (v RestBC) (v Cells)))
                (Light.Stmt.seq (.set Third ((Light.Expr.op Light.Op.add) (v RestAC) (v Cells)))
                  (Light.Stmt.seq (.set SolverFree ((Light.Expr.op Light.Op.add) (v Third) (v Cells)))
                    (Light.Stmt.seq (.set Cells3 ((Light.Expr.op Light.Op.mul) (k 3) (v Cells)))
                      (Light.Stmt.seq (.set Power (k 1)) (.set Levels (k 0)))))))))))))

/-- The number of levels L and the power 2^L, by doubling. -/
def ntPow : Stmt :=
  .while ((Light.Cond.le (v Power) (v Bound6))) (
    (Light.Stmt.seq (.set Power ((Light.Expr.op Light.Op.mul) (k 2) (v Power)))
      (.set Levels ((Light.Expr.op Light.Op.add) (v Levels) (k 1)))))

/-- The arrays r and q at the top level. -/
def ntFill (pAff : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pAff [v Cells, v MatAB, k 2, (Light.Expr.op Light.Op.mul) (k 2) (v Bound), v RestAB] Res)
    (Light.Stmt.seq (.call pAff [v Cells, v MatBC, k 2, (Light.Expr.op Light.Op.mul) (k 2) (v Bound), v RestBC] Res)
      (Light.Stmt.seq
        (.call pAff
          [v Cells, v MatAC, (Light.Expr.op Light.Op.sub) (k 0) (k 2), (Light.Expr.op Light.Op.mul) (k 4) (v Bound),
            v RestAC]
          Res)
        (.call pAff [v Cells3, v RestAB, k 0, k 0, v PreAB] Res))))

/-- One question to the solver of Exact Triangle: the third matrix for the exact value e, the call,
and the note of a positive answer. -/
def ntProbe (pET pAff e : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pAff [v Cells, v PreAC, (Light.Expr.op Light.Op.sub) (k 0) (k 1), k e, v Third] Res)
    (Light.Stmt.seq (.call pET [v Verts, v Bound6, v PreAB, v PreBC, v Third, v SolverFree] Res)
      (.ite (Light.Cond.eq (v Res) (k 1)) (.set Ans (k 1)) .skip)))

/-- One round: the next level, and its two questions. -/
def ntRound (pET pAff pDown : ℕ) : Stmt :=
  (Light.Stmt.seq (.call pDown [v Cells3, v PreAB, v RestAB, v Power] Res)
    (Light.Stmt.seq (ntProbe pET pAff 2) (ntProbe pET pAff 3)))

/-- The L rounds. -/
def ntRounds (pET pAff pDown : ℕ) : Stmt :=
  (Light.Stmt.seq (.set Ans (k 0)) (.for Round (v Levels) (ntRound pET pAff pDown)))

/-- nt(n, U, ab, bc, ac, fr). -/
def ntBody (pET pAff pDown : ℕ) : Stmt :=
  (Light.Stmt.seq ntInit
    (Light.Stmt.seq ntPow (Light.Stmt.seq (ntFill pAff) (Light.Stmt.seq (ntRounds pET pAff pDown) (.set 0 (v Ans))))))

/-- The number of levels: for U ≥ 1, the least L with 2^L > 6U. -/
def ntLevels (U : ℕ) : ℕ := Nat.log 2 (6 * U) + 1

/-- The time of nt, if the solver of Exact Triangle takes T n U steps. -/
def ntTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  120 * (n * n) + 120 + ntLevels U * (154 * (n * n) + 92 + 2 * T n (6 * U))

/-- The need of nt, if the solver of Exact Triangle needs r n U. -/
def ntNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := 24 * U + 8 + (r n (6 * U)).word
  cells := 7 * (n * n) + (r n (6 * U)).cells
  depth := (r n (6 * U)).depth + 1









/-! ## The local variables and the hypotheses -/

namespace NegHost

/-- The locals of nt after its beginning.  The last five arguments are those that change later: the
power of two, the number of levels, the number of the round, the answer so far and the result of the
last call.  Local 13 is not used and stays 0. -/
abbrev locals (x : TriInst) (fr : ℕ) (pw lv rd ans res : ℤ) : List ℤ :=
  [x.n, x.U, x.ab, x.bc, x.ac, fr, (x.n * x.n : ℕ), pw, lv, rd, ans, res, (6 * x.U : ℕ), 0,
    (fr + 3 * (x.n * x.n) : ℕ), (fr + 6 * (x.n * x.n) : ℕ), (fr + 7 * (x.n * x.n) : ℕ),
    (fr + 2 * (x.n * x.n) : ℕ), (fr + x.n * x.n : ℕ), (3 * (x.n * x.n) : ℕ),
    (fr + 4 * (x.n * x.n) : ℕ), (fr + 5 * (x.n * x.n) : ℕ)]

/-- The program has the solver and the two loops over arrays, the instance is as the task
prescribes, and the limits allow for the need of nt. -/
structure Ctx (P₀ R' : Program) (p pAff pDown : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves etTask P₀ p T r
  aff : (P₀ ++ R')[pAff]? = some affineBody
  down : (P₀ ++ R')[pDown]? = some prefDownBody
  pre : x.Pre μ fr
  ok : (ntNeed r x.n x.U).Ok lim fr d

variable {P₀ R' : Program} {p pAff pDown : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {lim : Limits}
  {d : ℕ} {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ}

























/-! ## The beginning -/



























/-- The state of the loop that doubles after i rounds: Power = 2^i and Levels = i. -/
def PowInv (x : TriInst) (μ : ℕ → ℤ) (fr i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame (locals x fr (2 ^ i : ℕ) i 0 0 0), μ⟩
























/-! ## The memory -/

/-- The memory of nt at the level ℓ: the array q holds the prefixes, the array r the rests, and
nothing below the free pointer has changed. -/
def NtMem (x : TriInst) (μ : ℕ → ℤ) (fr ℓ : ℕ) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' fr ((negStart x.U x.AB x.BC x.AC).map (prefQ ℓ)) ∧
    Seg μ' (fr + 3 * (x.n * x.n))
      ((negStart x.U x.AB x.BC x.AC).map (prefR (ntLevels x.U) ℓ)) ∧
    Kept μ μ' fr










































































/-! ## One question -/

/-- The instance of Exact Triangle for the level ℓ and the exact value e, as it lies in the arrays
of nt. -/
def question (x : TriInst) (fr ℓ : ℕ) (e : ℤ) : TriInst :=
  ⟨x.n, 6 * x.U, fr, fr + x.n * x.n, fr + 6 * (x.n * x.n), (affL 2 (2 * x.U) x.AB).map (prefQ ℓ),
    (affL 2 (2 * x.U) x.BC).map (prefQ ℓ), negThird x.U ℓ e x.AC⟩

/-- The instance of Exact Triangle for the level ℓ and the exact value e has a zero triangle. -/
def NtYes (x : TriInst) (ℓ : ℕ) (e : ℤ) : Prop :=
  (triOf x.n ((affL 2 (2 * x.U) x.AB).map (prefQ ℓ)) ((affL 2 (2 * x.U) x.BC).map (prefQ ℓ))
    (negThird x.U ℓ e x.AC)).HasZeroTriangle




















































/-- The state of nt between two steps of a round: the locals, with some result of the last call,
and the memory at the level ℓ. -/
def St (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (rd ans : ℤ) (ℓ : ℕ) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr (2 ^ ntLevels x.U : ℕ) (ntLevels x.U) rd ans res), μ'⟩ ∧
      NtMem x μ fr ℓ μ'


























































/-! ## The rounds -/

/-- One of the questions at the levels from ℓ₀ on has the answer yes. -/
def NtFound (x : TriInst) (L ℓ₀ : ℕ) : Prop :=
  ∃ ℓ, ℓ₀ ≤ ℓ ∧ ℓ < L ∧ ∃ e : ℤ, (e = 2 ∨ e = 3) ∧ NtYes x ℓ e


















































































































/-! ## The procedure -/

































end NegHost















end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Ceiling


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Corollaries 26 and 31 in the light language: ⌈a m / b⌉ by counting

Proof of Corollary 26: "Let L := 21m and t := ⌈m/9⌉"; proof of Corollary 31: "with L := ⌈cm⌉ and t
:= ⌈θm⌉". For rational c = a/b the number ⌈a m / b⌉ is found without division: count in steps of b
up to a m. The numbers a and b are constants of the program text.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

namespace CeilMul

/-- The locals of ceilMul: the argument m, which the result replaces; the product a m; a counter
that goes up in steps of b; and the number of its steps. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Goal : ℕ := 1
@[inherit_doc Arg] abbrev Reached : ℕ := 2
@[inherit_doc Arg] abbrev Steps : ℕ := 3

end CeilMul

open CeilMul in
/-- ceilMul(m) counts up to a m in steps of b. For m = 0 the result is 0, and the constant a is not
touched (it need not fit in a word then). -/
def ceilMulBody (a b : ℕ) : Stmt :=
  .ite ((Light.Cond.eq (v Arg) (k 0))) .skip
    ((Light.Stmt.seq (.set Goal ((Light.Expr.op Light.Op.mul) (k a) (v Arg)))
       (Light.Stmt.seq (.set Reached (k 0))
         (Light.Stmt.seq (.set Steps (k 0))
           (Light.Stmt.seq
             (.while (Light.Cond.lt (v Reached) (v Goal))
               (Light.Stmt.seq (.set Reached ((Light.Expr.op Light.Op.add) (v Reached) (k b)))
                 (.set Steps ((Light.Expr.op Light.Op.add) (v Steps) (k 1)))))
             (.set Arg (v Steps)))))))










































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Contracts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollaries 26 and 31 in the light language: procedure numbers, time functions and interfaces

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉"; "for smaller m the corollary again holds trivially". Here a query
then computes an inner product, which takes a bounded number of steps since D is bounded.

The routines are relocatable: they receive the addresses of X and Y and a free pointer fr. From fr
on they use

    flag (1) | b0 (1) | 4^m (1) | X' (N 4^m) | Y' (4^m N) | the block of Theorem 30 from b0 on

flag = 1 says that the data structure of Theorem 30 has been built for the padded matrices X', Y';
flag = 0 that m is below the threshold m₀ (a constant of the program text) and that queries compute
inner products. Nothing is assumed about the cells from fr on.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Proc
abbrev copy : ℕ := 58
abbrev fill : ℕ := 59
abbrev log4 : ℕ := 60
abbrev padX : ℕ := 62
abbrev ipAt : ℕ := 63
abbrev pre31 : ℕ := 64
abbrev query31 : ℕ := 65


abbrev offline32 : ℕ := 68

abbrev allInstances26 : ℕ := 70
abbrev regimeTest26 : ℕ := 71
abbrev levels31 : ℕ := 72
abbrev switch31 : ℕ := 73
end Proc

/-! ## Time functions -/

def tCopy (n : ℕ) : ℕ := 16 * n + 6
def tFill (n : ℕ) : ℕ := 13 * n + 6
def tLog4 (m : ℕ) : ℕ := 20 * m + 20
/-- For each row: a copy, a fill, and the arithmetic of the addresses. -/
def tPadX (N D' : ℕ) : ℕ := N * (16 * D' + 80) + 10
def tIpAt (D : ℕ) : ℕ := 40 * D + 20

/-! ## The small routines -/

/-- copy(src, dst, n). -/
def CopySpec (lim : Limits) (P : Program) : Prop :=
  ∀ (src dst n : ℕ) (μ : ℕ → ℤ), src + n ≤ lim.space → dst + n ≤ lim.space → n < lim.space →
      (src + n ≤ dst ∨ dst + n ≤ src) →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.copy d [src, dst, n] μ (tCopy n) fun _ μ' =>
        (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n

/-- fill(dst, n, x). -/
def FillSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (dst n : ℕ) (x : ℤ) (μ : ℕ → ℤ), dst + n ≤ lim.space → n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.fill d [dst, n, x] μ (tFill n) fun _ μ' =>
        (∀ i < n, μ' (dst + i) = x) ∧ SameOutside μ μ' dst n

/-- log4(D, a) returns m = ⌈log₄ D⌉ and writes 4^m to the cell a. -/
def Log4Spec (lim : Limits) (P : Program) : Prop :=
  ∀ (D₀ a : ℕ) (μ : ℕ → ℤ), a < lim.space → ((4 ^ Nat.clog 4 D₀ : ℕ) : ℤ) ≤ lim.word →
      (Nat.clog 4 D₀ : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.log4 d [D₀, a] μ (tLog4 (Nat.clog 4 D₀)) fun r μ' =>
      r = Nat.clog 4 D₀ ∧ μ' = Function.update μ a ((4 ^ Nat.clog 4 D₀ : ℕ) : ℤ)

/-- padX(N, D, D', aX, aX') writes X, padded with zero columns to D' columns, to aX'. -/
def PadXSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (N D₀ D' aX aX' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (μ : ℕ → ℤ), D₀ ≤ D' → 1 ≤ D' →
      MatAt μ aX X → aX + N * D₀ ≤ aX' →
    aX' + N * D' < lim.space →
    ∀ d, d + 1 ≤ lim.depth → Meets lim P Proc.padX d [N, D₀, D', aX, aX'] μ (tPadX N D') fun _ μ' =>
      MatAt μ' aX' (padInnerCols D' X) ∧ SameOutside μ μ' aX' (N * D')

/-- ipAt(I, J, N, D, aX, aY) returns (XY)[I, J] as an inner product. -/
def IpAtSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (N D₀ aX aY : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N),
    1 ≤ D₀ → MatAt μ aX X → MatAt μ aY Y → (∀ i j, |X i j| ≤ U) →
        (∀ i j, |Y i j| ≤ U) → aX + N * D₀ < lim.space →
    aY + D₀ * N < lim.space → (D₀ : ℤ) * (U * U) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.ipAt d [(I : ℕ), (J : ℕ), N, D₀, aX, aY] μ (tIpAt D₀) fun r μ' =>
        r = (X * Y) I J ∧ μ' = μ

/-! ### copy and fill are those of the library -/













/-! ### ⌈log₄ D⌉ -/

namespace Log4

/-- The locals of log4: the argument D, which the result replaces; the address a; the power of 4;
and its exponent. -/
abbrev Dim : ℕ := 0
@[inherit_doc Dim] abbrev Cell : ℕ := 1
@[inherit_doc Dim] abbrev Power : ℕ := 2
@[inherit_doc Dim] abbrev Exp : ℕ := 3

end Log4

open Log4 in
/-- log4(D, a): multiply by 4 until D is reached; store the power at a and return the exponent. -/
def log4Body : Stmt :=
  (Light.Stmt.seq (.set Power (k 1))
    (Light.Stmt.seq (.set Exp (k 0))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v Power) (v Dim))
          (Light.Stmt.seq (.set Power ((Light.Expr.op Light.Op.mul) (v Power) (k 4)))
            (.set Exp ((Light.Expr.op Light.Op.add) (v Exp) (k 1)))))
        (Light.Stmt.seq (.store (v Cell) (v Power)) (.set Dim (v Exp))))))


































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_QueryLists


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# What a query reads (proof of Theorem 30, "Query")

The output string, which the paper calls w, is η as a string of variables and w as the list of its
digits; the levels of its inner set Q are the positions of the digit 9.  w is also the list of
digits of the private leaf of η, and `scatter w s` replaces its m nines by a string s of m digits:
the paper's "forming its leaf or its box from the private leaf".  A query adds up the products at
the leaves of order below t contributing to η, and the stored values of the boxes of η (steps (2)
and (3) of the query in Section 4.3).

* `lowList`: the strings with at least m - t + 1 nines give the leaves of order below t ("Each of
  these leaves is obtained from the private leaf of w, which has P₀ at every level of Q, by picking
  fewer than t of those levels and replacing P₀ with one of the nine other terms at each of them");
* `boxesOf`: the strings with exactly m - t nines give the leaves of order exactly t, and `starRun`
  turns the leading nines into stars.  This is the second description of the boxes of w in
  Section 4.2: "For such a leaf, consider the lowest level of Q at which it chooses a term other
  than P₀, and replace its P₀ by a star at every lower level of Q (or at every level of Q, if
  t = 0).  The result is a box of w, and each box of w arises exactly once in this way".  On cubes
  the result is `starBelow`, and the members of the list are exactly the strings of the cubes
  `starBelow η τ` for these leaves τ (`mem_boxesOf_iff`; no other proof rests on this statement).
  In the first description the nines are the levels of V, and the leading nines those of F_V, which
  "is the longest initial segment of Q contained in V".  `starRunIf` is `starRun` as a pass over the
  string with one flag.

The results are `sum_lowList` and `sum_boxesOf` (a sum over one of the lists is the sum over the set
of the paper) and `sum_queryTerms_storedD` (the numbers that a query adds up have the sum of the
query of the paper). Each list is compared with its set by counting
(`List.sum_map_eq_sum_of_length_eq_card`):
1. The list has no repetitions: `scatter w` is injective on strings of m digits, and `starRun` can
   be undone (`lowList_nodup`, `boxesOf_nodup`).
2. Each member is the list of digits of a member of the set.  `scatter w s` is a leaf τ contributing
   to η with as many symbols P₀ as s has nines (`exists_leaf_scatter`).  With at least m - t + 1
   nines its order is below t (`exists_of_mem_lowList`).  With exactly m - t nines its order is t.
   The cube `starBelow η τ` has the digits of τ with stars at the levels of F_Z, where Z, the set
   of the levels of Q at which τ chooses P₀, is the nines of s.  `Unreached` is the formula for F_Z
   read on digits (`unreached_iff_mem_FV`); it holds exactly at the leading nines of s
   (`getD_scatter_starRun`), so the cube has the digits `scatter w (starRun s)`
   (`digitsC_starBelow`, `exists_leaf_of_mem_boxesOf`), and it is a box of η (`starBelow_mem`,
   `exists_of_mem_boxesOf`).
3. The lists have ∑_{d<t} α_d and α_t members (`length_lowList`, `length_boxesOf`), and so have the
   sets, by the last line of Lemma 28 (`lemma_28_counts`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The list w with its digits 9 replaced, from the left, by the digits of s. -/
def scatter : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: w, [] => x :: w
  | x :: w, d :: s => if x = 9 then d :: scatter w s else x :: scatter w (d :: s)

/-- The leaves of order below t contributing to the output string with the digits w, in
lexicographic order: at the m levels of Q they have at least m - t + 1 digits 9. -/
def lowList (m t : ℕ) (w : List ℕ) : List (List ℕ) := (nineStrs m (m - t + 1) m).map (scatter w)

/-- The leading digits 9 turned into 10: F_V "is the longest initial segment of Q contained in V"
(Section 4.2). -/
def starRun : List ℕ → List ℕ
  | [] => []
  | d :: l => if d = 9 then 10 :: starRun l else d :: l

/-- The boxes of the output string with the digits w.  "There is another way to describe the boxes
of w, in terms of the leaves of order exactly t contributing to w.  For such a leaf, consider the
lowest level of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every
lower level of Q (or at every level of Q, if t = 0)" (Section 4.2).  Such a leaf has at the m levels
of Q a string with exactly m - t digits 9, and the leading ones are turned into stars
(`mem_boxesOf_iff`). -/
def boxesOf (m t : ℕ) (w : List ℕ) : List (List ℕ) :=
  (nineStrs m (m - t) (m - t)).map fun s => scatter w (starRun s)

/-- The numbers that a query adds up, in the order in which it adds them: the products at the leaves
of `lowList`, read from the two encodings, then the stored values of the boxes of `boxesOf`;
`stored l` is the value stored for the box l. -/
def queryTerms (m t : ℕ) (encA encB : List ℤ) (stored : List ℕ → ℤ) (w : List ℕ) : List ℤ :=
  (lowList m t w).map (leafProduct encA encB) ++ (boxesOf m t w).map stored

/-! ## Putting a string at the positions of the nines -/








































/-! ## The leading nines turned into stars -/











/-- `starRun` continued on the rest of a string that is read digit by digit: flag says that all the
digits read so far were nines, so the run of stars goes on; otherwise the rest is kept. -/
def starRunIf (flag : Bool) (s : List ℕ) : List ℕ := if flag then starRun s else s











/-- Position i is one of "the levels that we have not reached" (F_V, Section 4.2).  Here w is the
list of digits of the output string, so its nines are the levels of Q, and u is the list of digits
of a leaf, whose nines among them are the levels of V: i is a level of Q below every level of Q ∖ V.
-/
 def Unreached (w u : List ℕ) (i : ℕ) : Prop :=
  w.getD i 0 = 9 ∧ ∀ j, w.getD j 0 = 9 → u.getD j 0 ≠ 9 → i < j











































/-! ## The leaves of order below t -/

section

variable {L m t : ℕ} {η : OutStr L}



























































/-! ## The boxes -/




















































































end

/-! ## The query -/













end ThreeSumApsp.Spec

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_StarBoxes


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The boxes with e stars, as a list (proof of Lemma 29)

"A box in which f of the symbols are P₀ or stars is obtained from a leaf of order m - f (namely the
leaf we get by replacing its stars with P₀) by turning the e lowest symbols P₀ of that leaf into
stars, for some e ≤ f."  So the boxes with exactly e stars are the leaves with between e and m - t
symbols P₀, with the first e digits 9 turned into 10: this is `starBoxes`.

The list contains exactly the boxes with e stars (`mem_starBoxes`, `exists_of_mem_starBoxes`), each
of them once (`starBoxes_nodup`), so it has as many members as there are such boxes
(`length_starBoxes`), and all lists together have as many members as there are boxes
(`sum_length_starBoxes`).

The lists are the order of work of Lemma 29: "We compute the values of the boxes in increasing order
of their number of stars", "Generating the boxes with e stars and inserting them into the trie".
All of them go into the trie of the tile.  The number of stars can be read off a box
(`starCount_of_mem_starBoxes`), so boxes from different lists are different strings, and a string
is a box exactly if it is in the list for its number of stars (`isBoxDigits_digitsC`).  There are
boxes with e stars only for e ≤ m - t (`le_of_mem_starBoxes`).  Replacing the highest star of a box
with e + 1 stars by a term gives a box with e stars (`exists_lastStar_of_mem_starBoxes`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The boxes with e stars, as lists of digits. -/
def starBoxes (L m t e : ℕ) : List (List ℕ) := (nineStrs L e (m - t)).map (starFirst e)

























































/-- The string l is a box: it is in the list of the boxes with its number of stars. -/
abbrev IsBoxDigits (L m t : ℕ) (l : List ℕ) : Prop := l ∈ starBoxes L m t (starCount l)













































































end ThreeSumApsp.Spec

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_TileTries


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The trie of a tile, and the tries of all tiles (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  `tileTrie` builds this trie.

"We compute the values of the boxes in increasing order of their number of stars": `fillUpTo` goes
through the boxes with 0, 1, … stars (`starBoxes`), and `fillTrie` inserts the boxes with e stars
with their values (`boxValue`): the value of a box without stars is "the product of its two numbers
in the encodings", the value of a box with stars is computed "with ten lookups in the trie" of the
tile.  `allTries` does this for all tiles, in one array; the number of a trie is the number of its
tile.  The array and the list of the roots form a record `TrieStore`.

What the array holds at a moment is a function from pairs (the number of a trie, a box) to values:
`storedUpTo` in the middle of a tile, `storedAll` between two tiles.
1. One more box is one more entry, the state after all boxes with k stars is the state before the
   first box with k + 1 stars, and a complete tile adds its boxes to `storedAll`
   (`storedUpTo_snoc`, `storedUpTo_succ`, `storedAll_snoc`).
2. Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars
   (`exists_lastStar_of_mem_starBoxes`); so, once the boxes with e stars are stored, the value
   computed for the box is that of the dynamic program (`boxValue_eq`).
3. So the array represents these functions, in the sense of `TrieRep`, after some boxes with e stars
   (`fillTrie_rep`), after all boxes with fewer than k stars (`fillUpTo_rep`) and after some tiles
   (`allTries_rep`).
4. Hence a lookup returns the value of the dynamic program of Lemma 29 (`lookup_allTries`), which is
   the value of the box: the array holds "for every tile, the values of all its boxes"
   (`lookup_allTries_eq_val`).  Every box that a query reads is there (`boxesOf_mem_starBoxes`).
5. Space: "O(L) […] space per box" (`length_tileTrie_le`, `length_allTries_le`).
6. The bottom line, for any list of tiles: the query that reads the values of its boxes from the
   trie of its tile (`trieQuery`) returns `queryValue` (`trieQuery_allTries`), and all its walks
   down the trie are safe (`walkOK_allTries`).  The tiles of the product are `tileList`, and
   `tilesBefore` is its part before a tile.

Two ladders lead from the arrays to the paper.
* A query: `trieQuery` adds up `queryTerms` with the values read from the trie; these are the values
  of the dynamic program (`queryTerms_allTries`), with which the sum is `queryValue` on cubes
  (`sum_queryTerms_storedD`), which is `querySum`, the sum of Lemma 28 (`lemma_29_values`, inside
  `Theorem30.correct`), which is the entry `(X * Y) I J` (`Theorem30.query`).
* The value of a box: `boxValue` reads from the trie; it is `dpValueD` on lists of digits
  (`boxValue_eq`), which is `dpValue` on cubes (`dpValueD_digitsC`), which is `Cube.val`
  (`lemma_29_values`).  `lookup_allTries_eq_val` is the whole ladder; no other proof rests on it.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Building the tries -/

/-- A tile, given by the arrays of its two encodings. -/
structure TileEnc where
  encA : List ℤ
  encB : List ℤ

/-- The tries of some tiles in one array: the array, and the addresses of the roots.  The trie of
tile number i has the root number i. -/
structure TrieStore where
  cells : List ℤ
  roots : List ℕ

namespace TrieStore

/-- The address of the root of trie number i, or 0 if there is no such trie. -/
def root (s : TrieStore) (i : ℕ) : ℕ := s.roots.getD i 0

/-- The value stored for the string l in trie number i. -/
def lookup (s : TrieStore) (i : ℕ) (l : List ℕ) : ℤ := trieLookup s.cells (s.root i) l

/-- The tries hold the entries of f, in the sense of `TrieRep`. -/
def Holds (L lo : ℕ) (s : TrieStore) (f : ℕ × List ℕ → Option ℤ) : Prop :=
  TrieRep L lo s.cells s.root f

/-- A new, empty trie behind the others. -/
def new (s : TrieStore) : TrieStore := ⟨trieNew s.cells, s.roots ++ [s.cells.length]⟩













end TrieStore

/-- The value of a box l (the paper's π) with e stars, computed from the array T: for e = 0 "the
product of its two numbers in the encodings"; for e ≥ 1 the sum val(π) = ∑_λ val(π[ℓ ← λ]), where ℓ
is "the highest level at which π has a star", computed "with ten lookups in the trie" of the tile,
which has the given root.  The function looks only at whether e = 0. -/
def boxValue (encA encB T : List ℤ) (root : ℕ) : ℕ → List ℕ → ℤ
  | 0, l => leafProduct encA encB (starsToNines l)
  | _ + 1, l => sumAtLastStar (trieLookup T root) l






/-- "Generating the boxes with e stars and inserting them into the trie": the array after some boxes
with e stars have been inserted into the trie of the tile, which has the given root, each with its
value, computed from the array as it is before the box is inserted. -/
def fillTrie (encA encB : List ℤ) (root e : ℕ) (boxes : List (List ℕ)) (T : List ℤ) : List ℤ :=
  boxes.foldl (fun T l => trieInsert T root l (boxValue encA encB T root e l)) T

/-- "We compute the values of the boxes in increasing order of their number of stars": the array
after the boxes with 0, …, k - 1 stars have been inserted, in this order, into the trie with the
given root. -/
def fillUpTo (encA encB : List ℤ) (L m t root : ℕ) : ℕ → List ℤ → List ℤ
  | 0, T => T
  | k + 1, T => fillTrie encA encB root k (starBoxes L m t k) (fillUpTo encA encB L m t root k T)

/-- The tries s with a new trie that holds the boxes with fewer than k stars. -/
def tileTrieUpTo (encA encB : List ℤ) (L m t : ℕ) (s : TrieStore) (k : ℕ) : TrieStore :=
  { s.new with cells := fillUpTo encA encB L m t s.cells.length k s.new.cells }

/-- Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile".  The trie is added to an array that may hold the tries of
other tiles already: a new root, and then all the boxes, which have at most m - t stars. -/
def tileTrie (encA encB : List ℤ) (L m t : ℕ) (s : TrieStore) : TrieStore :=
  tileTrieUpTo encA encB L m t s (m - t + 1)

/-- The tries of all tiles in one array: the trie of tile number i has the number i.  Cell 0 is left
unused, since the address 0 means: no vertex. -/
def allTries (L m t : ℕ) (tiles : List TileEnc) : TrieStore :=
  tiles.foldl (fun s ab => tileTrie ab.encA ab.encB L m t s) ⟨[0], []⟩

/-- The query of Theorem 30.  For every box of the output string "we look up its value in the trie
of the tile", which has the given root. -/
def trieQuery (m t : ℕ) (encA encB T : List ℤ) (root : ℕ) (w : List ℕ) : ℤ :=
  (queryTerms m t encA encB (trieLookup T root) w).sum



















/-! ## What the tries hold -/

/-- What the tries hold in the middle of tile number i: on top of the entries old, trie number i
holds the boxes with fewer than k stars and the boxes in pre (some boxes with k stars).  The entry
for the key (i, l) is the value `storedD encA encB l` of the dynamic program. -/
def storedUpTo (old : ℕ × List ℕ → Option ℤ) (i : ℕ) (encA encB : List ℤ) (L m t k : ℕ)
    (pre : List (List ℕ)) : ℕ × List ℕ → Option ℤ
  | (n, l) =>
    if n = i ∧ ((starCount l < k ∧ IsBoxDigits L m t l) ∨ l ∈ pre) then
      some (storedD encA encB l)
    else old (n, l)

/-- What the tries of all tiles hold, the third component of the data structure: "for every tile,
the values of all its boxes (the boxes are the same strings in every tile, but their values depend
on the input arrays of the tile)".  Trie number i holds the values of all boxes for tile number i.
The array holds at least these entries (`allTries_rep`, in the sense of `TrieRep`). -/
def storedAll (L m t : ℕ) (tiles : List TileEnc) : ℕ × List ℕ → Option ℤ
  | (n, l) =>
    if IsBoxDigits L m t l then tiles[n]?.map fun ab => storedD ab.encA ab.encB l else none

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L m t : ℕ}








































end



























/-! ## The array represents what it should hold -/

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L lo m t e : ℕ}
  {roots : ℕ → ℕ}































end















section

variable (L m t : ℕ)





















variable {L m t} {tiles : List TileEnc} {i : ℕ}















end

/-! ## Space -/

section

variable (encA encB : List ℤ)















variable (L m t : ℕ)

































end

/-! ## The list of all tiles -/

section

variable {L : ℕ} (nB : ℕ) (encA encB : ℕ → Leaf L → ℤ)

/-- The tiles in row-major order, each given by the arrays of its two encodings: tile (β, β') has
the number β nB + β'. -/
def tileList : List TileEnc :=
  (List.range nB).flatMap fun β => (List.range nB).map fun β' => ⟨arrT (encA β), arrT (encB β')⟩













/-- The tiles before the tile (β, β'), in row-major order. -/
def tilesBefore (β β' : ℕ) : List TileEnc :=
  ((List.range β).flatMap fun b => (List.range nB).map fun b' => ⟨arrT (encA b), arrT (encB b')⟩) ++
    (List.range β').map fun b' => ⟨arrT (encA β), arrT (encB b')⟩

























end

/-! ## What the tries of all tiles give to a query

The query for tile number i gets the root of the trie of this tile. -/

section Query

variable {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
  (hi : tiles[i]? = some ab) {η : OutStr L} (hη : (innerSetO η).card = m)

include ht hi hη














end Query












end ThreeSumApsp.Spec

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Contracts


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 30 in the light language: procedure numbers, time functions, specifications

This file contains no program, and its only proof is a short remark on the trie area when other
cells change. It states the specifications of the procedures 40 to 53 (`nineFirst` to `queryCore`).
The proof of a routine uses only the specifications of the routines that it calls.

* A routine takes its scalars and the base addresses of its arrays as arguments; no routine but
  `preCore` and `queryAt` knows the memory map. The routines for a tile assume the order in which
  their areas lie (`TileCtx.layout`).
* The specification of a routine is a proposition XSpec lim P: "procedure number Proc.x of the
  program P, started on these arguments in a memory that satisfies this, ends within tX steps with
  this result in a memory that satisfies that". The file of x proves XSpec for every program P that
  holds the body of x at the number Proc.x and meets the specifications of the routines that x
  calls. A caller assumes XSpec and feeds it to the rule for calls. XSpec holds at every depth d of
  calls that leaves the levels which x needs below itself.
* Conventions of the programs: the result of a procedure is what it leaves in its local 0; locals
  that are not arguments start at 0. In the proofs, lines such as "have hw := C.std.space_le" or
  "obtain ⟨⟩ := areas p t b0" state the facts on the limits and on the map that the later steps use.
* The larger routines have two records: XArgs holds the arguments and the data behind them, and
  XPre lim μ x says what the routine assumes about the limits and the memory.
* The pure models are those of the specifications of Section 4 (strings are lists of digits, level 1
  first: P_ij is 3(i - 1) + (j - 1), P₀ is 9, the star is 10).
* Time functions are definitions. The time function of a caller is written in terms of the time
  functions of its callees. Their constants are upper bounds, some with room to spare; only the
  shape matters. The lemmas `within8_tAllTiles` and `exists_tQueryCore_le` compare `tAllTiles` and
  `tQueryCore` with the expressions (8) and L ∑ α_d of the paper.
* Tries use addresses relative to the base tr of the trie area: the cell tr + a of the memory is the
  cell a of the trie array T. The area has cap cells, of which the first T.length are in use;
  nothing is assumed about the others (a new vertex clears its eleven cells); the number T.length
  is kept in the cell fp outside the area.

The routines, the pure functions that model them, and the lemmas that say what the models compute:

| number | routine | model | what is proved about the model |
|---|---|---|---|
| 40 | `nineFirst` | `nineFirst` | `head?_nineStrs`: it is the first string of `nineStrs` |
| 41 | `nineNext` | `nineNext` | `nineNext_getElem`: from string i of `nineStrs` to string i + 1 |
| 42 | `scatter` | `scatter`, `starRunIf` | `lowList` and `boxesOf` are built from them |
| 43 | `starFirst` | `starFirst`, `lastStar` | `starBoxes` is `nineStrs` mapped by `starFirst` |
| 44 | `horner` | `ofDigitList 10` | `ofDigitList_digitsT`: the code of a leaf |
| 45 | `lookup` | `trieLookup` | `TrieRep.lookup`, `TrieRep.walkOK` |
| 46 | `insert` | `trieInsert` | `TrieRep.insert`, `TrieRep.insertOK` |
| 47 | `newRoot` | `trieNew` | `TrieRep.new` |
| 48 | `sumTen` | sum of `tenValues` | `exists_lastStar_of_mem_starBoxes`, `abs_dp_partial_sum_le` |
| 49 | `fillList` | `fillTrie` | `fillTrie_rep`, `length_fillTrie_le` |
| 50 | `tile` | `tileTrie` | `fillUpTo_rep`, `length_tileTrie_le` |
| 51 | `allTiles` | `allTries` | `allTries_rep`, `length_allTries_le`, `lookup_allTries` |
| 52 | `outDigits` | `OutDigitsArgs.digits` | `digitsO_outStrOfPos`: the string of a position |
| 53 | `queryCore` | `trieQuery`, `queryTerms` | `trieQuery_allTries`, `abs_query_partial_sum_le` |

The last line of the table continues with `Theorem30.correct`. The model `boxValue` is computed by a
part of `fillList`, which calls `sumTen` for a box with stars.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## Vocabulary -/

/-- The trie area of cap cells from tr: its first cells hold the array T, and the cell fp holds the
length of T. Nothing is assumed about the rest of the area. -/
structure TrieMem (μ : ℕ → ℤ) (tr cap fp : ℕ) (T : List ℤ) : Prop where
  seg : Seg μ tr T
  free : μ fp = T.length
  le_cap : T.length ≤ cap
  fp_out : fp < tr ∨ tr + cap ≤ fp








/-- The memory μ' agrees with μ outside the trie area and the cell fp. -/
abbrev SameOutsideTrie (μ μ' : ℕ → ℤ) (tr cap fp : ℕ) : Prop :=
  SameOn (fun b => Outside tr cap b ∧ b ≠ fp) μ μ'

/-! ## Procedure numbers

The numbers 0 to 39 belong to Section 2, the numbers from 40 on to Section 4. This file fixes 40 to
53; the files of the other routines of Section 4 fix theirs. -/

namespace Proc
/-- The numbers of the fourteen routines, in the order in which they call each other. -/
abbrev nineFirst : ℕ := 40
@[inherit_doc nineFirst] abbrev nineNext : ℕ := 41
@[inherit_doc nineFirst] abbrev scatter : ℕ := 42
@[inherit_doc nineFirst] abbrev starFirst : ℕ := 43
@[inherit_doc nineFirst] abbrev horner : ℕ := 44
@[inherit_doc nineFirst] abbrev lookup : ℕ := 45
@[inherit_doc nineFirst] abbrev insert : ℕ := 46
@[inherit_doc nineFirst] abbrev newRoot : ℕ := 47
@[inherit_doc nineFirst] abbrev sumTen : ℕ := 48
@[inherit_doc nineFirst] abbrev fillList : ℕ := 49
@[inherit_doc nineFirst] abbrev tile : ℕ := 50
@[inherit_doc nineFirst] abbrev allTiles : ℕ := 51
@[inherit_doc nineFirst] abbrev outDigits : ℕ := 52
@[inherit_doc nineFirst] abbrev queryCore : ℕ := 53
end Proc

/-! ## Time functions -/

/-- The routines with one loop over a string of n or L digits: a constant number of steps for each
digit. -/
def tNineFirst (n : ℕ) : ℕ := 30 * n + 30
@[inherit_doc tNineFirst] def tNineNext (n : ℕ) : ℕ := 90 * n + 60
@[inherit_doc tNineFirst] def tScatter (L : ℕ) : ℕ := 60 * L + 30
@[inherit_doc tNineFirst] def tStarFirst (L : ℕ) : ℕ := 50 * L + 30
@[inherit_doc tNineFirst] def tHorner (L : ℕ) : ℕ := 20 * L + 10
@[inherit_doc tNineFirst] def tLookup (L : ℕ) : ℕ := 20 * L + 12
@[inherit_doc tNineFirst] def tInsert (L : ℕ) : ℕ := 220 * L + 20
/-- Eleven cells are cleared. -/
def tNewRoot : ℕ := 160
/-- Ten times: write a digit, look up, add. -/
def tSumTen (L : ℕ) : ℕ := 10 * (tLookup L + 40) + 30
/-- A round for one box: stars, value (both branches are paid for), insertion, next leaf. -/
def tFillRound (L : ℕ) : ℕ :=
  tStarFirst L + tHorner L + tSumTen L + tInsert L + tNineNext L + 116
/-- One box: the test of the loop and a round. -/
def tFillStep (L : ℕ) : ℕ := tFillRound L + 4
/-- The boxes with a given number of stars, cnt of them. -/
def tFillList (L cnt : ℕ) : ℕ := tNineFirst L + cnt * tFillStep L + 60
/-- The trie of a tile: its root, then the boxes with 0, …, m - t stars. -/
def tTile (L m t : ℕ) : ℕ :=
  tNewRoot + ((List.range (m - t + 1)).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
    + 60
/-- All tiles. -/
def tAllTiles (L m t nB : ℕ) : ℕ := nB * (nB * (tTile L m t + 80) + 40) + 30
@[inherit_doc tNineFirst] def tOutDigits (L : ℕ) : ℕ := 70 * L + 40
/-- A query, once the digits of its output string are known. -/
def tQueryCore (L m t : ℕ) : ℕ :=
  2 * tNineFirst m + (lowList m t []).length * (tScatter L + tHorner L + tNineNext m + 90)
    + (boxesOf m t []).length * (tScatter L + tLookup L + tNineNext m + 90) + 120

/-! ## The enumeration of the strings with a bounded number of nines -/

/-- nineFirst(a, n, lo) writes the least string of n digits with lo nines. -/
def NineFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo : ℕ) (μ : ℕ → ℤ), lo ≤ n → a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineFirst d [a, n, lo] μ (tNineFirst n) fun _ μ' =>
      SegN μ' a (nineFirst n lo) ∧ SameOutside μ μ' a n

/-- nineNext(a, n, lo, hi) replaces the string at a by the next one and returns 1, or leaves it and
returns 0 if it is the last one. -/
def NineNextSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l ∈ nineStrs n lo hi →
    a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineNext d [a, n, lo, hi] μ (tNineNext n) fun r μ' =>
      SegN μ' a ((nineNext lo hi l).getD l) ∧ r = (if (nineNext lo hi l).isSome then 1 else 0) ∧
        SameOutside μ μ' a n

/-! ## Strings -/

/-- scatter(w, s, out, L, star) writes at out the string at w with its nines replaced by the digits
of the string at s, whose leading nines are first turned into stars if star = 1. -/
def ScatterSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (w s out L : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ), SegN μ w wl → SegN μ s sl →
    wl.length = L → sl.length = wl.count 9 → Apart out L w L → Apart out L s sl.length →
    w + L < lim.space → s + sl.length < lim.space → out + L < lim.space →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.scatter d [w, s, out, L, if star then 1 else 0] μ (tScatter L) fun _ μ' =>
      SegN μ' out (scatter wl (starRunIf star sl)) ∧ SameOutside μ μ' out L

/-- starFirst(cur, box, L, e) writes at box the string at cur with its first e nines turned into
stars; it returns the position of the last star (0 if e = 0). -/
def StarFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (cur box L e : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ cur l → l.length = L → Apart box L cur L →
    cur + L < lim.space → box + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.starFirst d [cur, box, L, e] μ (tStarFirst L) fun r μ' =>
      SegN μ' box (starFirst e l) ∧ r = ((lastStar (starFirst e l)).getD 0 : ℕ) ∧
        SameOutside μ μ' box L

/-- horner(a, L) returns the number with the L decimal digits at a, most significant first. -/
def HornerSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a L : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l.length = L → (∀ d ∈ l, d < 10) →
    a + L < lim.space →
    (10 : ℤ) ^ L ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.horner d [a, L] μ (tHorner L) fun r μ' => r = (ofDigitList 10 l : ℕ) ∧
      μ' = μ

/-! ## Tries -/

/-- lookup(tr, root, key, L) returns the value stored for the string at key in the trie with the
given root. -/
def LookupSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (tr root key L : ℕ) (T : List ℤ) (kl : List ℕ) (μ : ℕ → ℤ), Seg μ tr T → SegN μ key kl →
    kl.length = L →
    (∀ d ∈ kl, d < 11) → WalkOK T root kl → tr + T.length < lim.space → key + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.lookup d [tr, root, key, L] μ (tLookup L) fun r μ' =>
      r = trieLookup T root kl ∧ μ' = μ

/-- The arguments of insert(tr, root, key, L, val, fp), and the data behind them: the trie area of
cap cells at tr holds the array T, the cell fp holds its length, and the string kl is at key. -/
structure InsertArgs where
  (tr root key L : ℕ) (val : ℤ) (fp : ℕ)
  (cap : ℕ) (T : List ℤ) (kl : List ℕ)

/-- The values of the arguments of `insert`. -/
abbrev InsertArgs.vals (x : InsertArgs) : List ℤ := [x.tr, x.root, x.key, x.L, x.val, x.fp]

/-- What `insert` assumes: the tries and the string are in the memory, the walk down the string is
safe, there is room for one new vertex at each level, the string lies apart from the trie area and
from the free pointer, and everything lies within the memory. -/
structure InsertPre (lim : Limits) (μ : ℕ → ℤ) (x : InsertArgs) : Prop where
  trie : TrieMem μ x.tr x.cap x.fp x.T
  seg : SegN μ x.key x.kl
  len : x.kl.length = x.L
  digits : ∀ d ∈ x.kl, d < 11
  walk : InsertOK x.T x.root x.kl
  room : x.T.length + 11 * x.kl.length ≤ x.cap
  apart : Apart x.key x.kl.length x.tr x.cap := by first
                                                   | omega
                                                   | ( (try have := Light.Std.space_le (by assumption))
                                                       (try have := Light.Std.const_le (by assumption))
                                                       simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  free_out : Outside x.key x.kl.length x.fp := by first
                                                  | omega
                                                  | ( (try have := Light.Std.space_le (by assumption))
                                                      (try have := Light.Std.const_le (by assumption))
                                                      simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  area_in : x.tr + x.cap < lim.space := by first
                                           | omega
                                           | ( (try have := Light.Std.space_le (by assumption))
                                               (try have := Light.Std.const_le (by assumption))
                                               simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  key_in : x.key + x.kl.length < lim.space := by first
                                                 | omega
                                                 | ( (try have := Light.Std.space_le (by assumption))
                                                     (try have := Light.Std.const_le (by assumption))
                                                     simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  free_in : x.fp < lim.space := by first
                                   | omega
                                   | ( (try have := Light.Std.space_le (by assumption))
                                       (try have := Light.Std.const_le (by assumption))
                                       simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

/-- insert(tr, root, key, L, val, fp) stores val for the string at key in the trie with the given
root. A new vertex is taken from the free part of the trie area, and its eleven cells are
cleared. -/
def InsertSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : InsertArgs) (μ : ℕ → ℤ), InsertPre lim μ x →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.insert d x.vals μ (tInsert x.L) fun _ μ' =>
      TrieMem μ' x.tr x.cap x.fp (trieInsert x.T x.root x.kl x.val) ∧
        SameOutsideTrie μ μ' x.tr x.cap x.fp

/-- newRoot(tr, fp) takes a new vertex from the free part of the trie area, clears its eleven cells,
and returns its address. -/
def NewRootSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (tr cap fp : ℕ) (T : List ℤ) (μ : ℕ → ℤ), TrieMem μ tr cap fp T → T.length + 11 ≤ cap →
    tr + cap < lim.space →
    fp < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.newRoot d [tr, fp] μ tNewRoot fun r μ' =>
      r = T.length ∧ TrieMem μ' tr cap fp (trieNew T) ∧ SameOutsideTrie μ μ' tr cap fp

/-! ## The dynamic program of Lemma 29 -/

/-- The arguments of sumTen(tr, root, box, L, p), and the data behind them: the array T of the tries
is at tr, and the string l, which has a star at the position p, is at box. -/
structure SumTenArgs where
  (tr root box L p : ℕ)
  (T : List ℤ) (l : List ℕ)

/-- The values of the arguments of `sumTen`. -/
abbrev SumTenArgs.vals (x : SumTenArgs) : List ℤ := [x.tr, x.root, x.box, x.L, x.p]

/-- The ten values that `sumTen` adds up. -/
abbrev SumTenArgs.values (x : SumTenArgs) : List ℤ := tenValues (trieLookup x.T x.root) x.l x.p

/-- What `sumTen` assumes: the array of the tries and the box, which do not meet and lie within the
memory, the position of the star, that the ten strings are stored, and that the partial sums of
their values fit in a word. -/
structure SumTenPre (lim : Limits) (μ : ℕ → ℤ) (x : SumTenArgs) : Prop where
  area : Seg μ x.tr x.T
  seg : SegN μ x.box x.l
  len : x.l.length = x.L
  star : x.p < x.l.length
  digits : ∀ d ∈ x.l, d < 11
  walk : ∀ d < 10, WalkOK x.T x.root (x.l.set x.p d)
  sums : ∀ j ≤ 10, |(x.values.take j).sum| ≤ lim.word
  apart : Apart x.box x.l.length x.tr x.T.length := by first
                                                       | omega
                                                       | ( (try have := Light.Std.space_le (by assumption))
                                                           (try have := Light.Std.const_le (by assumption))
                                                           simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  area_in : x.tr + x.T.length < lim.space := by first
                                                | omega
                                                | ( (try have := Light.Std.space_le (by assumption))
                                                    (try have := Light.Std.const_le (by assumption))
                                                    simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)
  box_in : x.box + x.l.length < lim.space := by first
                                                | omega
                                                | ( (try have := Light.Std.space_le (by assumption))
                                                    (try have := Light.Std.const_le (by assumption))
                                                    simp [Light.Limits.Addr, abs_le, -abs_mul, ] <;> omega)

/-- sumTen(tr, root, box, L, p) returns the sum of the ten values, looked up in the trie with the
given root, of the strings obtained from the string at box by writing 0, …, 9 at the position p; it
leaves the memory as it was. -/
def SumTenSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : SumTenArgs) (μ : ℕ → ℤ), SumTenPre lim μ x →
    ∀ d, d + 1 ≤ lim.depth → Meets lim P Proc.sumTen d x.vals μ (tSumTen x.L) fun r μ' =>
      r = x.values.sum ∧ μ' = μ

/-- What the routines for a tile assume about their surroundings: the parameters, the two encodings
of the tile and where they are, the trie area, two scratch strings, and the limits. -/
structure TileCtx (lim : Limits) (L m t : ℕ) (encA encB : Leaf L → ℤ)
    (aA aB tr cap fp cur box : ℕ) : Prop where
  std : Std lim
  ht : t ≤ m
  hmL : m ≤ L
  /-- Every value and every partial sum fits in a word. -/
  value_le : ∃ A B : ℤ, (∀ τ, |encA τ| ≤ A) ∧ (∀ τ, |encB τ| ≤ B) ∧ 10 ^ m * (A * B) ≤ lim.word
  pow_le : (10 : ℤ) ^ L ≤ lim.word
  /-- The two encodings, the two scratch strings, the cell fp and the trie area lie in this order,
  and the last cell of the memory lies behind them. -/
  layout : InOrder (lim.space - 1)
    [(aA, 10 ^ L), (aB, 10 ^ L), (cur, L), (box, L), (fp, 1), (tr, cap)]

/-- The memory μ' agrees with μ outside the trie area, the cell fp, and the two scratch strings. -/
abbrev SameOutsideTile (μ μ' : ℕ → ℤ) (L tr cap fp cur box : ℕ) : Prop :=
  SameOn (fun b => Outside tr cap b ∧ b ≠ fp ∧ Outside cur L b ∧ Outside box L b) μ μ'

/-- The arguments of fillList(e, root, aA, aB, tr, fp, cur, box, L, mt), with mt = m - t, and the
data behind them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap
cells at tr holds the array T, and fp holds its length; cur and box (L cells each) are scratch. The
array is described as in `fillTrie_rep`: tile is the number of the trie (the number of the tile),
roots tile its root, old what the other tries hold, and lo the address from which the tries stand
in the array. -/
structure FillListArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box e tile lo : ℕ)
  roots : ℕ → ℕ
  old : ℕ × List ℕ → Option ℤ
  T : List ℤ

namespace FillListArgs

variable (x : FillListArgs)

/-- The root of the trie of the tile. -/
abbrev root : ℕ := x.roots x.tile

/-- The values of the arguments of `fillList`. -/
abbrev vals : List ℤ :=
  [x.e, x.root, x.aA, x.aB, x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)]

/-- The boxes that `fillList` inserts. -/
abbrev boxes : List (List ℕ) := starBoxes x.L x.m x.t x.e

/-- What the tries hold when the boxes in pre have been inserted. -/
abbrev stored (pre : List (List ℕ)) : ℕ × List ℕ → Option ℤ :=
  storedUpTo x.old x.tile (arrT x.encA) (arrT x.encB) x.L x.m x.t x.e pre

end FillListArgs

/-- What `fillList` assumes: the surroundings of a tile, a trie that holds the boxes with fewer
stars, the tries and the two encodings in the memory, and room for L vertices for each box. -/
structure FillListPre (lim : Limits) (μ : ℕ → ℤ) (x : FillListArgs) : Prop where
  ctx : TileCtx lim x.L x.m x.t x.encA x.encB x.aA x.aB x.tr x.cap x.fp x.cur x.box
  stars_le : x.e ≤ x.m - x.t
  root_ne : x.root ≠ 0
  rep : TrieRep x.L x.lo x.T x.roots (x.stored [])
  trie : TrieMem μ x.tr x.cap x.fp x.T
  segA : Seg μ x.aA (arrT x.encA)
  segB : Seg μ x.aB (arrT x.encB)
  room : x.T.length + 11 * x.L * x.boxes.length ≤ x.cap

/-- fillList(e, root, aA, aB, tr, fp, cur, box, L, mt), with mt = m - t, inserts the boxes with e
stars, with their values, into the trie of the tile, which has the given root and holds the boxes
with fewer stars; for e ≥ 1 the values are sums of ten values looked up in it. -/
def FillListSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : FillListArgs) (μ : ℕ → ℤ), FillListPre lim μ x →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.fillList d x.vals μ (tFillList x.L x.boxes.length) fun _ μ' =>
      TrieMem μ' x.tr x.cap x.fp (fillTrie (arrT x.encA) (arrT x.encB) x.root x.e x.boxes x.T) ∧
        SameOutsideTile μ μ' x.L x.tr x.cap x.fp x.cur x.box

/-- The arguments of tile(aA, aB, ra, tr, fp, cur, box, L, mt), with mt = m - t, and the data behind
them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap cells at tr
holds the tries s.cells of the earlier tiles, in which the values old are stored, and fp holds their
length; their roots s.roots, one for each tile, are in the cells from aR, and ra is the address of
the cell behind them; cur and box (L cells each) are scratch; the tries stand in the trie array from
the address lo on. -/
structure TileArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box aR : ℕ)
  s : TrieStore
  old : ℕ × List ℕ → Option ℤ
  lo : ℕ

/-- The trie array and the roots after the trie of the tile has been built. -/
def TileArgs.tries (x : TileArgs) : TrieStore :=
  tileTrie (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s

/-- The number of cells for the roots, the older ones and the new one. -/
def TileArgs.cells (x : TileArgs) : ℕ := x.s.roots.length + 1

/-- The cells that `tile` keeps: those outside the trie area, the cell fp, the two scratch strings
and the cell of the new root. -/
abbrev TileArgs.Kept (x : TileArgs) (b : ℕ) : Prop :=
  Outside x.tr x.cap b ∧ b ≠ x.fp ∧ Outside x.cur x.L b ∧ Outside x.box x.L b ∧
    b ≠ x.aR + x.s.roots.length

/-- What `tile` assumes: the surroundings of a tile, the older tries and roots and the two encodings
in the memory, room for the new trie, and the place of the cells of the roots. -/
structure TilePre (lim : Limits) (μ : ℕ → ℤ) (x : TileArgs) : Prop where
  ctx : TileCtx lim x.L x.m x.t x.encA x.encB x.aA x.aB x.tr x.cap x.fp x.cur x.box
  rep : x.s.Holds x.L x.lo x.old
  trie : TrieMem μ x.tr x.cap x.fp x.s.cells
  roots : SegN μ x.aR x.s.roots
  segA : Seg μ x.aA (arrT x.encA)
  segB : Seg μ x.aB (arrT x.encB)
  room : x.s.cells.length + 11 * (1 + x.L * (boxes x.L x.m x.t).card) ≤ x.cap
  /-- The cells of the roots lie between the cell fp and the trie area. -/
  rootsPlace : x.fp < x.aR ∧ x.aR + x.cells ≤ x.tr

/-- `tile` builds the trie of one tile, with the values of all its boxes, on top of the older tries,
and writes its root into the cell behind the older roots. It changes only the trie area, the cell
fp, the two scratch strings and this cell. -/
def TileSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : TileArgs) (μ : ℕ → ℤ), TilePre lim μ x →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.tile d
      [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ
      (tTile x.L x.m x.t) fun _ μ' =>
        TrieMem μ' x.tr x.cap x.fp x.tries.cells ∧ SegN μ' x.aR x.tries.roots ∧ SameOn x.Kept μ μ'

/-- The arguments of allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt), with T = 10^L and
mt = m - t, and the data behind them: the encodings of the nB row bands from aENCA and of the nB
column bands from aENCB (band β at the offset β 10^L), the cells of the roots from aR (one for each
tile), the trie area of cap cells from tr, the cell fp for its length, and two scratch strings cur
and box. -/
structure AllTilesArgs where
  (L m t nB : ℕ)
  (encA encB : ℕ → Leaf L → ℤ)
  (aENCA aENCB aR tr cap fp cur box : ℕ)

/-- The tries of all tiles, and their roots. -/
def AllTilesArgs.tries (x : AllTilesArgs) : TrieStore :=
  allTries x.L x.m x.t (tileList x.nB x.encA x.encB)

/-- The cells that `allTiles` keeps: those below cur and those behind the trie area. -/
abbrev AllTilesArgs.Kept (x : AllTilesArgs) (b : ℕ) : Prop := b < x.cur ∨ x.tr + x.cap ≤ b

/-- What `allTiles` assumes: the limits, room in the trie area for the tries of all tiles, the order
of the areas, the encodings in the memory, and the trie array [0]. -/
structure AllTilesPre (lim : Limits) (μ : ℕ → ℤ) (x : AllTilesArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  m_le : x.m ≤ x.L
  /-- Every value and every partial sum fits in a word. -/
  value_le : ∃ A B : ℤ, (∀ β τ, |x.encA β τ| ≤ A) ∧ (∀ β τ, |x.encB β τ| ≤ B) ∧
    10 ^ x.m * (A * B) ≤ lim.word
  pow_le : (10 : ℤ) ^ x.L ≤ lim.word
  cap_ge : 1 + x.nB * x.nB * (11 * (1 + x.L * (boxes x.L x.m x.t).card)) ≤ x.cap
  /-- The areas lie in this order, without overlap, below the end of the memory. -/
  order : x.aENCA + x.nB * 10 ^ x.L ≤ x.aENCB ∧ x.aENCB + x.nB * 10 ^ x.L ≤ x.cur ∧
    x.cur + x.L ≤ x.box ∧ x.box + x.L ≤ x.fp ∧ x.fp < x.aR ∧
    x.aR + x.nB * x.nB ≤ x.tr ∧ x.tr + x.cap < lim.space
  segA : ∀ β < x.nB, Seg μ (x.aENCA + β * 10 ^ x.L) (arrT (x.encA β))
  segB : ∀ β < x.nB, Seg μ (x.aENCB + β * 10 ^ x.L) (arrT (x.encB β))
  trie : TrieMem μ x.tr x.cap x.fp [0]

/-- `allTiles` builds the tries of all tiles, starting from the trie array [0], and changes nothing
below cur or behind the trie area. -/
def AllTilesSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : AllTilesArgs) (μ : ℕ → ℤ), AllTilesPre lim μ x →
    ∀ d, d + 4 ≤ lim.depth →
    Meets lim P Proc.allTiles d [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp,
      x.cur, x.box, x.L, (x.m - x.t : ℕ)] μ (tAllTiles x.L x.m x.t x.nB) fun _ μ' =>
        TrieMem μ' x.tr x.cap x.fp x.tries.cells ∧ SegN μ' x.aR x.tries.roots ∧ SameOn x.Kept μ μ'

/-! ## A query -/

/-- The arguments of outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) and the data behind them: gI and gJ
are the numbers of the blocks of I and J within their bands, dI and dJ the addresses of the base-3
digits rI and rJ of their offsets, aMASK the address of the list of the subsets (a mask of L cells
for each), k0 the number of blocks of a band, L the number of levels, m of which belong to a subset,
and wd the address of the result. -/
structure OutDigitsArgs where
  (gI gJ dI dJ aMASK k0 L wd m : ℕ)
  (rI rJ : List ℕ)

namespace OutDigitsArgs

variable (x : OutDigitsArgs)

/-- The mask of the subset of the block product (gI, gJ). -/
def mask : List Bool := unrank x.L x.m (x.gI * x.k0 + x.gJ)

/-- The address of that mask in the list of the subsets. -/
def base : ℕ := x.aMASK + (x.gI * x.k0 + x.gJ) * x.L

/-- The digits of the output string: 9 at the levels of the subset, and elsewhere 3 a + b for the
next digits a of rI and b of rJ. -/
def digits : List ℕ := outDigits x.m x.mask x.rI x.rJ

end OutDigitsArgs

/-- What `outDigits` assumes: the mask of the subset and the digits of the two offsets stand in the
memory, and the L cells from wd are apart from all three. -/
structure OutDigitsPre (lim : Limits) (μ : ℕ → ℤ) (x : OutDigitsArgs) : Prop where
  std : Std lim
  m_le : x.m ≤ x.L
  gI_lt : x.gI < x.k0
  gJ_lt : x.gJ < x.k0
  index_lt : x.gI * x.k0 + x.gJ < x.L.choose x.m
  segMask : SegN μ x.base (x.mask.map fun b => if b then 1 else 0)
  segI : SegN μ x.dI x.rI
  segJ : SegN μ x.dJ x.rJ
  lenI : x.rI.length = x.L - x.m
  lenJ : x.rJ.length = x.L - x.m
  ltI : ∀ a ∈ x.rI, a < 3
  ltJ : ∀ a ∈ x.rJ, a < 3
  apartMask : Apart x.wd x.L x.base x.L
  apartI : Apart x.wd x.L x.dI (x.L - x.m)
  apartJ : Apart x.wd x.L x.dJ (x.L - x.m)
  spaceMasks : x.aMASK + x.k0 * x.k0 * x.L < lim.space
  spaceI : x.dI + x.L < lim.space
  spaceJ : x.dJ + x.L < lim.space
  spaceDest : x.wd + x.L < lim.space

/-- `outDigits` writes the digits of the output string at wd and changes nothing else. -/
def OutDigitsSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : OutDigitsArgs) (μ : ℕ → ℤ), OutDigitsPre lim μ x →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.outDigits d [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd] μ
      (tOutDigits x.L) fun _ μ' => SegN μ' x.wd x.digits ∧ SameOutside μ μ' x.wd x.L

/-- The arguments of queryCore(aA, aB, tr, root, wd, ss, box, L, m, t) and the data behind them: the
encodings encA and encB of the tile are at aA and aB, the trie array T at tr, root is the root of
the trie of the tile, the digits of the output string η are at wd; ss (m cells) and box (L cells)
are scratch. -/
structure QueryCoreArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  η : OutStr L
  (aA aB tr root wd ss box : ℕ)
  T : List ℤ

/-- The numbers that the query adds up, in the order in which it adds them. -/
def QueryCoreArgs.terms (x : QueryCoreArgs) : List ℤ :=
  queryTerms x.m x.t (arrT x.encA) (arrT x.encB) (trieLookup x.T x.root) (digitsO x.η)

/-- What `queryCore` assumes: the data stand in the memory, every box of the query is found in the
trie of the tile, all partial sums fit in a word, and the two scratch strings are apart from each
other and from the data. -/
structure QueryCorePre (lim : Limits) (μ : ℕ → ℤ) (x : QueryCoreArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  card : (innerSetO x.η).card = x.m
  segA : Seg μ x.aA (arrT x.encA)
  segB : Seg μ x.aB (arrT x.encB)
  segT : Seg μ x.tr x.T
  segDigits : SegN μ x.wd (digitsO x.η)
  walk : ∀ l ∈ boxesOf x.m x.t (digitsO x.η), WalkOK x.T x.root l
  sums : ∀ j, |(x.terms.take j).sum| ≤ lim.word
  prod : ∀ τ, |x.encA τ * x.encB τ| ≤ lim.word
  pow : (10 : ℤ) ^ x.L ≤ lim.word
  ss_wd : Apart x.ss x.m x.wd x.L
  box_wd : Apart x.box x.L x.wd x.L
  ss_box : Apart x.ss x.m x.box x.L
  ss_aA : Apart x.ss x.m x.aA (10 ^ x.L)
  ss_aB : Apart x.ss x.m x.aB (10 ^ x.L)
  box_aA : Apart x.box x.L x.aA (10 ^ x.L)
  box_aB : Apart x.box x.L x.aB (10 ^ x.L)
  ss_tr : Apart x.ss x.m x.tr x.T.length
  box_tr : Apart x.box x.L x.tr x.T.length
  aA_lt : x.aA + 10 ^ x.L < lim.space
  aB_lt : x.aB + 10 ^ x.L < lim.space
  tr_lt : x.tr + x.T.length < lim.space
  wd_lt : x.wd + x.L < lim.space
  ss_lt : x.ss + x.m < lim.space
  box_lt : x.box + x.L < lim.space

/-- `queryCore` returns the sum `trieQuery` for the output string whose digits are at wd: the
products at its leaves of order below t, read from the two encodings, and what the trie with the
given root holds for its boxes. This is the sum of Lemma 28 if the trie holds the values of the
boxes (`trieQuery_allTries`). The routine changes only the two scratch strings. -/
def QueryCoreSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : QueryCoreArgs) (μ : ℕ → ℤ), QueryCorePre lim μ x →
    ∀ d, d + 1 ≤ lim.depth →
    Meets lim P Proc.queryCore d [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t] μ
      (tQueryCore x.L x.m x.t) fun r μ' =>
        r = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
          SameOutside2 μ μ' x.ss x.m x.box x.L

end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Memory


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/

/-- The digits of the output string of a query: L cells. -/
def aWD (p : Sec2.Par) (b0 : ℕ) : ℕ := p.sharedEnd b0
/-- Scratch of the preprocessing, the current leaf: L cells. -/
def aCUR (p : Sec2.Par) (b0 : ℕ) : ℕ := aWD p b0 + p.L
/-- Scratch, the current box: L cells. -/
def aBOX (p : Sec2.Par) (b0 : ℕ) : ℕ := aCUR p b0 + p.L
/-- Scratch of a query, the current string on the levels of Q: m cells. -/
def aSS (p : Sec2.Par) (b0 : ℕ) : ℕ := aBOX p b0 + p.L
/-- The cell that holds the length of the trie array. -/
def aFP (p : Sec2.Par) (b0 : ℕ) : ℕ := aSS p b0 + p.m
/-- The roots of the tries: one cell for each tile. -/
def aROOTS (p : Sec2.Par) (b0 : ℕ) : ℕ := aFP p b0 + 1
/-- The trie area. -/
def aTR (p : Sec2.Par) (b0 : ℕ) : ℕ := aROOTS p b0 + p.nB * p.nB
/-- The capacity of the trie area (`Spec.length_allTries_le`). -/
def trieCap (p : Sec2.Par) (t : ℕ) : ℕ :=
  1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card))
/-- The first address behind the block (one cell is left unused, so that every address of the block
is strictly below it). -/
def top (p : Sec2.Par) (t b0 : ℕ) : ℕ := aTR p b0 + trieCap p t + 1

/-! ## Where the areas lie -/

/-- What the routines of Section 4 need of the map: the tables that they read lie one behind the
other between the directory and WD, and the areas of Section 4 behind WD. -/
structure Areas (p : Sec2.Par) (t b0 : ℕ) : Prop where
  dir : b0 + 32 ≤ p.aMASK b0
  mask : p.aMASK b0 + p.KK * p.L = p.aBAND b0
  band : p.aBAND b0 + p.N = p.aBLOCK b0
  block : p.aBLOCK b0 + p.N = p.aDIG3 b0
  dig3 : p.aDIG3 b0 + p.N * p.Lo ≤ p.aENCA b0
  enca : p.aENCA b0 + p.nB * p.T = p.aENCB b0
  encb : p.aENCB b0 + p.nB * p.T ≤ aWD p b0
  cur : aCUR p b0 = aWD p b0 + p.L
  box : aBOX p b0 = aWD p b0 + 2 * p.L
  ss : aSS p b0 = aWD p b0 + 3 * p.L
  fp : aFP p b0 = aWD p b0 + 3 * p.L + p.m
  roots : aROOTS p b0 = aWD p b0 + 3 * p.L + p.m + 1
  tr : aTR p b0 = aROOTS p b0 + p.nB * p.nB
  top : top p t b0 = aTR p b0 + trieCap p t + 1









































/-! ## The directory -/

namespace Dir

/-- The cells of the directory, the first 32 cells of the block, that the routines of Section 4 use.
They hold L, m, L - m, K₀, nB, 10^L, the addresses of the tables MASK, BAND, BLOCK, DIG3 and of the
encodings ENCA, ENCB, the end of the shared block (which is the address of WD), and t. All but the
last are written by the shared stage. -/
abbrev levels : ℕ := 0
@[inherit_doc levels] abbrev inner : ℕ := 1
@[inherit_doc levels] abbrev outer : ℕ := 4
@[inherit_doc levels] abbrev blocks : ℕ := 7
@[inherit_doc levels] abbrev bands : ℕ := 9
@[inherit_doc levels] abbrev leaves : ℕ := 10
@[inherit_doc levels] abbrev mask : ℕ := 21
@[inherit_doc levels] abbrev band : ℕ := 22
@[inherit_doc levels] abbrev block : ℕ := 23
@[inherit_doc levels] abbrev digits : ℕ := 24
@[inherit_doc levels] abbrev encA : ℕ := 26
@[inherit_doc levels] abbrev encB : ℕ := 27
@[inherit_doc levels] abbrev sharedEnd : ℕ := 30
@[inherit_doc levels] abbrev switch : ℕ := 31

end Dir

/-! ## The invariant -/

/-- The encoding of the row band β. -/
def encRow (p : Sec2.Par) (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (β : ℕ) : Leaf p.L → ℤ :=
  encodingL (bandArrayL (stdLayout hmL) X β)

/-- The encoding of the column band β. -/
def encCol (p : Sec2.Par) (hmL : p.m ≤ p.L) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ)
    (β : ℕ) : Leaf p.L → ℤ :=
  encodingR (bandArrayR (stdLayout hmL) Y β)

/-- The tries of all tiles, and their roots. -/
def dsTries (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    TrieStore :=
  allTries p.L p.m t (tileList p.nB (encRow p hmL X) (encCol p hmL Y))

/-- **The block from b0 on holds the data structure for X and Y.** The preprocessing establishes
this, and every query needs it and keeps it. -/
structure DSReady (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (μ : ℕ → ℤ) : Prop where
  shared : Sec2.SharedReady p hmL aX aY b0 X Y μ
  cellT : μ (b0 + 31) = t
  roots : SegN μ (aROOTS p b0) (dsTries p t hmL X Y).roots
  trie : Seg μ (aTR p b0) (dsTries p t hmL X Y).cells

section

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}
























end

/-- The limits that the two routines need: U bounds the entries of X and Y. -/
structure Lim30 (lim : Limits) (p : Sec2.Par) (t b0 : ℕ) (U : ℤ) : Prop where
  std : Std lim
  space : top p t b0 ≤ lim.space
  /-- Every value and every partial sum fits in a word. -/
  value : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ lim.word
  /-- The shared stage can compute the encodings. -/
  enc : 7 ^ (p.L + 1) * U ≤ lim.word
  /-- The shared stage can compute the table of the powers of 10. -/
  pow : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word

/-! ## The two routines that know the map -/

/-- The numbers of the two routines. -/
abbrev Proc.preCore : ℕ := 54
@[inherit_doc Proc.preCore] abbrev Proc.queryAt : ℕ := 55

/-- The time of `queryAt`. -/
def tQueryAt (L m t : ℕ) : ℕ := tOutDigits L + tQueryCore L m t + 400

/-- The time of `preCore`; c is the constant of the shared stage (`Sec2.SharedSpec`). -/
def tPreCore (c : ℕ) (p : Sec2.Par) (t : ℕ) : ℕ :=
  c * Sec2.sharedShape p + tAllTiles p.L p.m t p.nB + 300

/-- queryAt(I, J, b0) returns (XY)[I, J] from the block at b0, of which it changes only cells of the
scratch strings WD to SS. -/
def QueryAtSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (μ : ℕ → ℤ) (I J : Fin p.N),
    t ≤ p.m → Lim30 lim p t b0 U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    DSReady p t hmL aX aY b0 X Y μ →
    ∀ d, d + 2 ≤ lim.depth →
    Meets lim P Proc.queryAt d [(I : ℕ), (J : ℕ), b0] μ (tQueryAt p.L p.m t) fun r μ' =>
      r = (X * Y) I J ∧ DSReady p t hmL aX aY b0 X Y μ' ∧
        SameOutside μ μ' (aWD p b0) (3 * p.L + p.m)

/-- preCore(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on. Nothing is assumed about the content of the block. -/
def PreCoreSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ) (μ : ℕ → ℤ),
    t ≤ p.m → Lim30 lim p t b0 U → (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) →
    MatAt μ aX X → MatAt μ aY Y → aX + p.N * p.D ≤ b0 → aY + p.D * p.N ≤ b0 →
    ∀ d, d + (p.L + 6) ≤ lim.depth →
    Meets lim P Proc.preCore d [p.L, p.m, t, p.N, p.D, aX, aY, b0] μ
      (tPreCore c p t) fun _ μ' =>
      DSReady p t hmL aX aY b0 X Y μ' ∧ SameOutside μ μ' b0 (top p t b0 - b0)

end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Setup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters and map -/

/-- m = ⌈log₄ D⌉. -/
def logFour (D₀ : ℕ) : ℕ := Nat.clog 4 D₀
/-- The address of the padded X. -/
def paddedXAt (fr : ℕ) : ℕ := fr + 3
/-- The address of the padded Y. -/
def paddedYAt (N D₀ fr : ℕ) : ℕ := fr + 3 + N * D (logFour D₀)
/-- The base address of the block of Theorem 30. -/
def blockAt (N D₀ fr : ℕ) : ℕ := fr + 3 + N * D (logFour D₀) + N * D (logFour D₀)
/-! ## The query -/

namespace Query31

/-- The locals of query31 are its arguments I, J, N, D, aX, aY, fr; the answer replaces I. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Size : ℕ := 2
@[inherit_doc Row] abbrev Dim : ℕ := 3
@[inherit_doc Row] abbrev MatX : ℕ := 4
@[inherit_doc Row] abbrev MatY : ℕ := 5
@[inherit_doc Row] abbrev Free : ℕ := 6

end Query31

open Query31 in
/-- query31(I, J, N, D, aX, aY, fr): if the flag is 1, the query of Theorem 30, and otherwise the
inner product. -/
def query31Body : Stmt :=
  .ite ((Light.Cond.eq (M (v Free)) (k 1))) (.call Proc.queryAt [v Row, v Col, M (((Light.Expr.op Light.Op.add) (v Free) (k 1)))] Row)
    (.call Proc.ipAt [v Row, v Col, v Size, v Dim, v MatX, v MatY] Row)


































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Time


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 30 in the light language: the tiles and a query against the expressions (8) and L ∑ α_d

Pure arithmetic. The routines of Section 4 have explicit time functions. This file and the next one
show that, under the hypotheses of Theorem 30 (`Hyp30`), time and space of the preprocessing are at
most a constant times the expression (8), and the time of a query is at most a constant times
L ∑_{d ≤ t} α_d.

`Within8 f` says that f is at most a constant times (8). Such bounds can be added, multiplied by a
number and passed to smaller functions. Four quantities are within (8) by the counts in the proof of
Theorem 30: the number 1, the number 10^L of leaves, the work 10^L + L 7^L for each band, and L for
each box of each tile (`within8_one` to `within8_boxes`); the next file adds a fifth, N (L + 1)
(`within8_N_mul`). Every other function is bounded by a multiple of a sum of these: here the time
for all tiles (`within8_tAllTiles`) and the space of their tries (`within8_trieSpace`). For a query
see `exists_tQueryCore_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The hypotheses of Theorem 30, and what lies within (8) -/

/-- The hypotheses of Theorem 30 on the parameters. -/
structure Hyp30 (p : Sec2.Par) (t : ℕ) : Prop where
  m_pos : 1 ≤ p.m
  L_ge : 10 * p.m ≤ p.L
  t_le : t ≤ p.m
  N_ge : sqrtKN0 p.L p.m ≤ (p.N : ℝ)



























/-- `f = O((8))`: at most a constant times the expression (8), for all parameters that satisfy the
hypotheses of Theorem 30. -/
def Within8 (f : Sec2.Par → ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, Hyp30 p t → (f p t : ℝ) ≤ C * cost8 p.L p.m t p.N

namespace Within8

variable {f g : Sec2.Par → ℕ → ℕ}



















end Within8































/-! ## The tiles -/


















































































/-! ## A query -/



































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Parameters


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Parameters -/

/-- The parameters in the program text: c = a/b > 10, θ = p/q in (0, 0.9), and the threshold m₀ ≥ 1
below which queries compute inner products. -/
structure RatParams where
  a : ℕ
  b : ℕ
  p : ℕ
  q : ℕ
  m₀ : ℕ
  hb : 1 ≤ b
  hq : 1 ≤ q
  hc : 10 * b < a
  hp : 1 ≤ p
  hθ : 10 * p < 9 * q
  hm₀ : 1 ≤ m₀

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-- L = ⌈(a/b) m⌉. -/
def RatParams.L (G : RatParams) (m : ℕ) : ℕ := (G.a * m + G.b - 1) / G.b
/-- t = ⌈(p/q) m⌉. -/
def RatParams.t (G : RatParams) (m : ℕ) : ℕ := (G.p * m + G.q - 1) / G.q

/-- 10 m ≤ L. -/
theorem RatParams.ten_le_L (G : RatParams) (m : ℕ) : 10 * m ≤ G.L m := by
  unfold RatParams.L
  rw [Nat.le_div_iff_mul_le G.hb]
  have h1 : 10 * G.b * m ≤ G.a * m := Nat.mul_le_mul_right _ G.hc.le
  have h2 : 10 * m * G.b = 10 * G.b * m := by ring
  have := G.hb
  omega






























/-- The parameters of Theorem 30. -/
def parOf (G : RatParams) (N D₀ : ℕ) : Sec2.Par := ⟨G.L (logFour D₀), logFour D₀, N⟩
/-- The switching order. -/
def switchOf31 (G : RatParams) (D₀ : ℕ) : ℕ := G.t (logFour D₀)
/-- The hypotheses of Theorem 30 at these parameters. -/
abbrev RatParams.Hyp (G : RatParams) (N D₀ : ℕ) : Prop := Hyp30 (parOf G N D₀) (switchOf31 G D₀)
/-- The cost (8) of the preprocessing of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.preCost (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N
/-- The cost L ∑ α_d of a query of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.queryCost (G : RatParams) (D₀ : ℕ) : ℝ :=
  costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀)
/-- The first address after the block of Theorem 30. -/
abbrev RatParams.blockEnd (G : RatParams) (N D₀ fr : ℕ) : ℕ :=
  top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)
/-- The first address that is not used. -/
def structEnd (G : RatParams) (N D₀ fr : ℕ) : ℕ :=
  if logFour D₀ < G.m₀ then fr + 3 else top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)




































/-- m ≤ L. -/
theorem logFour_le_levels (G : RatParams) (N D₀ : ℕ) : (parOf G N D₀).m ≤ (parOf G N D₀).L := by
  change logFour D₀ ≤ G.L (logFour D₀)
  have := G.ten_le_L (logFour D₀)
  omega

/-- The data structure of Theorem 30 for the padded matrices has been built in the cells after fr.
-/
abbrev Built31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (fr : ℕ) (μ : ℕ → ℤ) : Prop :=
  DSReady (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
    (paddedYAt N D₀ fr) (blockAt N D₀ fr) (padInnerCols (D (logFour D₀)) X)
    (padInnerRows (D (logFour D₀)) Y) μ

/-- **The cells from fr on hold what a query needs.** -/
structure Ready31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  small : logFour D₀ < G.m₀ → μ fr = 0
  large : G.m₀ ≤ logFour D₀ → μ fr = 1 ∧ μ (fr + 1) = blockAt N D₀ fr ∧ Built31 G X Y fr μ

/-- The limits that the two routines need. -/
structure Lim31 (lim : Limits) (G : RatParams) (N D₀ fr : ℕ) (U : ℤ) : Prop where
  std : Std lim
  space : structEnd G N D₀ fr ≤ lim.space
  pow : ((4 ^ logFour D₀ : ℕ) : ℤ) ≤ lim.word
  /-- For the computation of L and t. -/
  mword : ((G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word
  m0word : (G.m₀ : ℤ) ≤ lim.word
  ip : (D₀ : ℤ) * (U * U) ≤ lim.word
  large : G.m₀ ≤ logFour D₀ → Lim30 lim (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) U











/-- **What both routines are given**: matrices X and Y with entries bounded by U, the addresses aX
and aY of their cells, which lie below the free pointer fr, and limits that suffice. -/
structure Input31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) : Prop where
  one_le_D : 1 ≤ D₀
  one_le_N : 1 ≤ N
  lim : Lim31 lim G N D₀ fr U
  absX : ∀ i j, |X i j| ≤ U
  absY : ∀ i j, |Y i j| ≤ U
  belowX : aX + N * D₀ ≤ fr
  belowY : aY + D₀ * N ≤ fr




/-! ## The query: the text is query31Body -/

/-- The time of a query. -/
def tQuery31 (G : RatParams) (D₀ : ℕ) : ℕ :=
  (if logFour D₀ < G.m₀ then tIpAt D₀ else tQueryAt (G.L (logFour D₀)) (logFour D₀)
      (switchOf31 G D₀)) + 20

/-- query31 returns the entry (XY)[I, J], keeps the structure ready, and changes only cells of the
structure behind its first three. -/
def QuerySpec31 (lim : Limits) (P : Program) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N), Input31 lim G X Y aX aY fr U → Ready31 G X Y aX aY fr μ →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
        (tQuery31 G D₀) fun r μ' =>
      r = (X * Y) I J ∧ Ready31 G X Y aX aY fr μ' ∧
          SameOutside μ μ' (fr + 3) (structEnd G N D₀ fr - (fr + 3))






























































/-! ## The preprocessing: text and interface -/

/-- The time of ceilMul: it counts up to ⌈a m / b⌉. -/
def tCeilMul (a m : ℕ) : ℕ := 20 * (a * m) + 40

/-- Procedure number pn returns ⌈a m / b⌉ on the argument m, and changes no cell. -/
def CeilMulSpec (lim : Limits) (P : Program) (pn a b : ℕ) : Prop :=
  ∀ (m : ℕ) (μ : ℕ → ℤ), ((a * m + b : ℕ) : ℤ) ≤ lim.word → ∀ d, d ≤ lim.depth →
    Meets lim P pn d [m] μ (tCeilMul a m) fun r μ' => r = ((a * m + b - 1) / b : ℕ) ∧ μ' = μ

namespace Pre31

/-- The locals of pre31. The first five are its arguments N, D, aX, aY, fr. Then come m, 4^m, L, t,
the addresses of the padded matrices, the base address b0 of the block of Theorem 30, a result that
is not used, and the product N 4^m. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Dim : ℕ := 1
@[inherit_doc Size] abbrev MatX : ℕ := 2
@[inherit_doc Size] abbrev MatY : ℕ := 3
@[inherit_doc Size] abbrev Free : ℕ := 4
@[inherit_doc Size] abbrev Log : ℕ := 5
@[inherit_doc Size] abbrev Padded : ℕ := 6
@[inherit_doc Size] abbrev Levels : ℕ := 7
@[inherit_doc Size] abbrev Switch : ℕ := 8
@[inherit_doc Size] abbrev PadX : ℕ := 9
@[inherit_doc Size] abbrev PadY : ℕ := 10
@[inherit_doc Size] abbrev Block : ℕ := 11
@[inherit_doc Size] abbrev Res : ℕ := 12
@[inherit_doc Size] abbrev Area : ℕ := 13

end Pre31

open Pre31 in
/-- The first part of pre31 for m ≥ m₀: L, t, the addresses, and the padded matrices. -/
def prePad31 : Stmt :=
  (Light.Stmt.seq (.set Padded (M ((Light.Expr.op Light.Op.add) (v Free) (k 2))))
    (Light.Stmt.seq (.call Proc.levels31 [v Log] Levels)
      (Light.Stmt.seq (.call Proc.switch31 [v Log] Switch)
        (Light.Stmt.seq (.set PadX ((Light.Expr.op Light.Op.add) (v Free) (k 3)))
          (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Size) (v Padded)))
            (Light.Stmt.seq (.set PadY ((Light.Expr.op Light.Op.add) (v PadX) (v Area)))
              (Light.Stmt.seq (.set Block ((Light.Expr.op Light.Op.add) (v PadY) (v Area)))
                (Light.Stmt.seq (.call Proc.padX [v Size, v Dim, v Padded, v MatX, v PadX] Res)
                  (Light.Stmt.seq (.call Proc.copy [v MatY, v PadY, (Light.Expr.op Light.Op.mul) (v Dim) (v Size)] Res)
                    (.call Proc.fill
                      [(Light.Expr.op Light.Op.add) (v PadY) ((Light.Expr.op Light.Op.mul) (v Dim) (v Size)),
                        (Light.Expr.op Light.Op.mul) ((Light.Expr.op Light.Op.sub) (v Padded) (v Dim)) (v Size), k 0]
                      Res))))))))))

open Pre31 in
/-- The second part: the preprocessing of Theorem 30, the base address and the flag 1. -/
def preBuild31 : Stmt :=
  (Light.Stmt.seq (.call Proc.preCore [v Levels, v Log, v Switch, v Size, v Padded, v PadX, v PadY, v Block] Res)
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Free) (k 1)) (v Block)) (.store (v Free) (k 1))))

/-- The part of pre31 for m ≥ m₀. -/
def preLarge31 : Stmt := (Light.Stmt.seq prePad31 preBuild31)

open Pre31 in
/-- pre31(N, D, aX, aY, fr): m and 4^m; for m < m₀ the flag 0, for m ≥ m₀ preLarge31. -/
def pre31Body (G : RatParams) : Stmt :=
  (Light.Stmt.seq (.call Proc.log4 [v Dim, (Light.Expr.op Light.Op.add) (v Free) (k 2)] Log)
    (.ite (Light.Cond.lt (v Log) (k G.m₀)) (.store (v Free) (k 0)) preLarge31))

/-- The time of the preprocessing; c is the constant of the shared stage. -/
def tPre31 (c : ℕ) (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 120

/-- pre31 prepares the cells from fr on, about which nothing is assumed, for queries to XY. -/
def PreSpec31 (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ), Input31 lim G X Y aX aY fr U → MatAt μ aX X → MatAt μ aY Y →
    ∀ d, d + (G.L (logFour D₀) + 7) ≤ lim.depth → Meets lim P Proc.pre31 d [N, D₀, aX, aY, fr] μ
        (tPre31 c G N D₀) fun _ μ' =>
      Ready31 G X Y aX aY fr μ' ∧ SameOutside μ μ' fr (structEnd G N D₀ fr - fr)

end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Costs


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Section 4.4: the costs of the programs with rational parameters

Bounds for the time and the space of the preprocessing and for the time of a query. `CostsWithin`
says of two bounds tp and tq that they dominate the two costs of Theorem 30. A quantity that is
bounded for m < m₀ and within a constant times a cost for m ≥ m₀ is then within a constant times the
bound (`exists_le_of_small_of_large`). The overheads are absorbed by the cost expression (8) of
Theorem 30: padding, copying and filling cost O(N 4^m), and N 4^m ≤ N 10^L/(√K N₀), because K N₀ 4^m
≤ 7^L (`N_mul_pow_le_cost8`); computing L and t costs O(L). For m < m₀ everything is bounded by a
constant. This gives the results that the end theorems use: `exists_tPre31_le`,
`exists_tQuery31_le`, `exists_tOffline32_le`, `exists_structEnd_sub_le`, `exists_lim31_depth_le`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

section
variable (G : RatParams)

/-- **The two bounds dominate the two costs**, at the sizes N and D: sizes and bounds are at least
1, D ≤ N, and from the threshold on the hypotheses of Theorem 30 hold and its two cost expressions,
(8) and L ∑ α_d, are at most C tp and C tq. -/
structure CostsWithin (C : ℝ) (N D₀ : ℕ) (tp tq : ℝ) : Prop where
  one_le_N : 1 ≤ N
  one_le_D : 1 ≤ D₀
  D_le_N : D₀ ≤ N
  one_le_pre : 1 ≤ tp
  one_le_query : 1 ≤ tq
  above : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀) ∧
    cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤ C * tp ∧
    costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤ C * tq
































/-! ### The preprocessing -/







































































/-! ### A query -/





























end

































/-! ### Space and the nesting of calls -/


























































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_InnerProduct


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace IpAt

/-- The locals of ipAt. The first six are its arguments I, J, N, D, aX, aY; the answer replaces I.
Then come the index s of the summand, the sum, the address of row I of X, and the address of Y[0,
J]. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Size : ℕ := 2
@[inherit_doc Row] abbrev Dim : ℕ := 3
@[inherit_doc Row] abbrev MatX : ℕ := 4
@[inherit_doc Row] abbrev MatY : ℕ := 5
@[inherit_doc Row] abbrev Pos : ℕ := 6
@[inherit_doc Row] abbrev Sum : ℕ := 7
@[inherit_doc Row] abbrev RowAt : ℕ := 8
@[inherit_doc Row] abbrev ColAt : ℕ := 9

end IpAt

open IpAt in
/-- ipAt(I, J, N, D, aX, aY): the inner product of row I of X and column J of Y. -/
def ipAtBody : Stmt :=
  (Light.Stmt.seq (.set Pos (k 0))
    (Light.Stmt.seq (.set Sum (k 0))
      (Light.Stmt.seq (.set RowAt ((Light.Expr.op Light.Op.add) (v MatX) ((Light.Expr.op Light.Op.mul) (v Row) (v Dim))))
        (Light.Stmt.seq (.set ColAt ((Light.Expr.op Light.Op.add) (v MatY) (v Col)))
          (Light.Stmt.seq
            (.while (Light.Cond.lt (v Pos) (v Dim))
              (Light.Stmt.seq
                (.set Sum
                  ((Light.Expr.op Light.Op.add) (v Sum)
                    ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v RowAt) (v Pos)))
                      (M ((Light.Expr.op Light.Op.add) (v ColAt) ((Light.Expr.op Light.Op.mul) (v Pos) (v Size)))))))
                (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 1)))))
            (.set Row (v Sum)))))))

section
variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)

/-- The first s summands of the inner product. -/
def ipPart (s : ℕ) : ℤ := ∑ i ∈ range s, if h : i < D₀ then X I ⟨i, h⟩ * Y ⟨i, h⟩ J else 0










variable {X Y}

















end






















































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Layout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Section 4.4, the data structure: the two main procedures for the layout of the statements

The input is N, D, X, Y (`ThinPair.input []`), as in the statements of the corollaries; the free
pointer is the first cell after it. The texts `preMain31Body` and `queryMain31Body` serve all
rational parameters c and θ. Each reads N and D, computes the address of Y and the free pointer, and
calls the relocatable routine: `preMain31_meets` for the preprocessing, `queryMain31_meets` for a
query. Between them the memory satisfies `InputReady31`. The relocatable routines enter through
their specifications `PreSpec31` and `QuerySpec31`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The texts -/

namespace Main31

/-- The locals of the two main procedures: the answer, which in a query is at first the row I, and
the column J; then N, D, the product N D, the address of Y, the free pointer, and in the
preprocessing the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Col : ℕ := 1
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Area : ℕ := 4
@[inherit_doc Ans] abbrev MatY : ℕ := 5
@[inherit_doc Ans] abbrev Free : ℕ := 6
@[inherit_doc Ans] abbrev Res : ℕ := 7

end Main31

open Main31 in
/-- The main procedure of the preprocessing: read the sizes, compute the two addresses, call pre31,
answer 1. -/
def preMain31Body : Stmt :=
  (Light.Stmt.seq (.set Size (M (k 0)))
    (Light.Stmt.seq (.set Dim (M (k 1)))
      (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Size) (v Dim)))
        (Light.Stmt.seq (.set MatY ((Light.Expr.op Light.Op.add) (k 2) (v Area)))
          (Light.Stmt.seq (.set Free ((Light.Expr.op Light.Op.add) (v MatY) (v Area)))
            (Light.Stmt.seq (.call Proc.pre31 [v Size, v Dim, k 2, v MatY, v Free] Res) (.set Ans (k 1))))))))

open Main31 in
/-- The main procedure of a query (I, J): the same five assignments, then call query31. -/
def queryMain31Body : Stmt :=
  (Light.Stmt.seq (.set Size (M (k 0)))
    (Light.Stmt.seq (.set Dim (M (k 1)))
      (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Size) (v Dim)))
        (Light.Stmt.seq (.set MatY ((Light.Expr.op Light.Op.add) (k 2) (v Area)))
          (Light.Stmt.seq (.set Free ((Light.Expr.op Light.Op.add) (v MatY) (v Area)))
            (.call Proc.query31 [v Ans, v Col, v Size, v Dim, k 2, v MatY, v Free] Ans))))))




/-! ## What they do -/











































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Offline


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/

/-- The entry (XY)[I, J] for natural numbers I, J (0 outside the matrix). -/
def entryN {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : ℕ) :
    ℤ :=
  if h : I < N ∧ J < N then (X * Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0

namespace Offline32

/-- The locals of offline32. The first ten are its arguments: N, D, the number of positions, a bound
that is not used, the addresses of X, of Y, of the rows and of the columns of the wanted positions
and of the output, and the free pointer. Then come the number of the current position and the result
of a call. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Dim : ℕ := 1
@[inherit_doc Size] abbrev Count : ℕ := 2
@[inherit_doc Size] abbrev MatX : ℕ := 4
@[inherit_doc Size] abbrev MatY : ℕ := 5
@[inherit_doc Size] abbrev Rows : ℕ := 6
@[inherit_doc Size] abbrev Cols : ℕ := 7
@[inherit_doc Size] abbrev Out : ℕ := 8
@[inherit_doc Size] abbrev Free : ℕ := 9
@[inherit_doc Size] abbrev Pos : ℕ := 10
@[inherit_doc Size] abbrev Res : ℕ := 11

end Offline32

open Offline32 in
/-- One round of offline32: ask the query for the current position and store its answer. -/
def offlineAsk32 : Stmt :=
  (Light.Stmt.seq
    (.call Proc.query31
      [M ((Light.Expr.op Light.Op.add) (v Rows) (v Pos)), M ((Light.Expr.op Light.Op.add) (v Cols) (v Pos)), v Size,
        v Dim, v MatX, v MatY, v Free]
      Res)
    (.store ((Light.Expr.op Light.Op.add) (v Out) (v Pos)) (v Res)))

open Offline32 in
/-- offline32(N, D, w, U, x, y, wi, wj, out, fr): preprocess, then ask one query for each wanted
position and store its answer. -/
def offline32Body : Stmt :=
  (Light.Stmt.seq (.call Proc.pre31 [v Size, v Dim, v MatX, v MatY, v Free] Res) (.for Pos (v Count) offlineAsk32))

/-! ## What it does -/

























/-- The time of offline32: the preprocessing, and for each wanted position a query, the reading of
the position and the storing of the answer. -/
def tOffline32 (c : ℕ) (G : RatParams) (N D₀ w : ℕ) : ℕ :=
  tPre31 c G N D₀ + w * (tQuery31 G D₀ + 30) + 20

/-- **Where the input of offline32 stands**, beyond what `Input31` says: the matrices at aX and aY;
the two lists of indices, which are below N, and the output, all below the free pointer; and the
output meets neither the matrices nor the lists. -/
structure OfflineInput32 {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY aI aJ out fr : ℕ) (WI WJ : List ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  rows : SegN μ aI WI
  cols : SegN μ aJ WJ
  length_eq : WJ.length = WI.length
  rows_lt : ∀ I ∈ WI, I < N
  cols_lt : ∀ J ∈ WJ, J < N
  rows_le : aI + WI.length ≤ fr
  cols_le : aJ + WI.length ≤ fr
  out_le : out + WI.length ≤ fr
  out_matX : Apart out WI.length aX (N * D₀)
  out_matY : Apart out WI.length aY (D₀ * N)
  out_rows : Apart out WI.length aI WI.length
  out_cols : Apart out WI.length aJ WI.length

/-- offline32 writes the wanted entries of XY to out. Below fr it changes only the output; nothing
is assumed about the cells from fr on. -/
def OfflineSpec32 (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY aI aJ out fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (U : ℤ) (u : ℤ) (μ : ℕ → ℤ) (WI WJ : List ℕ),
    Input31 lim G X Y aX aY fr U → OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ →
    ∀ d, d + (G.L (logFour D₀) + 8) ≤ lim.depth → Meets lim P Proc.offline32 d
      [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ (tOffline32 c G N D₀ WI.length)
      fun _ μ' => Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
        ∀ a < fr, (a < out ∨ out + WI.length ≤ a) → μ' a = μ a

























































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_OfflineLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Section 4.4, the offline form: the main procedure for the layout of the statements

The input is N, D, |W|, X, Y, the rows of the wanted positions, their columns (the problem
`thinProduct []`); the output follows the input, and the free pointer follows the output. The text
`offlineMain32Body` serves all rational parameters c and θ: it reads the sizes, computes the
addresses of Y, of the two lists of indices and of the output and the free pointer, and calls
offline32 (`offlineMain32_meets`). The input in the statements of the corollaries
(`ThinInstance.input`) is laid out as the procedure expects (`offlineLayout32_input`). offline32
enters through its specification `OfflineSpec32`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam

/-! ## The text -/

namespace OfflineMain32

/-- The locals of offlineMain32: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns and of the output, the free pointer,
and the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Count : ℕ := 4
@[inherit_doc Ans] abbrev Area : ℕ := 5
@[inherit_doc Ans] abbrev MatY : ℕ := 6
@[inherit_doc Ans] abbrev Rows : ℕ := 7
@[inherit_doc Ans] abbrev Cols : ℕ := 8
@[inherit_doc Ans] abbrev Out : ℕ := 9
@[inherit_doc Ans] abbrev Free : ℕ := 10
@[inherit_doc Ans] abbrev Res : ℕ := 11

end OfflineMain32

open OfflineMain32 in
/-- offlineMain32: read the sizes, compute the addresses, call offline32, answer 1. -/
def offlineMain32Body : Stmt :=
  (Light.Stmt.seq (.set Size (M (k 0)))
    (Light.Stmt.seq (.set Dim (M (k 1)))
      (Light.Stmt.seq (.set Count (M (k 2)))
        (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Size) (v Dim)))
          (Light.Stmt.seq (.set MatY ((Light.Expr.op Light.Op.add) (k 3) (v Area)))
            (Light.Stmt.seq (.set Rows ((Light.Expr.op Light.Op.add) (v MatY) (v Area)))
              (Light.Stmt.seq (.set Cols ((Light.Expr.op Light.Op.add) (v Rows) (v Count)))
                (Light.Stmt.seq (.set Out ((Light.Expr.op Light.Op.add) (v Cols) (v Count)))
                  (Light.Stmt.seq (.set Free ((Light.Expr.op Light.Op.add) (v Out) (v Count)))
                    (Light.Stmt.seq
                      (.call Proc.offline32 [v Size, v Dim, v Count, k 0, k 3, v MatY, v Rows, v Cols, v Out, v Free] Res)
                      (.set Ans (k 1))))))))))))














/-! ## What it does -/























































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Pad


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Padding X with zero columns

Proof of Corollary 26: "pad the inner dimension to 4^m < 4D with zero columns of X". Row by row: a
copy of the row and a fill with zeros. The invariant `PadX.Rows` says that the first i rows of the
padded matrix have been written; `PadX.Rows.succ` is what a round does to the memory, and
`padX_meets` the specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace PadX

/-- The local variables of padX: the arguments N, D, D', aX, aX', the row, and a result that is not
used. -/
abbrev Height : ℕ := 0
@[inherit_doc Height] abbrev Width : ℕ := 1
@[inherit_doc Height] abbrev Padded : ℕ := 2
@[inherit_doc Height] abbrev Source : ℕ := 3
@[inherit_doc Height] abbrev Dest : ℕ := 4
@[inherit_doc Height] abbrev Row : ℕ := 5
@[inherit_doc Height] abbrev Unused : ℕ := 6

end PadX

open PadX in
/-- padX(N, D, D', aX, aX'): for each row i, copy its D entries from aX + i D to aX' + i D', and
fill the D' - D cells behind them with zeros. -/
def padXBody : Stmt :=
  .for Row (v Height) (
    (Light.Stmt.seq
      (.call Proc.copy
        [(Light.Expr.op Light.Op.add) (v Source) ((Light.Expr.op Light.Op.mul) (v Row) (v Width)),
          (Light.Expr.op Light.Op.add) (v Dest) ((Light.Expr.op Light.Op.mul) (v Row) (v Padded)), v Width]
        Unused)
      (.call Proc.fill
        [(Light.Expr.op Light.Op.add)
            ((Light.Expr.op Light.Op.add) (v Dest) ((Light.Expr.op Light.Op.mul) (v Row) (v Padded))) (v Width),
          (Light.Expr.op Light.Op.sub) (v Padded) (v Width), k 0]
        Unused)))

namespace PadX

variable {N D₀ D' aX aX' i : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {μ μ' μ₁ μ₂ : ℕ → ℤ}

/-- The memory before row i: the first i rows of the padded matrix stand at aX', and no cell outside
them has changed. -/
def Rows (μ : ℕ → ℤ) (aX' D' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ (r : Fin N) (j : Fin D'), (r : ℕ) < i → μ' (aX' + r * D' + j) = padInnerCols D' X r j) ∧
    SameOutside μ μ' aX' (i * D')



























end PadX








































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Preprocessing


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollaries 26 and 31 in the light language: the preprocessing, with rational parameters

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉". Then the preprocessing of Theorem 30 on the padded matrices; "for
smaller m the corollary again holds trivially".

The routine meets its specification (`pre31_meets`). It computes m and branches. Below the threshold
it writes the flag 0 (`PreInput31.ready_small`). From the threshold on it computes L, t and the
addresses, pads X, and pads Y by a copy and a fill with zeros (`prePad31_ends`,
`matAt_padInnerRows`); then it calls the preprocessing of Theorem 30 and writes the base address and
the flag 1 (`preBuild31_ends`, `PreInput31.ready_large`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## What the routine is given, and what it leaves -/

/-- The routines that the preprocessing calls meet their specifications. -/
structure PreCalls31 (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop where
  log4 : Log4Spec lim P
  levels : CeilMulSpec lim P Proc.levels31 G.a G.b
  switch : CeilMulSpec lim P Proc.switch31 G.p G.q
  padX : PadXSpec lim P
  copy : CopySpec lim P
  fill : FillSpec lim P
  preCore : PreCoreSpec lim P c

/-- What the preprocessing is given: besides what both routines are given, the matrices X and Y
stand at aX and aY. -/
structure PreInput31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) (μ : ℕ → ℤ) : Prop
    extends Input31 lim G X Y aX aY fr U where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y





























/-! ## From the threshold on -/

/-- The areas from the free pointer on: fr, fr + 1, fr + 2 | X' | Y' | the block of Theorem 30 from
b0 on. F = 4^m is the padded inner dimension, and R the number of cells in the zero rows of Y'. -/
structure Areas31 (lim : Limits) (N D₀ fr F R : ℕ) : Prop where
  F_eq : F = D (logFour D₀)
  R_eq : R = (F - D₀) * N
  base : blockAt N D₀ fr = fr + 3 + N * F + N * F
  base_lt : blockAt N D₀ fr < lim.space
  D_le : D₀ ≤ F
  rows : D₀ * N + R = N * F
  F_le : F ≤ N * F











/-- The time of prePad31. -/
def tPrePad31 (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀)) + tCopy (D₀ * N)
    + tFill ((D (logFour D₀) - D₀) * N) + 60

/-- The state after prePad31: the locals hold the parameters and the addresses, the padded matrices
stand at their places, and only cells between fr and b0 have changed. -/
def Padded31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY fr : ℕ) (μ : ℕ → ℤ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [N, D₀, aX, aY, fr, logFour D₀, (D (logFour D₀) : ℕ), (G.L (logFour D₀) : ℕ),
      (G.t (logFour D₀) : ℕ), (paddedXAt fr : ℕ), (paddedYAt N D₀ fr : ℕ), (blockAt N D₀ fr : ℕ), r,
      (N * D (logFour D₀) : ℕ)], μ'⟩ ∧
    MatAt μ' (paddedXAt fr) (padInnerCols (D (logFour D₀)) X) ∧
    MatAt μ' (paddedYAt N D₀ fr) (padInnerRows (D (logFour D₀)) Y) ∧
    SameOutside μ μ' fr (blockAt N D₀ fr - fr)



























































































/-! ## The routine -/










































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_AllTiles


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The tries of all tiles

Proof of Theorem 30, "Preprocessing": "Finally, we compute the values of all the boxes of each of
the at most 4N²/M tiles". The routine `tile` builds the trie of a tile, and this routine calls it
for every tile. The tiles are taken in row-major order. Three pointers move along: the address of
the encoding of the row band, that of the column band, and the cell for the root of the tile. The
text has three parts, one inside the other: one tile (`allTilesStep`), one row of tiles
(`allTilesRow`), all rows (`allTilesBody`). The invariant `AllTiles.Inv` says what the memory holds
before the tile (β, β'); there is one lemma for each part.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace AllTiles

/-- The local variables of `allTiles`: the arguments aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L,
mt; the row band β, the column band β', the cell for the root of the tile, the address of the
encoding of the row band, that of the column band, and a local for a result that is not used. -/
abbrev EncA : ℕ := 0
@[inherit_doc EncA] abbrev EncB : ℕ := 1
@[inherit_doc EncA] abbrev Bands : ℕ := 2
@[inherit_doc EncA] abbrev Leaves : ℕ := 3
@[inherit_doc EncA] abbrev RootTab : ℕ := 4
@[inherit_doc EncA] abbrev Tries : ℕ := 5
@[inherit_doc EncA] abbrev Free : ℕ := 6
@[inherit_doc EncA] abbrev Cur : ℕ := 7
@[inherit_doc EncA] abbrev Box : ℕ := 8
@[inherit_doc EncA] abbrev Levels : ℕ := 9
@[inherit_doc EncA] abbrev Last : ℕ := 10
@[inherit_doc EncA] abbrev RowBand : ℕ := 11
@[inherit_doc EncA] abbrev ColBand : ℕ := 12
@[inherit_doc EncA] abbrev RootPtr : ℕ := 13
@[inherit_doc EncA] abbrev RowEnc : ℕ := 14
@[inherit_doc EncA] abbrev ColEnc : ℕ := 15
@[inherit_doc EncA] abbrev Void : ℕ := 16

end AllTiles

open AllTiles in
/-- One tile, and on to the next column band. -/
def allTilesStep : Stmt :=
  (Light.Stmt.seq (.call Proc.tile [v RowEnc, v ColEnc, v RootPtr, v Tries, v Free, v Cur, v Box, v Levels, v Last] Void)
    (Light.Stmt.seq (.set RootPtr ((Light.Expr.op Light.Op.add) (v RootPtr) (k 1)))
      (Light.Stmt.seq (.set ColEnc ((Light.Expr.op Light.Op.add) (v ColEnc) (v Leaves)))
        (.set ColBand ((Light.Expr.op Light.Op.add) (v ColBand) (k 1))))))

open AllTiles in
/-- One row of tiles, and on to the first tile of the next row band. -/
def allTilesRow : Stmt :=
  (Light.Stmt.seq (.while (Light.Cond.lt (v ColBand) (v Bands)) allTilesStep)
    (Light.Stmt.seq (.set RowEnc ((Light.Expr.op Light.Op.add) (v RowEnc) (v Leaves)))
      (Light.Stmt.seq (.set RowBand ((Light.Expr.op Light.Op.add) (v RowBand) (k 1)))
        (Light.Stmt.seq (.set ColBand (k 0)) (.set ColEnc (v EncB))))))

open AllTiles in
/-- allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt). -/
def allTilesBody : Stmt :=
  (Light.Stmt.seq (.set RowBand (k 0))
    (Light.Stmt.seq (.set ColBand (k 0))
      (Light.Stmt.seq (.set RootPtr (v RootTab))
        (Light.Stmt.seq (.set RowEnc (v EncA))
          (Light.Stmt.seq (.set ColEnc (v EncB))
            (Light.Stmt.seq (.set Void (k 0)) (.while (Light.Cond.lt (v RowBand) (v Bands)) allTilesRow)))))))

namespace AllTiles

/-! ## The invariant and one tile -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : AllTilesArgs} {β β' : ℕ} {σ : State}

/-- The tries and the roots of the tiles before the tile (β, β'). -/
def triesBefore (x : AllTilesArgs) (β β' : ℕ) : TrieStore :=
  allTries x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')

/-- What the memory μ' holds before the tile (β, β'): the tries and the roots of the tiles before
it; nothing below cur or behind the trie area has changed since μ. -/
structure Mem (μ μ' : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp (triesBefore x β β').cells
  roots : SegN μ' x.aR (triesBefore x β β').roots
  same : SameOn x.Kept μ μ'

/-- The state before the tile (β, β'): the three pointers stand at this tile, and the memory is as
Mem says. -/
def Inv (μ : ℕ → ℤ) (x : AllTilesArgs) (β β' : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aENCA, x.aENCB, x.nB, (10 ^ x.L : ℕ), x.aR, x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), β, β', (x.aR + (β * x.nB + β') : ℕ), (x.aENCA + β * 10 ^ x.L : ℕ),
      (x.aENCB + β' * 10 ^ x.L : ℕ), void], μ'⟩ ∧
    Mem μ μ' x β β'

/-- The arguments of the call of `tile` for the tile (β, β'), and the data behind them. -/
def tileArgs (x : AllTilesArgs) (β β' : ℕ) : TileArgs where
  L := x.L
  m := x.m
  t := x.t
  encA := x.encA β
  encB := x.encB β'
  aA := x.aENCA + β * 10 ^ x.L
  aB := x.aENCB + β' * 10 ^ x.L
  tr := x.tr
  cap := x.cap
  fp := x.fp
  cur := x.cur
  box := x.box
  aR := x.aR
  s := triesBefore x β β'
  old := storedAll x.L x.m x.t (tilesBefore x.nB x.encA x.encB β β')
  lo := 1






































































































/-! ## One row, and all rows -/















































end AllTiles





































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_FillList


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The boxes with e stars go into the trie of their tile (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  "We compute the values of the boxes in
increasing order of their number of stars."  This routine handles the boxes with e stars.  It goes
through the leaves with between e and m - t symbols P₀ in lexicographic order.  For each of them it
turns the first e nines into stars, which gives the next box with e stars; computes the value of the
box, for e = 0 as the product of the two encoded numbers at its code and for e ≥ 1 as the sum of the
values of ten boxes with e - 1 stars, looked up in the trie of the tile; and inserts the box with
its value into the trie.

1. The first section is about lists only: `fillAt` is the trie array after the first i boxes, and
   `StarBox` collects what the routine needs to know about a box with stars (`exists_starBox`).
2. `FillListArgs` holds the data of one run, `FillListPre` what the routine assumes, and
   `FillList.Callees` the specifications of the routines that are called.  `FillList.Inv` is the
   invariant of the loop, and `FillList.RoundFacts` what is known in a round once the box has been
   written.  A round is the call of starFirst, the value (`value_zero_spec`, `value_succ_spec`,
   `fillValue_spec`) and the end of the round (`tail_spec`); together they are `round_spec`, and
   `body_spec` is the whole run.  `fillList_spec` is the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The trie array after the first boxes -/

section pure

variable {L m t : ℕ} {encA encB : Leaf L → ℤ} {e tile lo : ℕ} {roots : ℕ → ℕ}
  {old : ℕ × List ℕ → Option ℤ} {T : List ℤ}

/-- The trie array after the first i boxes with e stars. -/
def fillAt (L m t : ℕ) (encA encB : Leaf L → ℤ) (root e : ℕ) (T : List ℤ) (i : ℕ) : List ℤ :=
  fillTrie (arrT encA) (arrT encB) root e ((starBoxes L m t e).take i) T












































/-- What the routine needs to know about a box with e + 1 stars. -/
structure StarBox (L : ℕ) (encA encB : Leaf L → ℤ) (Ti : List ℤ) (root e : ℕ) (bx : List ℕ)
    (bound : ℤ) (p : ℕ) : Prop where
  /-- p is the position of the last star. -/
  last : lastStar bx = some p
  lt : p < L
  /-- The ten strings are stored in the trie. -/
  walk : ∀ d < 10, WalkOK Ti root (bx.set p d)
  /-- The partial sums of their values are bounded. -/
  sums : ∀ j, |((tenValues (trieLookup Ti root) bx p).take j).sum| ≤ bound
  value : boxValue (arrT encA) (arrT encB) Ti root (e + 1) bx
    = (tenValues (trieLookup Ti root) bx p).sum





























end pure

/-! ## The program -/

namespace FillList

/-- The local variables of fillList: the arguments (the number e of stars, the root of the trie of
the tile, the addresses of the two encodings, the base of the trie area, the address of the free
pointer, the addresses of the leaf and of the box, their length, and m - t), whether there is
another leaf, the position of the last star, the value of the box, its code, and results that are
not used. -/
abbrev Stars : ℕ := 0
@[inherit_doc Stars] abbrev Root : ℕ := 1
@[inherit_doc Stars] abbrev EncA : ℕ := 2
@[inherit_doc Stars] abbrev EncB : ℕ := 3
@[inherit_doc Stars] abbrev Area : ℕ := 4
@[inherit_doc Stars] abbrev Free : ℕ := 5
@[inherit_doc Stars] abbrev LeafAt : ℕ := 6
@[inherit_doc Stars] abbrev BoxAt : ℕ := 7
@[inherit_doc Stars] abbrev Len : ℕ := 8
@[inherit_doc Stars] abbrev MaxNines : ℕ := 9
@[inherit_doc Stars] abbrev More : ℕ := 10
@[inherit_doc Stars] abbrev LastStar : ℕ := 11
@[inherit_doc Stars] abbrev Value : ℕ := 12
@[inherit_doc Stars] abbrev Code : ℕ := 13
@[inherit_doc Stars] abbrev Junk : ℕ := 14

end FillList

open FillList

/-- The value of a box without stars: the product of the two encoded numbers at its code. -/
def fillValueZero : Stmt :=
  (Light.Stmt.seq (.call Proc.horner [v BoxAt, v Len] Code)
    (.set Value
      ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v EncA) (v Code)))
        (M ((Light.Expr.op Light.Op.add) (v EncB) (v Code))))))

/-- The value of the box: for a box with stars, the sum of ten values looked up in the trie that is
being filled. -/
def fillValue : Stmt :=
  .ite ((Light.Cond.eq (v Stars) (k 0))) fillValueZero
    (.call Proc.sumTen [v Area, v Root, v BoxAt, v Len, v LastStar] Value)

/-- The end of a round: insert the box with its value, and form the next leaf. -/
def fillTailStmt : Stmt :=
  (Light.Stmt.seq (.call Proc.insert [v Area, v Root, v BoxAt, v Len, v Value, v Free] Junk)
    (.call Proc.nineNext [v LeafAt, v Len, v Stars, v MaxNines] More))

/-- One round: the box of the leaf, its value, the insertion, the next leaf. -/
def fillRound : Stmt :=
  (Light.Stmt.seq (.call Proc.starFirst [v LeafAt, v BoxAt, v Len, v Stars] LastStar)
    (Light.Stmt.seq fillValue fillTailStmt))

/-- fillList(e, root, encA, encB, area, free, leaf, box, len, m - t): start with the least leaf, and
handle one leaf in each round as long as there is another. -/
def fillListBody : Stmt :=
  (Light.Stmt.seq (.call Proc.nineFirst [v LeafAt, v Len, v Stars] Junk)
    (Light.Stmt.seq (.set More (k 1)) (.while (Light.Cond.eq (v More) (k 1)) fillRound)))

namespace FillListArgs

variable (x : FillListArgs)

/-- The leaves that the run goes through. -/
abbrev leaves : List (List ℕ) := nineStrs x.L x.e (x.m - x.t)

/-- The trie array after the first i boxes. -/
abbrev trieAt (i : ℕ) : List ℤ := fillAt x.L x.m x.t x.encA x.encB x.root x.e x.T i

/-- The value that the routine computes for a box, from the trie array Ti. -/
abbrev value (Ti : List ℤ) (bx : List ℕ) : ℤ :=
  boxValue (arrT x.encA) (arrT x.encB) Ti x.root x.e bx

/-- The locals: the ten arguments, and then More, LastStar, Value, Code and Junk. -/
abbrev locals (more star value code junk : ℤ) : ℕ → ℤ :=
  frame [x.e, x.root, x.aA, x.aB, x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ), more, star, value,
    code, junk]

end FillListArgs

namespace FillList

/-- The routines that fillList calls meet their specifications. -/
structure Callees (lim : Limits) (P : Program) : Prop where
  first : NineFirstSpec lim P
  next : NineNextSpec lim P
  star : StarFirstSpec lim P
  horner : HornerSpec lim P
  insert : InsertSpec lim P
  box : SumTenSpec lim P

/-- The memory ν before round number i: leaf number i, if there is one, is at cur; the first i boxes
have been inserted; the two encodings are in place. -/
structure MemInv (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (ν : ℕ → ℤ) : Prop where
  leaf : ∀ h : i < x.leaves.length, SegN ν x.cur x.leaves[i]
  trie : TrieMem ν x.tr x.cap x.fp (x.trieAt i)
  segA : Seg ν x.aA (arrT x.encA)
  segB : Seg ν x.aB (arrT x.encB)
  same : SameOutsideTile μ ν x.L x.tr x.cap x.fp x.cur x.box

/-- The invariant of the loop, before round number i: the arguments are in place, More says whether
there is a leaf number i, and the memory is as `MemInv` says. -/
def Inv (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (σ : State) : Prop :=
  ∃ (star value code junk : ℤ) (ν : ℕ → ℤ),
    σ = ⟨x.locals (if i < x.leaves.length then 1 else 0) star value code junk, ν⟩ ∧ MemInv μ x i ν

/-- What is known in round number i once the box has been written: l is the leaf, Ti the trie array
before the round, ν the memory. -/
structure RoundFacts (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (l : List ℕ) (Ti : List ℤ)
    (ν : ℕ → ℤ) : Prop where
  leaf_mem : l ∈ x.leaves
  box_mem : starFirst x.e l ∈ starBoxes x.L x.m x.t x.e
  /-- nineNext goes to leaf number i + 1. -/
  next : nineNext x.e (x.m - x.t) l = x.leaves[i + 1]?
  /-- The round inserts the box with its value. -/
  succ : x.trieAt (i + 1) = trieInsert Ti x.root (starFirst x.e l) (x.value Ti (starFirst x.e l))
  /-- The trie holds the boxes with fewer stars and the first i boxes with e stars. -/
  rep : TrieRep x.L x.lo Ti x.roots (x.stored ((starBoxes x.L x.m x.t x.e).take i))
  room : Ti.length + 11 * x.L ≤ x.cap
  trie : TrieMem ν x.tr x.cap x.fp Ti
  segA : Seg ν x.aA (arrT x.encA)
  segB : Seg ν x.aB (arrT x.encB)
  leaf : SegN ν x.cur l
  box : SegN ν x.box (starFirst x.e l)
  same : SameOutsideTile μ ν x.L x.tr x.cap x.fp x.cur x.box

section round

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : FillListArgs} {i : ℕ} {l : List ℕ}
  {Ti : List ℤ} {ν : ℕ → ℤ} {more star value code junk : ℤ}
















































































































































































































end round

end FillList










end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Horner


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Horner's rule: the code of a string of decimal digits

horner(a, L) returns the number whose L decimal digits, most significant first, are in the cells
from a.  It is used to index an encoding by a leaf (Section 4.3: "The encodings are indexed by the
leaves (Section 2.4.1) […].  Thus reading the product at a leaf […] takes O(L) operations").

After i rounds the routine holds the number formed by the first i digits (`Horner.Inv`).  One more
digit multiplies it by ten and adds the digit (`ofDigitList_take_succ`), and it stays below 10^L
(`ofDigitList_lt`), which fits in a word.  `horner_spec` is the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

namespace Horner

/-- The local variables of horner: the arguments (the address of the string and its length), the
level, and the number formed so far.  Local 0 also takes the result. -/
abbrev Str : ℕ := 0
@[inherit_doc Str] abbrev Result : ℕ := 0
@[inherit_doc Str] abbrev Len : ℕ := 1
@[inherit_doc Str] abbrev Level : ℕ := 2
@[inherit_doc Str] abbrev Acc : ℕ := 3

/-- Before round i the number formed by the first i digits has been computed.  The memory is not
changed. -/
def Inv (a : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [a, l.length, i, (ofDigitList 10 (l.take i) : ℕ)], μ⟩

end Horner

open Horner in
/-- horner(str, len): multiply by ten and add the next digit, from the most significant digit on. -/
def hornerBody : Stmt :=
  (Light.Stmt.seq (.set Level (k 0))
    (Light.Stmt.seq (.set Acc (k 0))
      (Light.Stmt.seq
        (.while (Light.Cond.lt (v Level) (v Len))
          (Light.Stmt.seq
            (.set Acc
              ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v Acc) (k 10))
                (M ((Light.Expr.op Light.Op.add) (v Str) (v Level)))))
            (.set Level ((Light.Expr.op Light.Op.add) (v Level) (k 1)))))
        (.set Result (v Acc)))))








































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Insert


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Inserting a string into a trie (Lemma 29)

"inserting them into the trie also takes O(L) operations per box, and adds at most L vertices per
box."  New vertices are taken from the end of the part of the trie area that is in use, whose length
is kept in the cell fp.  No routine relies on what the free part of the area holds: the eleven cells
of a new vertex are cleared.  Addresses are relative to the base of the area, so the models are
`Spec.trieNew` and `Spec.trieInsert`.

1. `Ends.clearLoop` is the rule for the loop that clears cells.  `TrieMem.new` and `TrieMem.set`
   say what the trie area holds after a new vertex has been cleared and after a cell has been
   written.
2. `newRoot_spec`: a new vertex as a root.
3. `alloc_spec`: a new vertex as a child.  `Insertion.child` is the array after the test for the
   child, and `Insertion.Progress.step` says that the insertion goes on from the child in that
   array.
4. `insert_spec`: the loop goes down one level in each round (`Insertion.Inv`,
   `Insertion.round_spec`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Clearing cells -/

/-- Writes 0 into the cells from the address in local x up to, and not including, the address in
local y. -/
def clearLoop (x y : ℕ) : Stmt :=
  .while ((Light.Cond.lt (v x) (v y))) (
    (Light.Stmt.seq (.store (v x) (k 0)) (.set x ((Light.Expr.op Light.Op.add) (v x) (k 1)))))

























/-! ## The trie area -/

section

variable {μ μ₁ : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ}

































end

/-! ## A new root -/

namespace NewRoot

/-- The local variables of newRoot: the arguments (the base of the trie area and the address of the
free pointer), the address of the new vertex, and the two ends of its cells in the memory.  Local 0
also takes the result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Free : ℕ := 1
@[inherit_doc Area] abbrev New : ℕ := 2
@[inherit_doc Area] abbrev From : ℕ := 3
@[inherit_doc Area] abbrev Upto : ℕ := 4

end NewRoot

open NewRoot in
/-- newRoot(area, free): take a new vertex from the end of the part in use, clear its cells, move
the free pointer, and return the address of the vertex. -/
def newRootBody : Stmt :=
  (Light.Stmt.seq (.set New (M (v Free)))
    (Light.Stmt.seq (.set From ((Light.Expr.op Light.Op.add) (v Area) (v New)))
      (Light.Stmt.seq (.set Upto ((Light.Expr.op Light.Op.add) (v From) (k 11)))
        (Light.Stmt.seq (clearLoop From Upto)
          (Light.Stmt.seq (.store (v Free) ((Light.Expr.op Light.Op.add) (v New) (k 11))) (.set Result (v New)))))))























/-! ## A new child -/

namespace Insertion

/-- The local variables of insert: the arguments (the base of the trie area, the root, which becomes
the current vertex, the address of the string, its length, the value, the address of the free
pointer), the level, the address of the cell with the pointer to the child, and, for a new vertex,
its address and the two ends of its cells in the memory. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Vertex : ℕ := 1
@[inherit_doc Area] abbrev Key : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Value : ℕ := 4
@[inherit_doc Area] abbrev Free : ℕ := 5
@[inherit_doc Area] abbrev Level : ℕ := 6
@[inherit_doc Area] abbrev Cell : ℕ := 7
@[inherit_doc Area] abbrev New : ℕ := 8
@[inherit_doc Area] abbrev From : ℕ := 9
@[inherit_doc Area] abbrev Upto : ℕ := 10

end Insertion

open Insertion

/-- A new vertex as the child in the current cell. -/
def allocStmt : Stmt :=
  (Light.Stmt.seq (.set New (M (v Free)))
    (Light.Stmt.seq (.store (v Cell) (v New))
      (Light.Stmt.seq (.set From ((Light.Expr.op Light.Op.add) (v Area) (v New)))
        (Light.Stmt.seq (.set Upto ((Light.Expr.op Light.Op.add) (v From) (k 11)))
          (Light.Stmt.seq (clearLoop From Upto) (.store (v Free) ((Light.Expr.op Light.Op.add) (v New) (k 11))))))))

/-- The time of allocStmt. -/
def tAlloc : ℕ := 144
































/-! ## Insertion -/

/-- One round: find the cell with the pointer to the child, make a new child if there is none, and
go down to the child. -/
def insertRound : Stmt :=
  (Light.Stmt.seq
    (.set Cell
      ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Area) (v Vertex))
        (M ((Light.Expr.op Light.Op.add) (v Key) (v Level)))))
    (Light.Stmt.seq (.ite (Light.Cond.eq (M (v Cell)) (k 0)) allocStmt .skip) (.set Vertex (M (v Cell)))))

/-- insert(area, root, key, len, value, free): go down the string, making new children where there
are none, and write the value into the vertex that is reached. -/
def insertBody : Stmt :=
  (Light.Stmt.seq (Stmt.for Level (v Len) insertRound)
    (.store ((Light.Expr.op Light.Op.add) (v Area) (v Vertex)) (v Value)))

namespace Insertion








/-- The array after the test for the child in the cell q: a new vertex has been appended if there
was no child. -/
def child (T : List ℤ) (q : ℕ) : List ℤ :=
  if T.getD q 0 = 0 then trieNew (T.set q T.length) else T

/-- After i levels the array is Ti and the current vertex p: what is left is the insertion of the
rest of the string from p. -/
structure Progress (T : List ℤ) (root : ℕ) (kl : List ℕ) (val : ℤ) (i : ℕ) (Ti : List ℤ) (p : ℕ) :
    Prop where
  ok : InsertOK Ti p (kl.drop i)
  eq : trieInsert T root kl val = trieInsert Ti p (kl.drop i) val
  /-- Each level has added at most one vertex. -/
  len : Ti.length ≤ T.length + 11 * i

section

variable {T Ti : List ℤ} {root i p : ℕ} {kl : List ℕ} {val : ℤ}

































end

/-- Before round i: the area holds an array Ti, the current vertex is p, and what is left is as
`Progress` says; outside the trie area nothing has changed. -/
def Inv (x : InsertArgs) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (Ti : List ℤ) (p : ℕ) (x₇ x₈ x₉ x₁₀ : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.tr, p, x.key, x.kl.length, x.val, x.fp, i, x₇, x₈, x₉, x₁₀], μ'⟩ ∧
      Progress x.T x.root x.kl x.val i Ti p ∧ TrieMem μ' x.tr x.cap x.fp Ti ∧
        SameOutsideTrie μ μ' x.tr x.cap x.fp

section

variable {x : InsertArgs} {i p q : ℕ} {x₇ x₈ x₉ x₁₀ : ℤ} {Ti : List ℤ} {μ μ' : ℕ → ℤ}

/-- The time of a round: the cell, the test, a new vertex, and the step down. -/
def tRound : ℕ := tAlloc + 17

































































end

end Insertion

































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Lookup


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Looking up a string in a trie (Section 4.3)

"looking up or inserting a box, takes O(L) operations": the routine follows the symbols of the box
down from the root.  A vertex is a block of eleven consecutive cells of the trie area, one for each
symbol, holding the address of the child; a vertex at depth L holds the value in its first cell.
Addresses are relative to the base of the area, so the model is `Spec.trieLookup` on the array T
that the area holds.

The loop goes down one level in each round.  Its invariant (`Lookup.Inv`) says that the walk from
the current vertex along the rest of the string ends where the walk from the root along the whole
string ends, and that it stays inside the array (`Spec.WalkOK`); `Lookup.walk_step` says what one
step down does to both facts.  `lookup_spec` is the specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Lookup

/-- The local variables of lookup: the arguments (the base of the trie area, the root, which becomes
the current vertex, the address of the string and its length) and the level.  Local 0 also takes the
result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Vertex : ℕ := 1
@[inherit_doc Area] abbrev Key : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Level : ℕ := 4

end Lookup

open Lookup in
/-- lookup(area, root, key, len): follow the symbols of the string down from the root, and return
the first cell of the vertex that is reached. -/
def lookupBody : Stmt :=
  (Light.Stmt.seq (.set Level (k 0))
    (Light.Stmt.seq
      (.while (Light.Cond.lt (v Level) (v Len))
        (Light.Stmt.seq
          (.set Vertex
            (M
              ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Area) (v Vertex))
                (M ((Light.Expr.op Light.Op.add) (v Key) (v Level))))))
          (.set Level ((Light.Expr.op Light.Op.add) (v Level) (k 1)))))
      (.set Result (M ((Light.Expr.op Light.Op.add) (v Area) (v Vertex))))))

namespace Lookup

variable {T : List ℤ} {kl : List ℕ} {p i : ℕ}










/-- Before round i: the walk from the current vertex p along the rest of the string stays inside the
array and ends where the walk from the root ends.  The memory is not changed. -/
def Inv (tr root key : ℕ) (T : List ℤ) (kl : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ p : ℕ, σ = ⟨frame [tr, p, key, kl.length, i], μ⟩ ∧ WalkOK T p (kl.drop i) ∧
    trieWalk T root kl = trieWalk T p (kl.drop i)

end Lookup







































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_NineFirst


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The least string with a given number of nines

nineFirst(a, n, lo) writes n - lo zeros and then lo nines into the cells from a: the first string of
the enumeration `Spec.nineStrs n lo hi`.  The two loops that write zeros and then nines up to the
end of the string are also the end of nineNext, so they are a statement of their own, `fillTail`.

Each of the two loops writes one digit again and again while a test holds (`fillRun`,
`Ends.fillRun`).  Together they write the least string from the current position on
(`fillTail_spec`), and `nineFirst_spec` is the case of the position 0.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine

/-- The local variables that nineFirst and nineNext share: the address of the string, its length,
the least number of nines, the current position, and the number of nines that are still to be
written.  Local 0 also takes the result. -/
abbrev Str : ℕ := 0
@[inherit_doc Str] abbrev Result : ℕ := 0
@[inherit_doc Str] abbrev Len : ℕ := 1
@[inherit_doc Str] abbrev MinNines : ℕ := 2
@[inherit_doc Str] abbrev Pos : ℕ := 4
@[inherit_doc Str] abbrev Need : ℕ := 10

end Nine

open Nine

/-! ## One digit again and again -/

/-- While the test holds: mem[str + pos] := c; pos := pos + 1. -/
def fillRun (test : Cond) (c : ℕ) : Stmt :=
  .while test (
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Str) (v Pos)) (k c))
      (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 1)))))



































/-! ## Zeros and then nines up to the end of the string -/

/-- Writes zeros from the current position on as long as more than need cells remain, and nines into
the remaining cells. -/
def fillTail : Stmt :=
  (Light.Stmt.seq (fillRun (Light.Cond.lt ((Light.Expr.op Light.Op.add) (v Pos) (v _root_.Light.Sec4.Nine.Need)) (v Len)) 0)
    (fillRun (Light.Cond.lt (v Pos) (v Len)) 9))
































/-! ## The least string -/

/-- nineFirst(str, len, minNines): the least string from the position 0 on. -/
def nineFirstBody : Stmt :=
  (Light.Stmt.seq (.set Pos (k 0)) (Light.Stmt.seq (.set _root_.Light.Sec4.Nine.Need (v MinNines)) fillTail))

















end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_NineNext


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The next string of the enumeration

nineNext(a, n, lo, hi) replaces the string of n digits at a by the next string with between lo and
hi nines (`Spec.nineNext`), and returns 1; if the string is the last one, it leaves it and
returns 0.  This is the step of all three enumerations of Section 4 (proof of Lemma 29: "Generating
the boxes with e stars […] also takes O(L) operations per box"; proof of Theorem 30: "Enumerating
them also takes O(L) operations per number").

There are two passes, as in `Spec.nineNext_eq_scan`.
1. The first pass finds the last position that can be raised and the number of nines before it.  One
   round is `Spec.nineScanStep` (`scanRound_runs`), so after i rounds the locals hold
   `Spec.nineScan hi l i` (`ScanInv`).
2. The second pass computes how many nines are needed behind that position (`needStmt_runs`), raises
   the digit and writes the least admissible filling behind it (`fillTail_spec`).  What stands in
   the memory then is `Spec.raiseAt` (`segN_raiseAt`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine

/-- The further local variables of nineNext: the largest number of nines, the state of the scan
(whether a position that can be raised has been found, the last such position, the number of nines
before it, the number of nines seen so far), and a digit. -/
abbrev MaxNines : ℕ := 3
@[inherit_doc MaxNines] abbrev Found : ℕ := 5
@[inherit_doc MaxNines] abbrev Best : ℕ := 6
@[inherit_doc MaxNines] abbrev Before : ℕ := 7
@[inherit_doc MaxNines] abbrev Nines : ℕ := 8
@[inherit_doc MaxNines] abbrev Digit : ℕ := 9

end Nine

open Nine

/-! ## The first pass -/

/-- Remember the current position and the number of nines before it. -/
def markStmt : Stmt := (Light.Stmt.seq (.set Found (k 1)) (Light.Stmt.seq (.set Best (v Pos)) (.set Before (v Nines))))

/-- If the digit can be raised, remember its position. -/
def raiseTest : Stmt :=
  .ite ((Light.Cond.lt (v Digit) (k 8))) markStmt
    (.ite ((Light.Cond.eq (v Digit) (k 8))) (.ite ((Light.Cond.lt (v Nines) (v MaxNines))) markStmt .skip) .skip)

/-- One round of the scan: read the digit at the current position, remember the position if the
digit can be raised, count the digit if it is a nine, and go on. -/
def scanRound : Stmt :=
  (Light.Stmt.seq (.set Digit (M ((Light.Expr.op Light.Op.add) (v Str) (v Pos))))
    (Light.Stmt.seq raiseTest
      (Light.Stmt.seq
        (.ite (Light.Cond.eq (v Digit) (k 9)) (.set Nines ((Light.Expr.op Light.Op.add) (v Nines) (k 1))) .skip)
        (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 1))))))



/-- The locals during the scan: the arguments, the position i, the state s of the scan, and the
digit read last. -/
def scanFrame (a n lo hi i : ℕ) (s : NineScan) (dg : ℕ) : ℕ → ℤ :=
  frame [a, n, lo, hi, i, s.found, s.pos, s.before, s.nines, dg]




















/-- Before round i the locals hold the state of the scan after i cells.  The memory is not
changed. -/
def ScanInv (a lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ dg : ℕ, σ = ⟨scanFrame a l.length lo hi i (nineScan hi l i) dg, μ⟩

/-! ## The second pass -/

/-- The digit at the position found, and the number of nines that have to be written behind it:
lo - before, less one if the digit becomes a nine, and not below 0. -/
def needStmt : Stmt :=
  (Light.Stmt.seq (.set Digit (M ((Light.Expr.op Light.Op.add) (v Str) (v Best))))
    (Light.Stmt.seq (.set _root_.Light.Sec4.Nine.Need ((Light.Expr.op Light.Op.sub) (v MinNines) (v Before)))
      (Light.Stmt.seq
        (.ite (Light.Cond.eq (v Digit) (k 8)) (.set _root_.Light.Sec4.Nine.Need ((Light.Expr.op Light.Op.sub) (v _root_.Light.Sec4.Nine.Need) (k 1))) .skip)
        (.ite (Light.Cond.lt (v _root_.Light.Sec4.Nine.Need) (k 0)) (.set _root_.Light.Sec4.Nine.Need (k 0)) .skip))))










































/-- The second pass: raise the digit at the position found, and write the least admissible filling
behind it. -/
def raiseStmt : Stmt :=
  (Light.Stmt.seq needStmt
    (Light.Stmt.seq
      (.store ((Light.Expr.op Light.Op.add) (v Str) (v Best)) ((Light.Expr.op Light.Op.add) (v Digit) (k 1)))
      (Light.Stmt.seq (.set Pos ((Light.Expr.op Light.Op.add) (v Best) (k 1)))
        (Light.Stmt.seq fillTail (.set Result (k 1))))))














































/-! ## The routine -/

/-- nineNext(str, len, minNines, maxNines): scan the string; if a position can be raised, write the
next string and return 1, and return 0 if not.  The locals of the scan start at 0. -/
def nineNextBody : Stmt :=
  (Light.Stmt.seq (.set Pos (k 0))
    (Light.Stmt.seq (.while (Light.Cond.lt (v Pos) (v Len)) scanRound)
      (.ite (Light.Cond.eq (v Found) (k 1)) raiseStmt (.set Result (k 0)))))









































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Offline


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}

/-- The invariant of a loop that asks one query after the other and stores the answers ans from the
address out on, before query i.  The memory is Ready for a query, the first i answers are in place,
and the cells in Kept outside these i cells are as in the memory μ at the start. -/
structure Answered (Ready : (ℕ → ℤ) → Prop) (Kept : ℕ → Prop) (out : ℕ) (ans : List ℤ) (μ : ℕ → ℤ)
    (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  ready : Ready μ'
  answers : Seg μ' out (ans.take i)
  same : SameOn (fun a => Outside out i a ∧ Kept a) μ μ'


























end

/-! ## The routine -/

abbrev Proc.wantedCore : ℕ := 56

namespace WantedCore

/-- The locals of wantedCore. The first twelve are its arguments: L, m, t, N, D, the addresses of X,
of Y, of the rows and of the columns of the wanted positions, the number of positions, and the
addresses of the output and of the free block. Then come the number of the current position and the
result of a call. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Inner : ℕ := 1
@[inherit_doc Levels] abbrev Switch : ℕ := 2
@[inherit_doc Levels] abbrev Size : ℕ := 3
@[inherit_doc Levels] abbrev Dim : ℕ := 4
@[inherit_doc Levels] abbrev MatX : ℕ := 5
@[inherit_doc Levels] abbrev MatY : ℕ := 6
@[inherit_doc Levels] abbrev Rows : ℕ := 7
@[inherit_doc Levels] abbrev Cols : ℕ := 8
@[inherit_doc Levels] abbrev Count : ℕ := 9
@[inherit_doc Levels] abbrev Out : ℕ := 10
@[inherit_doc Levels] abbrev Block : ℕ := 11
@[inherit_doc Levels] abbrev Pos : ℕ := 12
@[inherit_doc Levels] abbrev Res : ℕ := 13

end WantedCore

open WantedCore in
/-- One round of wantedCore: ask the query for the current position and store its answer. -/
def wantedAsk : Stmt :=
  (Light.Stmt.seq
    (.call Proc.queryAt
      [M ((Light.Expr.op Light.Op.add) (v Rows) (v Pos)), M ((Light.Expr.op Light.Op.add) (v Cols) (v Pos)), v Block] Res)
    (.store ((Light.Expr.op Light.Op.add) (v Out) (v Pos)) (v Res)))

open WantedCore in
/-- wantedCore(L, m, t, N, D, aX, aY, aI, aJ, w, out, b0): preprocess, then ask one query for each
wanted position and store its answer. -/
def wantedCoreBody : Stmt :=
  (Light.Stmt.seq (.call Proc.preCore [v Levels, v Inner, v Switch, v Size, v Dim, v MatX, v MatY, v Block] Res)
    (.for Pos (v Count) wantedAsk))





section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}


















end






















































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_OfflineLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Theorem 30, the offline form: the main procedure for the trusted layout

The input is N, D, |W|, m, L, t, X, Y, the rows of the wanted positions, their columns (the problem
thinProduct [m, L, t]); the output follows the input, and the block of the data structure follows
the output.  The main procedure wantedMain reads the sizes, computes the six addresses and calls
wantedCore (`wantedMain_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.WordRam



namespace WantedMain

/-- The locals of wantedMain: the answer (the two arguments are not used), then N, D, |W|, the
product N D, the addresses of Y, of the rows, of the columns, of the output and of the block, and
the result of the call. -/
abbrev Ans : ℕ := 0
@[inherit_doc Ans] abbrev Size : ℕ := 2
@[inherit_doc Ans] abbrev Dim : ℕ := 3
@[inherit_doc Ans] abbrev Count : ℕ := 4
@[inherit_doc Ans] abbrev Area : ℕ := 5
@[inherit_doc Ans] abbrev MatY : ℕ := 6
@[inherit_doc Ans] abbrev Rows : ℕ := 7
@[inherit_doc Ans] abbrev Cols : ℕ := 8
@[inherit_doc Ans] abbrev Out : ℕ := 9
@[inherit_doc Ans] abbrev Block : ℕ := 10
@[inherit_doc Ans] abbrev Res : ℕ := 11

end WantedMain

open WantedMain in
/-- wantedMain: read the sizes, compute the addresses, call wantedCore, answer 1. -/
def wantedMainBody : Stmt :=
  (Light.Stmt.seq (.set Size (M (k 0)))
    (Light.Stmt.seq (.set Dim (M (k 1)))
      (Light.Stmt.seq (.set Count (M (k 2)))
        (Light.Stmt.seq (.set Area ((Light.Expr.op Light.Op.mul) (v Size) (v Dim)))
          (Light.Stmt.seq (.set MatY ((Light.Expr.op Light.Op.add) (k 6) (v Area)))
            (Light.Stmt.seq (.set Rows ((Light.Expr.op Light.Op.add) (v MatY) (v Area)))
              (Light.Stmt.seq (.set Cols ((Light.Expr.op Light.Op.add) (v Rows) (v Count)))
                (Light.Stmt.seq (.set Out ((Light.Expr.op Light.Op.add) (v Cols) (v Count)))
                  (Light.Stmt.seq (.set Block ((Light.Expr.op Light.Op.add) (v Out) (v Count)))
                    (Light.Stmt.seq
                      (.call Proc.wantedCore
                        [M (k 4), M (k 3), M (k 5), v Size, v Dim, k 6, v MatY, v Rows, v Cols, v Count, v Out, v Block]
                        Res)
                      (.set Ans (k 1))))))))))))



































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_OutDigits


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The digits of the output string of a position

Proof of Theorem 30, "Query": "Given (I, J), we find its tile from the bands of row I and column J,
the subset Q of its block product, and its output string w (whose variables at the levels outside Q
we read off the row and column of (I, J) within the block product), all in O(L) operations". The
routine walks the mask of the subset: it writes the digit 9 at a level of the subset (levelInner),
and otherwise 3 x + y for the next base-3 digits x and y of the offsets of I and J (levelOuter). The
invariant OutDigits.Inv says what has been written before level l; each of the two branches takes it
from l to l + 1 (OutDigits.inner, OutDigits.outer).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace OutDigits

/-- The local variables of outDigits: the arguments gI, gJ, dI, dJ, aMASK, K0, L, wd, then the
address of the mask of the subset, the level, and the number of levels outside the subset so far. -/
abbrev BlockI : ℕ := 0
@[inherit_doc BlockI] abbrev BlockJ : ℕ := 1
@[inherit_doc BlockI] abbrev DigitsI : ℕ := 2
@[inherit_doc BlockI] abbrev DigitsJ : ℕ := 3
@[inherit_doc BlockI] abbrev Masks : ℕ := 4
@[inherit_doc BlockI] abbrev Blocks : ℕ := 5
@[inherit_doc BlockI] abbrev Levels : ℕ := 6
@[inherit_doc BlockI] abbrev Dest : ℕ := 7
@[inherit_doc BlockI] abbrev Mask : ℕ := 8
@[inherit_doc BlockI] abbrev Level : ℕ := 9
@[inherit_doc BlockI] abbrev Outer : ℕ := 10

end OutDigits

open OutDigits in
/-- A level of the subset: wd[level] := 9; level := level + 1. -/
def levelInner : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Level)) (k 9))
    (.set Level ((Light.Expr.op Light.Op.add) (v Level) (k 1))))

open OutDigits in
/-- A level outside the subset: wd[level] := 3 dI[outer] + dJ[outer]; outer := outer + 1;
level := level + 1. -/
def levelOuter : Stmt :=
  (Light.Stmt.seq
    (.store ((Light.Expr.op Light.Op.add) (v Dest) (v Level))
      ((Light.Expr.op Light.Op.add)
        ((Light.Expr.op Light.Op.mul) (k 3) (M ((Light.Expr.op Light.Op.add) (v DigitsI) (v Outer))))
        (M ((Light.Expr.op Light.Op.add) (v DigitsJ) (v Outer)))))
    (Light.Stmt.seq (.set Outer ((Light.Expr.op Light.Op.add) (v Outer) (k 1)))
      (.set Level ((Light.Expr.op Light.Op.add) (v Level) (k 1)))))

open OutDigits in
/-- The walk along the mask: while level < L, treat the level according to mask[level]. -/
def outDigitsWalk : Stmt :=
  .while ((Light.Cond.lt (v Level) (v Levels))) (.ite ((Light.Cond.eq (M ((Light.Expr.op Light.Op.add) (v Mask) (v Level))) (k 1))) levelInner levelOuter)

open OutDigits in
/-- outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) writes the L digits of the output string at wd. -/
def outDigitsBody : Stmt :=
  (Light.Stmt.seq
    (.set Mask
      ((Light.Expr.op Light.Op.add) (v Masks)
        ((Light.Expr.op Light.Op.mul)
          ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v BlockI) (v Blocks)) (v BlockJ)) (v Levels))))
    (Light.Stmt.seq (.set Level (k 0)) (Light.Stmt.seq (.set Outer (k 0)) outDigitsWalk)))

namespace OutDigits

/-! ## The pure side: the digit at one level -/

variable {lim : Limits} {μ : ℕ → ℤ} {x : OutDigitsArgs} {l : ℕ} {σ : State}






























/-! ## The invariant and the two branches -/

/-- The state before level l: the first l digits have been written, and no cell outside wd has
changed. -/
def Inv (μ : ℕ → ℤ) (x : OutDigitsArgs) (l : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd, x.base, l,
      ((x.mask.take l).count false : ℕ)], μ'⟩ ∧
    SegN μ' x.wd (x.digits.take l) ∧ SameOutside μ μ' x.wd x.L
































































































end OutDigits

























end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Preprocessing


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The preprocessing of Theorem 30, at a given place of the memory

Proof of Theorem 30, "Preprocessing". The routine first runs the stage that it shares with
Theorem 5: the list of the subsets, the tables for the rows and columns, and the encodings of all
row bands and column bands. It notes t in the directory, computes the addresses of the areas of
Section 4 (preCoreAddr), starts the trie area with the array [0], and computes the values of all the
boxes of all tiles, by Lemma 29 (preCoreFinish). There is one lemma for each of the two named parts;
preCore_spec puts them behind the shared stage.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace PreCore

/-- The local variables of preCore: the arguments L, m, t, N, D, aX, aY, b0; a local for results
that are not used; the address of WD, the number nB, the addresses of CUR, BOX, FP, ROOTS, the
number m - t, and the address of TR. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Inner : ℕ := 1
@[inherit_doc Levels] abbrev Switch : ℕ := 2
@[inherit_doc Levels] abbrev Size : ℕ := 3
@[inherit_doc Levels] abbrev Width : ℕ := 4
@[inherit_doc Levels] abbrev MatX : ℕ := 5
@[inherit_doc Levels] abbrev MatY : ℕ := 6
@[inherit_doc Levels] abbrev Base : ℕ := 7
@[inherit_doc Levels] abbrev Void : ℕ := 8
@[inherit_doc Levels] abbrev Digits : ℕ := 9
@[inherit_doc Levels] abbrev Bands : ℕ := 10
@[inherit_doc Levels] abbrev Cur : ℕ := 11
@[inherit_doc Levels] abbrev Box : ℕ := 12
@[inherit_doc Levels] abbrev Free : ℕ := 13
@[inherit_doc Levels] abbrev Roots : ℕ := 14
@[inherit_doc Levels] abbrev Last : ℕ := 15
@[inherit_doc Levels] abbrev Tries : ℕ := 16

end PreCore

open PreCore in
/-- The addresses of the areas of Section 4, which lie one behind the other from WD on. -/
def preCoreAddr : Stmt :=
  (Light.Stmt.seq (.set Digits (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.sharedEnd))))
    (Light.Stmt.seq (.set Bands (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.bands))))
      (Light.Stmt.seq (.set Cur ((Light.Expr.op Light.Op.add) (v Digits) (v Levels)))
        (Light.Stmt.seq (.set Box ((Light.Expr.op Light.Op.add) (v Cur) (v Levels)))
          (Light.Stmt.seq
            (.set Free ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Box) (v Levels)) (v Inner)))
            (Light.Stmt.seq (.set Roots ((Light.Expr.op Light.Op.add) (v Free) (k 1)))
              (Light.Stmt.seq (.set Last ((Light.Expr.op Light.Op.sub) (v Inner) (v Switch)))
                (.set Tries
                  ((Light.Expr.op Light.Op.add) (v Roots) ((Light.Expr.op Light.Op.mul) (v Bands) (v Bands)))))))))))

open PreCore in
/-- The trie array starts as [0], of length 1; then the tries of all tiles. -/
def preCoreFinish : Stmt :=
  (Light.Stmt.seq (.store (v Tries) (k 0))
    (Light.Stmt.seq (.store (v Free) (k 1))
      (.call Proc.allTiles
        [M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.encA)), M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.encB)),
          v Bands, M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.leaves)), v Roots, v Tries, v Free, v Cur, v Box,
          v Levels, v Last]
        Void)))

open PreCore in
/-- preCore(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on. -/
def preCoreBody : Stmt :=
  (Light.Stmt.seq (.call Sec2.pShared [v Levels, v Inner, v Size, v Width, v MatX, v MatY, v Base] Void)
    (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Base) (k Dir.switch)) (v Switch))
      (Light.Stmt.seq preCoreAddr preCoreFinish)))

/-- What the locals hold after the shared stage; r is its result. -/
def preShared (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [p.L, p.m, t, p.N, p.D, aX, aY, b0, r]

/-- What the locals hold after the addresses have been computed. -/
def preLocals (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  preShared p t aX aY b0 r ++ [(aWD p b0 : ℤ), p.nB, aCUR p b0, aBOX p b0, aFP p b0, aROOTS p b0,
    (p.m - t : ℕ), aTR p b0]

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The addresses -/






























/-! ## The tries -/

/-- The arguments of the call of allTiles, and the data behind them. -/
def allArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    AllTilesArgs where
  L := p.L
  m := p.m
  t := t
  nB := p.nB
  encA := encRow p hmL X
  encB := encCol p hmL Y
  aENCA := p.aENCA b0
  aENCB := p.aENCB b0
  aR := aROOTS p b0
  tr := aTR p b0
  cap := trieCap p t
  fp := aFP p b0
  cur := aCUR p b0
  box := aBOX p b0










































































/-! ## The routine -/



























end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Query


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# A query, from the block that holds the data structure (proof of Theorem 30, "Query")

"Given (I, J), we find its tile from the bands of row I and column J, the subset Q of its block
product, and its output string w […], all in O(L) operations". Below, the output string is called η.
queryAt(I, J, b0) has four parts. It reads the sizes, the addresses of the tables and the bands of I
and J from the block at b0 (queryAtReads), computes the addresses of the areas of Section 4
(queryAtAreas), lets outDigits write the digits of η (queryAtOut), reads the root of the trie of the
tile from the table of roots, and lets queryCore compute the sum of Lemma 28 from the two encodings
and this trie (queryAtCore). There is one lemma for each part; for each of the two calls a record
holds the arguments (outArgs, coreArgs) and a lemma says that the block holds what the routine
assumes (outArgs_pre, coreArgs_pre). queryAt_spec puts the four parts together.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace QueryAt

/-- The local variables of queryAt: the arguments I, J, b0; the sizes L, m, t, L - m, K₀, nB, 10^L;
the addresses of the tables BAND, BLOCK, DIG3 and of the area WD; the bands of I and J; the
addresses of the areas BOX, SS, ROOTS, TR; and a local for the result of outDigits, which is not
used. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Base : ℕ := 2
@[inherit_doc Row] abbrev Levels : ℕ := 3
@[inherit_doc Row] abbrev Inner : ℕ := 4
@[inherit_doc Row] abbrev Switch : ℕ := 5
@[inherit_doc Row] abbrev Outer : ℕ := 6
@[inherit_doc Row] abbrev Blocks : ℕ := 7
@[inherit_doc Row] abbrev Bands : ℕ := 8
@[inherit_doc Row] abbrev Leaves : ℕ := 9
@[inherit_doc Row] abbrev BandTab : ℕ := 10
@[inherit_doc Row] abbrev BlockTab : ℕ := 11
@[inherit_doc Row] abbrev DigitTab : ℕ := 12
@[inherit_doc Row] abbrev Digits : ℕ := 13
@[inherit_doc Row] abbrev BandI : ℕ := 14
@[inherit_doc Row] abbrev BandJ : ℕ := 15
@[inherit_doc Row] abbrev Box : ℕ := 16
@[inherit_doc Row] abbrev Str : ℕ := 17
@[inherit_doc Row] abbrev Roots : ℕ := 18
@[inherit_doc Row] abbrev Tries : ℕ := 19
@[inherit_doc Row] abbrev Void : ℕ := 20

end QueryAt

open QueryAt in
/-- The first part of queryAt(I, J, b0): what is read from the directory and from the table BAND. -/
def queryAtReads : Stmt :=
  (Light.Stmt.seq (.set Levels (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.levels))))
    (Light.Stmt.seq (.set Inner (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.inner))))
      (Light.Stmt.seq (.set Switch (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.switch))))
        (Light.Stmt.seq (.set Outer (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.outer))))
          (Light.Stmt.seq (.set Blocks (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.blocks))))
            (Light.Stmt.seq (.set Bands (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.bands))))
              (Light.Stmt.seq (.set Leaves (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.leaves))))
                (Light.Stmt.seq (.set BandTab (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.band))))
                  (Light.Stmt.seq (.set BlockTab (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.block))))
                    (Light.Stmt.seq (.set DigitTab (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.digits))))
                      (Light.Stmt.seq (.set Digits (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.sharedEnd))))
                        (Light.Stmt.seq (.set BandI (M ((Light.Expr.op Light.Op.add) (v BandTab) (v Row))))
                          (.set BandJ (M ((Light.Expr.op Light.Op.add) (v BandTab) (v Col))))))))))))))))

open QueryAt in
/-- The second part: the areas of Section 4 lie one behind the other from WD on. -/
def queryAtAreas : Stmt :=
  (Light.Stmt.seq (.set Box ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Digits) (v Levels)) (v Levels)))
    (Light.Stmt.seq (.set Str ((Light.Expr.op Light.Op.add) (v Box) (v Levels)))
      (Light.Stmt.seq (.set Roots ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.add) (v Str) (v Inner)) (k 1)))
        (.set Tries ((Light.Expr.op Light.Op.add) (v Roots) ((Light.Expr.op Light.Op.mul) (v Bands) (v Bands)))))))

open QueryAt in
/-- The call of outDigits: the digits of the output string. -/
def queryAtOut : Stmt :=
  .call Proc.outDigits [M (((Light.Expr.op Light.Op.add) (v BlockTab) (v Row))), M (((Light.Expr.op Light.Op.add) (v BlockTab) (v Col))),
    ((Light.Expr.op Light.Op.add) (v DigitTab) ((Light.Expr.op Light.Op.mul) (v Row) (v Outer))), ((Light.Expr.op Light.Op.add) (v DigitTab) ((Light.Expr.op Light.Op.mul) (v Col) (v Outer))), M (((Light.Expr.op Light.Op.add) (v Base) (k Dir.mask))),
    v Blocks, v Levels, v Digits] Void

open QueryAt in
/-- The call of queryCore: the sum of Lemma 28. The tile of (I, J) has the number bandI nB + bandJ,
and the root of its trie is read from the table of roots. -/
def queryAtCore : Stmt :=
  .call Proc.queryCore [((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.encA)))
                          ((Light.Expr.op Light.Op.mul) (v BandI) (v Leaves))),
    ((Light.Expr.op Light.Op.add) (M ((Light.Expr.op Light.Op.add) (v Base) (k Dir.encB)))
      ((Light.Expr.op Light.Op.mul) (v BandJ) (v Leaves))), v Tries,
    M (((Light.Expr.op Light.Op.add) (v Roots)
         ((Light.Expr.op Light.Op.add) ((Light.Expr.op Light.Op.mul) (v BandI) (v Bands)) (v BandJ)))), v Digits, v Str, v Box, v Levels, v Inner,
    v Switch] Row

/-- queryAt(I, J, b0) returns (XY)[I, J]: the result of a procedure is its local 0, into which the
last call stores. -/
def queryAtBody : Stmt := (Light.Stmt.seq queryAtReads (Light.Stmt.seq queryAtAreas (Light.Stmt.seq queryAtOut queryAtCore)))

/-- What the locals hold after the first part. -/
def queryAtRead (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  [I, J, b0, p.L, p.m, t, p.Lo, p.K0, p.nB, p.T, p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, aWD p b0,
    (I / (p.K0 * p.N0) : ℕ), (J / (p.K0 * p.N0) : ℕ)]

/-- What the locals hold after the second part. -/
def queryAtLocals (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  queryAtRead p t b0 I J ++ [(aBOX p b0 : ℤ), aSS p b0, aROOTS p b0, aTR p b0]

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first two parts -/























































/-! ## The call of outDigits -/











/-- The arguments of the call of outDigits, and the data behind them. -/
def outArgs (p : Sec2.Par) (b0 I J : ℕ) : OutDigitsArgs :=
  ⟨I / p.N0 % p.K0, J / p.N0 % p.K0, p.aDIG3 b0 + I * p.Lo, p.aDIG3 b0 + J * p.Lo, p.aMASK b0, p.K0,
    p.L, aWD p b0, p.m, digitList 3 p.Lo (I % p.N0), digitList 3 p.Lo (J % p.N0)⟩



































































/-! ## The call of queryCore -/

/-- The number of the tile of the position (I, J). -/
def tileOf (p : Sec2.Par) (I J : ℕ) : ℕ := I / (p.K0 * p.N0) * p.nB + J / (p.K0 * p.N0)

/-- The arguments of the call of queryCore, and the data behind them. -/
def coreArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (I J : ℕ) :
    QueryCoreArgs where
  L := p.L
  m := p.m
  t := t
  encA := encRow p hmL X (I / (p.K0 * p.N0))
  encB := encCol p hmL Y (J / (p.K0 * p.N0))
  η := outStrOfPos (stdLayout hmL) I J
  aA := p.aENCA b0 + I / (p.K0 * p.N0) * p.T
  aB := p.aENCB b0 + J / (p.K0 * p.N0) * p.T
  tr := aTR p b0
  root := (dsTries p t hmL X Y).root (tileOf p I J)
  wd := aWD p b0
  ss := aSS p b0
  box := aBOX p b0
  T := (dsTries p t hmL X Y).cells













section Tile

variable (I J : Fin p.N)












variable (ht : t ≤ p.m)

include ht






























end Tile
















































































/-! ## The routine -/























end Proof

end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_QuerySum


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# A query, once the digits of its output string are known

Proof of Theorem 30, "Query"; these are steps (2) and (3) of the query in Section 4.3. The routine
adds up the sum of Lemma 28: for each leaf of order below t contributing to the output string the
product of its two numbers in the encodings of the tile (queryLowRound), and for each box of the
output string its value (queryBoxRound): "we look up its value in the trie of the tile". The root of
this trie is an argument of the routine.

Leaves and boxes are enumerated through the strings of m digits with a bounded number of nines. For
the boxes the proof of Theorem 30 says "for every V ⊆ Q with |V| = m - t and every box of 𝓑_V". The
routine has one loop (queryBoxes), over the strings with exactly m - t nines: such a string gives V
(the places of its nines) and the box of 𝓑_V (its other digits) at once. This is the other way in
which Section 4.2 describes the boxes of w, "in terms of the leaves of order exactly t contributing
to w. For such a leaf, consider the lowest level of Q at which it chooses a term other than P₀, and
replace its P₀ by a star at every lower level of Q (or at every level of Q, if t = 0). The result is
a box of w, and each box of w arises exactly once in this way" (for cubes:
`existsUnique_starBelow_eq`). The members of the list of the routine are exactly the strings of the
cubes so obtained (`mem_boxesOf_iff`), and a sum over the list is the sum over the sets 𝓑_V
(`sum_boxesOf`). The sets V come interleaved, in the lexicographic order of the strings.

Both loops have one invariant, Query.Inv: the sum of the first terms stands in a local, and the
current string of the enumeration in the scratch area ss. Query.low_term and Query.box_term say
which term a round adds; Query.lowRound and Query.boxRound are the two rounds, Query.loop is either
loop, and queryCore_spec puts the two loops together.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace Query

/-- The local variables of queryCore: the arguments aA, aB, tr, root, wd, ss, box, L, m, t; the sum
so far, whether there is a further string, the code of the leaf (the result of scatter, which is not
used, goes there too), the value of the box, and m - t. -/
abbrev EncA : ℕ := 0
@[inherit_doc EncA] abbrev EncB : ℕ := 1
@[inherit_doc EncA] abbrev Tries : ℕ := 2
@[inherit_doc EncA] abbrev Root : ℕ := 3
@[inherit_doc EncA] abbrev Digits : ℕ := 4
@[inherit_doc EncA] abbrev Str : ℕ := 5
@[inherit_doc EncA] abbrev Box : ℕ := 6
@[inherit_doc EncA] abbrev Levels : ℕ := 7
@[inherit_doc EncA] abbrev Inner : ℕ := 8
@[inherit_doc EncA] abbrev Switch : ℕ := 9
@[inherit_doc EncA] abbrev Sum : ℕ := 10
@[inherit_doc EncA] abbrev More : ℕ := 11
@[inherit_doc EncA] abbrev Code : ℕ := 12
@[inherit_doc EncA] abbrev Value : ℕ := 13
@[inherit_doc EncA] abbrev Nines : ℕ := 14

end Query

open Query in
/-- One round of the first loop: a leaf of order below t. -/
def queryLowRound : Stmt :=
  (Light.Stmt.seq (.call Proc.scatter [v Digits, v Str, v Box, v Levels, k 0] Code)
    (Light.Stmt.seq (.call Proc.horner [v Box, v Levels] Code)
      (Light.Stmt.seq
        (.set Sum
          ((Light.Expr.op Light.Op.add) (v Sum)
            ((Light.Expr.op Light.Op.mul) (M ((Light.Expr.op Light.Op.add) (v EncA) (v Code)))
              (M ((Light.Expr.op Light.Op.add) (v EncB) (v Code))))))
        (.call Proc.nineNext [v Str, v Inner, (Light.Expr.op Light.Op.add) (v Nines) (k 1), v Inner] More))))

open Query in
/-- One round of the second loop: a box, looked up in the trie of the tile. -/
def queryBoxRound : Stmt :=
  (Light.Stmt.seq (.call Proc.scatter [v Digits, v Str, v Box, v Levels, k 1] Code)
    (Light.Stmt.seq (.call Proc.lookup [v Tries, v Root, v Box, v Levels] Value)
      (Light.Stmt.seq (.set Sum ((Light.Expr.op Light.Op.add) (v Sum) (v Value)))
        (.call Proc.nineNext [v Str, v Inner, v Nines, v Nines] More))))

open Query in
/-- The leaves of order below t: the strings with more than m - t nines. -/
def queryLow : Stmt :=
  (Light.Stmt.seq (.call Proc.nineFirst [v Str, v Inner, (Light.Expr.op Light.Op.add) (v Nines) (k 1)] More)
    (Light.Stmt.seq (.set More (k 1)) (.while (Light.Cond.eq (v More) (k 1)) queryLowRound)))

open Query in
/-- The boxes: the strings with exactly m - t nines. -/
def queryBoxes : Stmt :=
  (Light.Stmt.seq (.call Proc.nineFirst [v Str, v Inner, v Nines] More)
    (Light.Stmt.seq (.set More (k 1)) (.while (Light.Cond.eq (v More) (k 1)) queryBoxRound)))

open Query in
/-- queryCore(aA, aB, tr, root, wd, ss, box, L, m, t) returns the sum of Lemma 28. The sum starts
at 0, as all locals that are not arguments; the result of a procedure is its local 0, so the last
statement puts the sum there. -/
def queryCoreBody : Stmt :=
  (Light.Stmt.seq (.set Nines ((Light.Expr.op Light.Op.sub) (v Inner) (v Switch)))
    (Light.Stmt.seq (.ite (Light.Cond.eq (v Switch) (k 0)) .skip queryLow)
      (Light.Stmt.seq queryBoxes (.set EncA (v Sum)))))

namespace Query

/-! ## The pure side: the terms of the sum -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}

/-- The number of leaves of order below t. -/
abbrev lowCount (x : QueryCoreArgs) : ℕ := (nineStrs x.m (x.m - x.t + 1) x.m).length

/-- The number of boxes. -/
abbrev boxCount (x : QueryCoreArgs) : ℕ := (nineStrs x.m (x.m - x.t) (x.m - x.t)).length








/-- The string that round i of the first loop writes at box: a leaf of order below t. -/
def leafAt (x : QueryCoreArgs) (i : ℕ) : List ℕ :=
  scatter (digitsO x.η) (nineStr x.m (x.m - x.t + 1) x.m i)

/-- The string that round i of the second loop writes at box: a box of the output string. -/
def boxAt (x : QueryCoreArgs) (i : ℕ) : List ℕ :=
  scatter (digitsO x.η) (starRunIf true (nineStr x.m (x.m - x.t) (x.m - x.t) i))






































/-! ## The memory and the invariant -/

section Same

variable {μ₁ μ₂ : ℕ → ℤ} {ss m box L a : ℕ} {l : List ℤ}














end Same

/-- The specifications of the routines that queryCore calls. -/
structure Callees (lim : Limits) (P : Program) : Prop where
  nineFirst : NineFirstSpec lim P
  nineNext : NineNextSpec lim P
  scatter : ScatterSpec lim P
  horner : HornerSpec lim P
  lookup : LookupSpec lim P

/-- The state before round i of the loop over the strings with lo to hi nines, when base terms have
been added before the loop: the sum of the first base + i terms stands in the local Sum, the local
More says whether there is a string number i, and this string stands at ss. -/
def Inv (μ : ℕ → ℤ) (x : QueryCoreArgs) (lo hi base i : ℕ) (σ : State) : Prop :=
  ∃ (code value : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t,
      (x.terms.take (base + i)).sum, if i < (nineStrs x.m lo hi).length then 1 else 0, code, value,
      (x.m - x.t : ℕ)], μ'⟩ ∧
    SegN μ' x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ' x.ss x.m x.box x.L

variable {σ : State}








/-! ## The two calls that both rounds make -/

section Calls

variable {lo hi : ℕ} {μ₀ : ℕ → ℤ}





























end Calls

/-! ## The two rounds -/





























































/-! ## The two loops -/
























/-- The state between the loops: the sum of the first n terms stands in the local Sum. -/
def Mid (μ : ℕ → ℤ) (x : QueryCoreArgs) (n : ℕ) (σ : State) : Prop :=
  ∃ (more code value : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t, (x.terms.take n).sum,
      more, code, value, (x.m - x.t : ℕ)], μ'⟩ ∧ SameOutside2 μ μ' x.ss x.m x.box x.L



































































end Query





























end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Scatter


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# A string put at the levels of the inner set

Proof of Theorem 30: a query forms each leaf or box "from the private leaf".  The output string is
the list of its L digits, and the levels of its inner set are the positions of the digit 9.  The
routine copies this list and replaces its digits 9, from the left, by the digits of a second string
(`Spec.scatter`).  If star = 1, the leading digits 9 of the second string (the levels of F_V,
Section 4.2) are written as stars (`Spec.starRunIf`).

One pass, with a pointer into the second string and a flag that says whether the leading run of
nines is still going on.  `Scatter.scatter_step` says what the first digit of
`scatter w (starRunIf flag s)` is and how the rest looks, in terms of the digit, the flag and the
pointer that the program computes (`outDigit`, `nextRun`, `nextPtr`); `Scatter.round_runs` says
that a round of the program computes them.  The invariant (`Scatter.Inv`) is that the digits written
so far, followed by what is still to be written, are the whole string.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Scatter

/-! ## One more digit -/

/-- The digit written at a position where the first string has x and the pointer is at a digit y of
the second string; run = 1 says that the leading run of nines is still going on. -/
def outDigit (x y run : ℕ) : ℕ :=
  if x = 9 then (if y = 9 then (if run = 1 then 10 else 9) else y) else x

/-- The flag after that position: a digit other than 9 of the second string ends the run. -/
def nextRun (x y run : ℕ) : ℕ := if x = 9 ∧ y ≠ 9 then 0 else run

/-- The pointer after that position. -/
def nextPtr (x o : ℕ) : ℕ := if x = 9 then o + 1 else o





















/-- After i positions: the digits written so far, the flag and the pointer. -/
structure Progress (star : Bool) (wl sl : List ℕ) (i run o : ℕ) (done : List ℕ) : Prop where
  length : done.length = i
  /-- The pointer has passed one digit for each nine of the first string. -/
  ptr : o = (wl.take i).count 9
  /-- The digits written, followed by what is still to be written, are the whole string. -/
  rest : done ++ scatter (wl.drop i) (starRunIf (decide (run = 1)) (sl.drop o))
    = scatter wl (starRunIf star sl)





section

variable {star : Bool} {wl sl done : List ℕ} {i run o : ℕ}






















end

/-! ## The program -/

/-- The local variables of scatter: the arguments (the addresses of the two strings and of the
copy, the length, and the flag, whose first value is the argument star), the position, the pointer
into the second string, and the digit to be written. -/
abbrev First : ℕ := 0
@[inherit_doc First] abbrev Second : ℕ := 1
@[inherit_doc First] abbrev Dst : ℕ := 2
@[inherit_doc First] abbrev Len : ℕ := 3
@[inherit_doc First] abbrev Run : ℕ := 4
@[inherit_doc First] abbrev Pos : ℕ := 5
@[inherit_doc First] abbrev Ptr : ℕ := 6
@[inherit_doc First] abbrev Digit : ℕ := 7

end Scatter

open Scatter

/-- One round: read a digit of the first string; if it is a nine, take the next digit of the second
string in its place, as a star if it is a nine of the leading run; write the digit, and go on. -/
def scatterRound : Stmt :=
  (Light.Stmt.seq (.set Digit (M ((Light.Expr.op Light.Op.add) (v First) (v Pos))))
    (Light.Stmt.seq
      (.ite (Light.Cond.eq (v Digit) (k 9))
        (Light.Stmt.seq (.set Digit (M ((Light.Expr.op Light.Op.add) (v Second) (v Ptr))))
          (Light.Stmt.seq (.set Ptr ((Light.Expr.op Light.Op.add) (v Ptr) (k 1)))
            (.ite (Light.Cond.eq (v Digit) (k 9)) (.ite (Light.Cond.eq (v Run) (k 1)) (.set Digit (k 10)) .skip)
              (.set Run (k 0)))))
        .skip)
      (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Pos)) (v Digit))
        (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 1))))))

/-- scatter(first, second, dst, len, star): copy the first string, with the digits of the second
string in place of its nines.  The locals that are not arguments start at 0. -/
def scatterBody : Stmt := .while ((Light.Cond.lt (v Pos) (v Len))) scatterRound

namespace Scatter




























/-- Before round i the first i digits have been written at out. -/
def Inv (w s out : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (run o dg : ℕ) (done : List ℕ),
    σ = ⟨frame [w, s, out, wl.length, run, i, o, dg], μ'⟩ ∧ Progress star wl sl i run o done ∧
      SegN μ' out done ∧ SameOutside μ μ' out wl.length

end Scatter

































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_StarFirst


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The lowest symbols P₀ of a leaf turned into stars

Proof of Lemma 29: "A box in which f of the symbols are P₀ or stars is obtained from a leaf of order
m - f […] by turning the e lowest symbols P₀ of that leaf into stars, for some e ≤ f."  The routine
copies a string of L digits and writes 10 (the star) in place of its first e digits 9
(`Spec.starFirst`).  It returns the position of the last star of the copy, "the highest level at
which π has a star" (proof of Lemma 29), which the dynamic program of Lemma 29 expands
(`Spec.lastStar`).

One pass that keeps two numbers: how many nines have been turned into stars so far, and the
position of the last star so far.  The first section says how one more digit changes the copy and
the two numbers; `StarFirst.round_runs` says that a round of the program does just this;
`StarFirst.Inv` is the invariant of the loop.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One more digit -/












namespace StarFirst

variable {e i : ℕ} {l : List ℕ}

/-- The number of nines among the first i digits that are turned into stars. -/
def turned (e : ℕ) (l : List ℕ) (i : ℕ) : ℕ := min e ((l.take i).count 9)

/-- The position of the last star among the first i digits of the copy (0 if there is none). -/
def lastPos (e : ℕ) (l : List ℕ) (i : ℕ) : ℕ := (lastStar ((starFirst e l).take i)).getD 0
























/-! ## The program -/

/-- The local variables of starFirst: the arguments (the address of the string, the address of the
copy, the length, the number of stars), the position, the position of the last star so far, the
digit, and the number of nines turned into stars so far.  Local 0 also takes the result. -/
abbrev Src : ℕ := 0
@[inherit_doc Src] abbrev Result : ℕ := 0
@[inherit_doc Src] abbrev Dst : ℕ := 1
@[inherit_doc Src] abbrev Len : ℕ := 2
@[inherit_doc Src] abbrev Stars : ℕ := 3
@[inherit_doc Src] abbrev Pos : ℕ := 4
@[inherit_doc Src] abbrev Last : ℕ := 5
@[inherit_doc Src] abbrev Digit : ℕ := 6
@[inherit_doc Src] abbrev Turned : ℕ := 7

end StarFirst

open StarFirst

/-- One round: read a digit, turn it into a star if it is one of the first e nines, remember the
position if a star is written, write the digit, and go on. -/
def starFirstRound : Stmt :=
  (Light.Stmt.seq (.set Digit (M ((Light.Expr.op Light.Op.add) (v Src) (v Pos))))
    (Light.Stmt.seq
      (.ite (Light.Cond.eq (v Digit) (k 9))
        (.ite (Light.Cond.lt (v Turned) (v Stars))
          (Light.Stmt.seq (.set Digit (k 10)) (.set Turned ((Light.Expr.op Light.Op.add) (v Turned) (k 1)))) .skip)
        .skip)
      (Light.Stmt.seq (.ite (Light.Cond.eq (v Digit) (k 10)) (.set Last (v Pos)) .skip)
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Dst) (v Pos)) (v Digit))
          (.set Pos ((Light.Expr.op Light.Op.add) (v Pos) (k 1)))))))

/-- starFirst(src, dst, len, stars): copy the string, with its first nines as stars, and return the
position of the last star.  The locals that are not arguments start at 0. -/
def starFirstBody : Stmt :=
  (Light.Stmt.seq (.while (Light.Cond.lt (v Pos) (v Len)) starFirstRound) (.set Result (v Last)))

namespace StarFirst

























/-- Before round i the first i digits of the copy have been written, and the two counters are up to
date. -/
def Inv (cur box e : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (dg : ℕ),
    σ = ⟨frame [cur, box, l.length, e, i, lastPos e l i, dg, turned e l i], μ'⟩ ∧
      SegN μ' box ((starFirst e l).take i) ∧ SameOutside μ μ' box l.length

end StarFirst








































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_SumTen


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The value of a box with stars (proof of Lemma 29, "The values")

"For a box π with e ≥ 1 stars, let ℓ be the highest level at which π has a star.  The leaves of π
are the leaves of the ten strings π[ℓ ← λ] obtained by replacing that star by a term λ, and each of
these strings is again a box, with e - 1 stars. […] Hence we compute val(π) = ∑_λ val(π[ℓ ← λ]) with
ten lookups in the trie, in O(L) operations."  The routine writes the ten digits one after the other
at the position of the star, looks each string up, adds, and puts the star back.  It looks in the
trie of the tile, which is being filled.

Before round j the sum of the first j values has been formed, and the memory differs from the
original one at the position of the star only (`SumTen.Inv`).  `SumTenPre` collects what the
routine assumes.  In a round the string with the digit j at the position of the star stands in the
memory (`segN_set`), so lookup returns its value (`SumTen.round_spec`); `sumTen_spec` is the
specification.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace SumTen

/-- The local variables of sumTen: the arguments (the base of the trie area, the root of the trie,
the address of the box, its length, the position of the star), the digit that stood at that
position, the digit written, the sum, and a value looked up.  Local 0 also takes the result. -/
abbrev Area : ℕ := 0
@[inherit_doc Area] abbrev Result : ℕ := 0
@[inherit_doc Area] abbrev Root : ℕ := 1
@[inherit_doc Area] abbrev Box : ℕ := 2
@[inherit_doc Area] abbrev Len : ℕ := 3
@[inherit_doc Area] abbrev Star : ℕ := 4
@[inherit_doc Area] abbrev Saved : ℕ := 5
@[inherit_doc Area] abbrev Digit : ℕ := 6
@[inherit_doc Area] abbrev Sum : ℕ := 7
@[inherit_doc Area] abbrev Val : ℕ := 8

end SumTen

open SumTen in
/-- One round: write the digit at the position of the star, look the string up, and add. -/
def sumTenRound : Stmt :=
  (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Box) (v Star)) (v Digit))
    (Light.Stmt.seq (.call Proc.lookup [v Area, v Root, v Box, v Len] Val)
      (.set Sum ((Light.Expr.op Light.Op.add) (v Sum) (v Val)))))

open SumTen in
/-- sumTen(area, root, box, len, star): the sum of the values of the ten strings; the digit at the
position of the star is put back at the end. -/
def sumTenBody : Stmt :=
  (Light.Stmt.seq (.set Saved (M ((Light.Expr.op Light.Op.add) (v Box) (v Star))))
    (Light.Stmt.seq (.set Sum (k 0))
      (Light.Stmt.seq (Stmt.for Digit (k 10) sumTenRound)
        (Light.Stmt.seq (.store ((Light.Expr.op Light.Op.add) (v Box) (v Star)) (v Saved)) (.set Result (v Sum))))))













namespace SumTen

/-- Before round j: the sum of the first j of the ten values has been formed, and the memory differs
from μ at the position of the star only. -/
def Inv (x : SumTenArgs) (saved : ℕ) (μ : ℕ → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (val : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.tr, x.root, x.box, x.l.length, x.p, saved, j, (x.values.take j).sum, val], μ'⟩ ∧
      SameOn (· ≠ x.box + x.p) μ μ'

/-- The time of a round. -/
def tRound (L : ℕ) : ℕ := tLookup L + 15





































end SumTen








































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Tile


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# The trie of one tile

Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile". Its proof: "We compute the values of the boxes in increasing
order of their number of stars." The routine takes a root for the trie of the tile and writes it
into the table of roots (Tile.Mem.newRoot). Then, for e = 0, …, m - t, it puts the boxes with e
stars into the trie (tileRound); for e ≥ 1 their values are sums of values looked up in the trie.
The invariant Tile.Inv says what the memory holds before the boxes with e stars; Tile.round takes it
from e to e + 1, and tile_spec is the root and the loop.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The program -/

namespace Tile

/-- The local variables of tile: the arguments aA, aB, ra, tr, fp, cur, box, L, mt; the number e of
stars, the root of the trie of the tile, and a local for a result that is not used. -/
abbrev EncA : ℕ := 0
@[inherit_doc EncA] abbrev EncB : ℕ := 1
@[inherit_doc EncA] abbrev RootCell : ℕ := 2
@[inherit_doc EncA] abbrev Tries : ℕ := 3
@[inherit_doc EncA] abbrev Free : ℕ := 4
@[inherit_doc EncA] abbrev Cur : ℕ := 5
@[inherit_doc EncA] abbrev Box : ℕ := 6
@[inherit_doc EncA] abbrev Levels : ℕ := 7
@[inherit_doc EncA] abbrev Last : ℕ := 8
@[inherit_doc EncA] abbrev Stars : ℕ := 9
@[inherit_doc EncA] abbrev Root : ℕ := 10
@[inherit_doc EncA] abbrev Void : ℕ := 11

end Tile

open Tile in
/-- The boxes with e stars go into the trie; on to the next number of stars. -/
def tileRound : Stmt :=
  (Light.Stmt.seq
    (.call Proc.fillList [v Stars, v Root, v EncA, v EncB, v Tries, v Free, v Cur, v Box, v Levels, v Last] Void)
    (.set Stars ((Light.Expr.op Light.Op.add) (v Stars) (k 1))))

open Tile in
/-- tile(aA, aB, ra, tr, fp, cur, box, L, mt): a root for the trie of the tile, noted in the cell
ra; then the boxes with 0, 1, …, mt stars. The number of stars starts at 0, as all locals that are
not arguments. -/
def tileBody : Stmt :=
  (Light.Stmt.seq (.call Proc.newRoot [v Tries, v Free] Root)
    (Light.Stmt.seq (.store (v RootCell) (v Root)) (.while (Light.Cond.le (v Stars) (v Last)) tileRound)))

namespace Tile

/-! ## The pure side -/
























/-! ## The memory during the loop -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ₁ μ₂ : ℕ → ℤ} {x : TileArgs} {e : ℕ} {σ : State}
  {T T' : List ℤ}

/-- What the memory μ' holds during the loop: the trie array T, the roots, with that of the tile
behind the older ones, and the two encodings; the cells that the routine does not own are as in
μ. -/
structure Mem (μ μ' : ℕ → ℤ) (x : TileArgs) (T : List ℤ) : Prop where
  trie : TrieMem μ' x.tr x.cap x.fp T
  roots : SegN μ' x.aR (x.s.roots ++ [x.s.cells.length])
  segA : Seg μ' x.aA (arrT x.encA)
  segB : Seg μ' x.aB (arrT x.encB)
  same : SameOn x.Kept μ μ'






























/-! ## The invariant and one round -/

/-- The trie array once the root of the tile has been taken and the boxes with fewer than e stars
are in the trie. -/
def trieAt (x : TileArgs) (e : ℕ) : List ℤ :=
  fillUpTo (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s.cells.length e (trieNew x.s.cells)

/-- The arguments of the call of fillList for the boxes with e stars. -/
def fillArgs (x : TileArgs) (e : ℕ) : FillListArgs :=
  { x with e := e, tile := x.s.roots.length, roots := x.s.new.root, T := trieAt x e }

/-- The state before the boxes with e stars: the root is in its local and in its cell, and the trie
holds the boxes with fewer stars. -/
def Inv (μ : ℕ → ℤ) (x : TileArgs) (e : ℕ) (σ : State) : Prop :=
  ∃ (void : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, (x.aR + x.s.roots.length : ℕ), x.tr, x.fp, x.cur, x.box, x.L,
      (x.m - x.t : ℕ), e, x.s.cells.length, void], μ'⟩ ∧
    Mem μ μ' x (trieAt x e)
























end Tile






































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Routines


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The routines of Section 4, assembled

The fourteen routines with the numbers 40 to 53, as a list (procs40), and the theorem that every
program that holds them at these numbers (Has40) meets all their specifications (specs40). Each
routine is proved under the specifications of the routines that it calls; here these assumptions are
discharged, in the order in which the routines call each other. For the programs of Theorem 30, its
offline form and Corollary 26, which hold the fourteen routines behind forty others
(has40_of_append), this gives the specifications of the two routines that know the memory map:
preCoreSpec_of and preCoreSpec_all for the preprocessing, queryAtSpec_all for a query.
-/

@[expose] public section

namespace Light.Sec4

/-- The bodies of the procedures number 40, 41, …, 53. -/
def procs40 : List Stmt :=
  [nineFirstBody, nineNextBody, scatterBody, starFirstBody, hornerBody, lookupBody, insertBody,
    newRootBody, sumTenBody,
    fillListBody, tileBody, allTilesBody, outDigitsBody, queryCoreBody]

/-- The program P holds the routines of Section 4 at their numbers. -/
def Has40 (P : Program) : Prop := ∀ i < 14, P[40 + i]? = procs40[i]?

/-- The specifications of all the routines of Section 4. -/
structure Specs40 (lim : Limits) (P : Program) : Prop where
  nineFirst : NineFirstSpec lim P
  nineNext : NineNextSpec lim P
  scatter : ScatterSpec lim P
  starFirst : StarFirstSpec lim P
  horner : HornerSpec lim P
  lookup : LookupSpec lim P
  insert : InsertSpec lim P
  newRoot : NewRootSpec lim P
  sumTen : SumTenSpec lim P
  fillList : FillListSpec lim P
  tile : TileSpec lim P
  allTiles : AllTilesSpec lim P
  outDigits : OutDigitsSpec lim P
  queryCore : QueryCoreSpec lim P






















































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Program


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Theorem 30 on the word RAM: the program

`program30` is the list of procedures: those of Section 2 (numbers 0 to 28, of which the
preprocessing uses the shared stage), the routines of Section 4 (40 to 53), preCore, queryAt and the
two procedures of the offline form (54 to 57), and the two main procedures of Theorem 30 (80 and
81); the unused numbers hold the empty statement.

The first 58 procedures (`base58`) are also the beginning of the programs for Corollaries 26, 31
and 32.  So the assumptions of the earlier files are discharged for every program `base58 ++ R` that
begins with them: it meets the specifications of the preprocessing and of a query at a given place
of the memory (`preCore_base58`, `queryAt_base58`).  With `theorem_30_of` and `theorem_30_wanted_of`
this gives Theorem 30 and its offline form without hypotheses (`wordRam_theorem_30`,
`wordRam_theorem_30_wanted`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The procedures number 0 to 57: Section 2's program for the thin matrix product (0 to 28), eleven
unused numbers, the routines of Section 4, the two routines that know the memory map, and the two
routines of the offline form. -/
def base58 : Program :=
  Sec2.programThin ++ List.replicate 11 .skip ++ procs40 ++
    [preCoreBody, queryAtBody, wantedCoreBody, wantedMainBody]









/-- The constant of the shared stage. -/
def cShared30 : ℕ := 12 * Sec2.cShared5 + 600




























end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_ChoosingParameters_Program


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/

/-- regimeTest26(N, D) returns 1 if D^18 ≤ N and 0 if not. It changes no cell. -/
def regimeTest26Body : Stmt := (Light.Stmt.seq Sec2.regimePow (.set 0 (v 9)))

/-- allInstances26(N, D, w, U, x, y, wi, wj, out, fr). Locals 0 to 9 are the arguments, which are
passed on as they are; local 10 is the result of the test. -/
def allInstances26Body : Stmt :=
  (Light.Stmt.seq (.call Proc.regimeTest26 [v 0, v 1] 10)
    (.ite (Light.Cond.lt (k 0) (v 10)) (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
      (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)))

/-! ## The program -/

/-- The bodies of the procedures number 58, 59, …, 73 (61 is not used). -/
def procs31 (G : RatParams) : List Stmt :=
  [copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody, pre31Body G, query31Body,
    preMain31Body, queryMain31Body, offline32Body, offlineMain32Body, allInstances26Body,
    regimeTest26Body, ceilMulBody G.a G.b, ceilMulBody G.p G.q]

/-- The program for the parameters G. -/
def program31 (G : RatParams) : Program := base58 ++ procs31 G














































/-! ## The program on the word RAM -/







































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Corollary26_Regime


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollary 26: the parameters 21, 1/9 and 60, and the regime N ≥ D^18

Corollary 26 is the case c = 21, θ = 1/9 of the programs with rational parameters, with the
threshold 60 (`ratParams26`): the preprocessing calls that of Theorem 30 with L = 21 m and t = ⌈m/9⌉
if m = ⌈log₄ D⌉ ≥ 60. On the inputs with N ≥ D^18, and for m ≥ 60, the hypotheses of Theorem 30 hold
at these L and t (`hyp30_26`), and its two cost expressions are O(N²/D^{0.063}) and O(D^{0.437})
(`costs26`); both come from `Corollary26.costs`. Then the bound N²/D^{0.063} (`preBound26`) and what
is used about it. `regime26` puts this in the form in which the statements about the programs with
rational parameters ask for it (`CostsWithin`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec Finset

/-! ## The parameters -/

/-- The parameters of Corollary 26 in the program text: "L := 21m and t := ⌈m/9⌉", and the 60 of
"for all m ≥ 60". -/
def ratParams26 : RatParams where
  a := 21
  b := 1
  p := 1
  q := 9
  m₀ := 60
  hb := le_rfl
  hq := by norm_num
  hc := by norm_num
  hp := le_rfl
  hθ := by norm_num
  hm₀ := by norm_num












/-- The parameters of Theorem 30: L = 21 m. -/
def par26 (N D₀ : ℕ) : Sec2.Par := ⟨21 * logFour D₀, logFour D₀, N⟩
/-- t = ⌈m/9⌉. -/
def switch26 (D₀ : ℕ) : ℕ := (logFour D₀ + 8) / 9















/-! ## The two cost expressions -/

/-- The bound of the preprocessing of Corollary 26. -/
noncomputable def preBound26 (D₀ N : ℕ) : ℝ := (N : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.063 : ℝ)






















/-! ## The overheads -/
































/-! ## The regime -/












end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Corollary26_AllInstances


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## Time and need -/

/-- The time of allInstances26, for the parameters N, D, w, U; c is the constant of the shared
stage. -/
def allInstancesTime26 (c : ℕ) : List ℕ → ℕ
  | [N, D, w, _] =>
    400 + (if D ^ 18 ≤ N then tOffline32 c ratParams26 N D w else 40 * ((w + 1) * (D + 1)))
  | _ => 0

/-- What allInstances26 needs, for the parameters N, D, w, U: the largest number formed, the cells
from the free pointer on, the levels of calls. With B = (N + 1)^5, which bounds 10^L in the regime
(`below`). -/
def allInstancesNeed26 : List ℕ → Need
  | [N, D, _, U] =>
    ⟨1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) + 7 * ((N + 1) ^ 5 * U)
        + 10 * (N + 1) ^ 5,
      4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4, 84 * D + 12⟩
  | _ => ⟨0, 0, 0⟩

/-! ## The test -/





















/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}










































































end need

/-! ## The matrices of an instance -/

/-- The first matrix of an instance. -/
def thinMX (x : ThinInst) : Matrix (Fin x.N) (Fin x.D) ℤ := fun i j => x.X.getD (i * x.D + j) 0

/-- The second matrix of an instance. -/
def thinMY (x : ThinInst) : Matrix (Fin x.D) (Fin x.N) ℤ := fun i j => x.Y.getD (i * x.N + j) 0





























/-! ## The routine -/


























































































/-! ## The time in the regime -/


















/-! ## The need is polynomial in the parameters -/





section summands

variable {N D U Q : ℕ}














































end summands






















end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Corollary26_Program


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# Corollary 26: the program

Proof of Corollary 26: "Let L := 21m and t := ⌈m/9⌉. We will apply Theorem 30 with these
parameters". `program26` is the program with rational parameters in its text (`program31`) at 21,
1/9 and the threshold 60 (`ratParams26`). Its preprocessing finds m = ⌈log₄ D⌉ and compares it with
60 (`program26_pre31`).

Only the definition `program26` is used elsewhere. The lemmas of this file show a reader of the
paper what the general program does at the parameters of Corollary 26; nothing rests on them.

* "For m ≥ 60, Theorem 30 thus applies": the preprocessing calls the procedures for L and t, which
  find ⌈21 m / 1⌉ and ⌈1 m / 9⌉ by counting (`program26_levels31`, `program26_switch31`), writes the
  padded matrices, calls the preprocessing of Theorem 30, and stores the base address and the flag
  1; this leaves the data structure of Theorem 30 with L = 21 m and t = ⌈m/9⌉
  (`pre31_program26_above`). A query reads the flag and calls the query of Theorem 30
  (`program26_query31`, `query31_program26_above`).
* "(For m < 60, D is bounded by a constant, and the corollary holds trivially.)": the preprocessing
  stores the flag 0 (`pre31_program26_below`), and a query reads the flag and computes an inner
  product (`program26_query31`, `query31_program26_below`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-- **The program of Corollary 26**: the parameters in its text are 21, 1/9 and 60. -/
def program26 : Program := program31 ratParams26

/-! ## The parameters in the text -/






















section stages

variable {lim : Limits} {N D₀ aX aY fr : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ} {μ : ℕ → ℤ}

/-! ## From the threshold on -/




















































/-! ## Below the threshold -/




























end stages

end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_Directory


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp


/-!
# The cells of the directory, by name

The routines of Section 4 find the sizes and the addresses of the tables in the directory, the
first cells of the block.  `DirCells p b0 μ` says what the cells that they read hold, one equation
for each cell, under the name that the cell has in the program texts (`Dir.bands`, `Dir.encA`, …).
A proof that treats `x := mem[b0 + Dir.bands]` names the equation `bands`.  The shared stage
establishes all of them (`SharedReady.dirCells`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-- What the cells of the directory that the routines of Section 4 read hold. -/
structure DirCells (p : Sec2.Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  levels : μ b0 = (p.L : ℕ)
  inner : μ (b0 + 1) = (p.m : ℕ)
  outer : μ ((b0 : ℤ) + 4).toNat = (p.Lo : ℕ)
  blocks : μ ((b0 : ℤ) + 7).toNat = (p.K0 : ℕ)
  bands : μ ((b0 : ℤ) + 9).toNat = (p.nB : ℕ)
  leaves : μ ((b0 : ℤ) + 10).toNat = (p.T : ℕ)
  mask : μ ((b0 : ℤ) + 21).toNat = (p.aMASK b0 : ℕ)
  band : μ ((b0 : ℤ) + 22).toNat = (p.aBAND b0 : ℕ)
  block : μ ((b0 : ℤ) + 23).toNat = (p.aBLOCK b0 : ℕ)
  digits : μ ((b0 : ℤ) + 24).toNat = (p.aDIG3 b0 : ℕ)
  encA : μ ((b0 : ℤ) + 26).toNat = (p.aENCA b0 : ℕ)
  encB : μ ((b0 : ℤ) + 27).toNat = (p.aENCB b0 : ℕ)
  sharedEnd : μ ((b0 : ℤ) + 30).toNat = (aWD p b0 : ℕ)



















end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_TimeOfBlock


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 30 in the light language: the two routines against the expressions (8) and L ∑ α_d

Pure arithmetic, continued. Every summand of the time of the shared stage and of the length of the
shared block is at most a constant times `10^L`, or `N (L + 1)`, or the work for the bands
(`sharedShape_le`, `sharedEnd_sub_le`), and these three are within (8). With the tiles of the
previous file this gives the three bounds that leave these two files: the preprocessing takes
`O((8))` steps (`exists_tPreCore_le`), the block has `O((8))` cells (`exists_top_sub_le`), and a
query takes `O(L ∑_{d ≤ t} α_d)` steps (`exists_tQueryAt_le`).  The offline form uses them
elsewhere: its expression (9) is (8) plus |W| times the cost of a query (`Theorem30.cost9_eq`, with
the mathematics of Theorem 30), and `exists_tWantedCore_le`, beside the offline statement, puts the
two bounds together.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-! ## The shared stage, in natural numbers -/















/-- The facts about the sizes that the two estimates below use; T is `10^L` and S7 is `7^L`. -/
 structure SizeFacts (L m K KK N0 D S7 T : ℕ) : Prop where
  sq : (L + 1) ^ 2 ≤ T
  KL : K * L ≤ T
  KND : K * N0 * D ≤ S7
  LS : L * S7 ≤ 2 * T
  ST : S7 ≤ T
  KK_le : KK ≤ K
  K_pos : 1 ≤ K
  N0_pos : 1 ≤ N0
  D_pos : 1 ≤ D
  L_pos : 1 ≤ L
  mL : m ≤ L










































































/-! ## Within (8) -/













































































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Programs_Sec4_Theorem30_WordSize


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec


/-!
# Theorem 30 in the light language: limits that are polynomial in N

"Word size", proof of Theorem 30.  For every exponent c of the bound N^c on the entries there are
limits (`lim30`) that the two routines preCore and queryAt can live with (`lim30_ok`) and that are
at most 2^9 ((N + 1) (D + 1))^(20 + 2c) (`small_lim30`).  The exponents are generous: since (10^L)²
≤ N^5, every quantity that depends on L is at most B = (N + 1)^5 (`below`), the block has at most
222 B⁴ cells (`top_sub_le_pow`), and the word bound `word30` is a sum of seven terms, each at most a
small multiple of (N + 1)^(20 + 2c) (`word30_le`).  What the two routines ask of the limits is
`Lim30`, in their specifications.  The polynomial bound is for a block whose base address b0 is at
most 10 (N + 1)³; the end theorems, which put the block behind the input, show this of their b0
(`b0_le`, `wantedB0_le`, `blockAt_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset
































/-- Everything that depends on `L` is at most `B`; see `below` for `B = (N + 1)^5`. -/
structure Below (p : Sec2.Par) (t B : ℕ) : Prop where
  one : 1 ≤ B
  T : 10 ^ p.L ≤ B
  S7 : 7 ^ p.L ≤ B
  L1 : p.L + 1 ≤ B
  tenm : 10 ^ p.m ≤ B
  bx : (boxes p.L p.m t).card ≤ B
  nB : p.nB ≤ B
  N : p.N ≤ B


























































































































































end Light.Sec4

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_RunningTimes_Sec3_Theorem19_Layout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# Exact Triangle: from a solver of the task to a program for the layout of the end statement

Exact Triangle (Theorem 19).  `realized_exactTriangle`: if the task `etTask` is solved in
time T, then `EndStatement.ExactTriangle` is solved on the word RAM within a constant times T.

The input is n in cell 0 and the three matrices of weights from the cells 1, 1 + n² and 1 + 2n²; the
free pointer is 1 + 3n² (`triangleInst`).  The task speaks of the instance that is read from the
three lists, which is the instance itself (`triOf_rowMajor`).  So the input meets the task's
precondition (`pre_exactTriangle`), and the result of a solver is the right verdict
(`post_exactTriangle`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The instance that is read from the three lists is the instance. -/
theorem triOf_rowMajor {n : ℕ} (T : TriangleInstance ℤ n) :
    triOf n (rowMajor T.wAB) (rowMajor T.wBC) (rowMajor T.wAC) = T := by
  cases T with
  | mk wAB wBC wAC =>
    unfold triOf
    congr 1 <;> funext i j <;> exact getD_rowMajor _ i j

/-- The input: the size and the three matrices, row by row. -/
theorem input_exactTriangle (x : Bounded EndStatement.ExactTriangle) :
    (ofEnd EndStatement.ExactTriangle).input x =
      (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2) := by
  simp only [EndStatement.ExactTriangle, rowByRow_eq]

/-- The entries of the three matrices are within the bound. -/
theorem abs_le_of_mem_exactTriangle (x : Bounded EndStatement.ExactTriangle) {a : ℤ}
    (ha : a ∈ rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2) : |a| ≤ (x.U : ℤ) :=
  Bounded.abs_le (by simpa only [EndStatement.ExactTriangle, rowByRow_eq] using ha)

/-- The instance of the task: where the three matrices stand. -/
def triangleInst (x : Bounded EndStatement.ExactTriangle) : etTask.Inst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), rowMajor x.x.1, rowMajor x.x.2.1,
    rowMajor x.x.2.2⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_exactTriangle (x : Bounded EndStatement.ExactTriangle) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    etTask.Pre (triangleInst x) (memOf ((ofEnd EndStatement.ExactTriangle).input x))
      (1 + 3 * (x.n * x.n)) := by
  have hAB : (rowMajor x.x.1).length = x.n * x.n := length_rowMajor _
  have hBC : (rowMajor x.x.2.1).length = x.n * x.n := length_rowMajor _
  rw [input_exactTriangle]
  exact triPre_of_arrays (base := 1) hn hU
    { len := hAB
      seg := by
        have := seg_first (x.n : ℤ) (rowMajor x.x.1) (rowMajor x.x.2.1 ++ rowMajor x.x.2.2)
        rwa [← List.append_assoc] at this
      bound := fun a (ha : a ∈ rowMajor x.x.1) => abs_le_of_mem_exactTriangle x (by simp [ha]) }
    { len := hBC
      seg := by
        have := seg_memOf ((x.n : ℤ) :: rowMajor x.x.1) (rowMajor x.x.2.1) (rowMajor x.x.2.2)
        rwa [List.length_cons, hAB, Nat.add_comm] at this
      bound := fun a (ha : a ∈ rowMajor x.x.2.1) => abs_le_of_mem_exactTriangle x (by simp [ha]) }
    { len := length_rowMajor _
      seg := by
        have := seg_second (x.n : ℤ) (rowMajor x.x.1 ++ rowMajor x.x.2.1) (rowMajor x.x.2.2)
        rwa [List.length_append, hAB, hBC, ← Nat.two_mul] at this
      bound := fun a (ha : a ∈ rowMajor x.x.2.2) => abs_le_of_mem_exactTriangle x (by simp [ha]) }

/-- The result of a solver of the task is the right verdict of the end statement's Exact
Triangle. -/
theorem post_exactTriangle (x : Bounded EndStatement.ExactTriangle) (r : ℤ) (μ' : ℕ → ℤ)
    (h : etTask.Post (triangleInst x) (memOf ((ofEnd EndStatement.ExactTriangle).input x))
      (1 + 3 * (x.n * x.n)) r μ') :
    (ofEnd EndStatement.ExactTriangle).IsAnswer x (verdictOf true r) fun i =>
      μ' (((ofEnd EndStatement.ExactTriangle).input x).length + i) := by
  obtain ⟨rfl, -⟩ := h
  exact ⟨(verdictOf_flag _).trans (iff_of_eq (congrArg TriangleInstance.HasZeroTriangle
    (triOf_rowMajor ⟨x.x.1, x.x.2.1, x.x.2.2⟩))), trivial⟩

/-- What connects Exact Triangle in the layout of the end statement with the task. -/
noncomputable def wrapTriangle : Wrap EndStatement.ExactTriangle etTask true where
  args := [v 1, v 2, k 1, ((Light.Expr.op Light.Op.add) (k 1) (v 3)), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 2) (v 3))), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 3) (v 3)))]
  inst := triangleInst
  fr x := 1 + 3 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [etTask, triangleInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
  zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨a, _⟩ => absurd a.isLt (by omega)⟩, trivial⟩
  pre := pre_exactTriangle
  post x r μ' _ h := post_exactTriangle x r μ' h







end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_RunningTimes_Sec3_Theorem22_ApspLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# APSP: from a solver of the task to a program for the layout of the end statement

APSP (Theorem 22).  `realized_apsp`: if the task `apTask` is solved in time T, then
`EndStatement.APSP` is solved on the word RAM within a constant times T.

The input is n in cell 0, the adjacency matrix from cell 1 and the weights from cell 1 + n².  The
answer goes to the 2n² cells from 1 + 2n², and the free pointer is 1 + 4n² (`apspInst`).  The task
speaks of the graph with weights in `WithTop ℤ` that is read from the two lists, which is the graph
of the instance (`graphOf_apsp`).  So the input meets the task's precondition (`pre_apsp`), and what
a solver leaves in the output cells is what `EndStatement.APSP` asks for (`post_apsp`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The adjacency matrix of an instance, as it is written into the memory. -/
def apspAdj (x : Bounded EndStatement.APSP) : List ℤ :=
  rowMajor fun i j => if (x.x.1 i j).isSome then 1 else 0

/-- The weights of an instance, as they are written into the memory. -/
def apspWeights (x : Bounded EndStatement.APSP) : List ℤ := rowMajor fun i j => (x.x.1 i j).getD 0

/-- The input: the size and the two matrices, row by row. -/
theorem input_apsp (x : Bounded EndStatement.APSP) :
    (ofEnd EndStatement.APSP).input x = (x.n : ℤ) :: (apspAdj x ++ apspWeights x) := by
  simp only [EndStatement.APSP, rowByRow_eq, apspAdj, apspWeights]

/-- The graph that is read from the two lists is the graph of the instance. -/
theorem graphOf_apsp (x : Bounded EndStatement.APSP) :
    graphOf x.n (apspAdj x) (apspWeights x) = fun i j => toTop (x.x.1 i j) := by
  funext i j
  unfold graphOf apspAdj apspWeights
  rw [getD_rowMajor _ i j, getD_rowMajor _ i j]
  cases x.x.1 i j <;> simp [toTop]

/-- The weights are within the bound. -/
theorem abs_le_of_mem_apspWeights (x : Bounded EndStatement.APSP) {a : ℤ} (ha : a ∈ apspWeights x) :
    |a| ≤ (x.U : ℤ) :=
  Bounded.abs_le (by
    simpa only [EndStatement.APSP, rowByRow_eq, apspAdj, apspWeights] using
      List.mem_append_right (apspAdj x) ha)

/-- The instance of the task: where the two matrices and the answer stand. -/
def apspInst (x : Bounded EndStatement.APSP) : GraphInst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), apspAdj x, apspWeights x⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_apsp (x : Bounded EndStatement.APSP) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    apTask.Pre (apspInst x) (memOf ((ofEnd EndStatement.APSP).input x)) (1 + 4 * (x.n * x.n)) := by
  have hA : (apspAdj x).length = x.n * x.n := length_rowMajor _
  rw [input_apsp]
  exact
  { n_pos := hn
    U_pos := hU
    lenADJ := hA
    lenW := length_rowMajor _
    segADJ := seg_first _ _ _
    segW := by
      have := seg_second (x.n : ℤ) (apspAdj x) (apspWeights x)
      rwa [hA] at this
    zeroOne := by
      intro a ha
      obtain ⟨i, j, rfl⟩ := mem_rowMajor ha
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    leW := fun a ha => abs_le_of_mem_apspWeights x ha
    belowADJ := by simp only [apspInst]; omega
    belowW := by simp only [apspInst]; omega
    belowOut := by simp only [apspInst]; omega
    apartADJ := Or.inl (by simp only [apspInst]; omega)
    apartW := Or.inl (by simp only [apspInst]; omega)
    noNegativeCycle :=
      (congrArg NoNegativeCycle (graphOf_apsp x)).mpr (noNegativeCycle_toTop x.x.2) }

/-- What the task leaves in the output cells is a right answer of the end statement's APSP. -/
theorem post_apsp (x : Bounded EndStatement.APSP) (r : ℤ) (μ' : ℕ → ℤ)
    (h : apTask.Post (apspInst x) (memOf ((ofEnd EndStatement.APSP).input x))
      (1 + 4 * (x.n * x.n)) r μ') :
    (ofEnd EndStatement.APSP).IsAnswer x (verdictOf false 1) fun i =>
      μ' (((ofEnd EndStatement.APSP).input x).length + i) := by
  obtain ⟨⟨dist, hdist, hcells⟩, -⟩ := h
  have hdist' : IsDistanceMatrix (fun i j => toTop (x.x.1 i j)) dist :=
    (congrArg (fun w => IsDistanceMatrix w dist) (graphOf_apsp x)).mp hdist
  have hlen : ((ofEnd EndStatement.APSP).input x).length = 1 + 2 * (x.n * x.n) := by
    have hA : (apspAdj x).length = x.n * x.n := length_rowMajor _
    have hB : (apspWeights x).length = x.n * x.n := length_rowMajor _
    rw [input_apsp, List.length_cons, List.length_append, hA, hB]
    omega
  refine ⟨by simp [verdictOf, EndStatement.APSP], output_apsp x.x _ fun i j => ?_⟩
  rw [hlen]
  exact reachable_or_not hdist' (hcells i j).1 (hcells i j).2

/-- What connects APSP in the layout of the end statement with the task.  The program always
accepts: the answer is in the output cells. -/
def wrapApsp : Wrap EndStatement.APSP apTask false where
  args := [v 1, v 2, k 1, ((Light.Expr.op Light.Op.add) (k 1) (v 3)), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 2) (v 3))), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 4) (v 3)))]
  inst := apspInst
  fr x := 1 + 4 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [apTask, apspInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
  zero x hn _ := ⟨⟨fun _ => trivial, fun _ => rfl⟩, fun i => absurd i.isLt (by omega)⟩
  pre := pre_apsp
  post x r μ' _ h := post_apsp x r μ' h







end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_RunningTimes_Sec3_Theorem22_MinPlusLayout


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam


/-!
# The (min,+)-product: from a solver of the task to a program for the layout of the end statement

The (min,+)-product (Theorem 22).  `realized_minPlusProduct`: if the task `mpTask` is
solved in time T, then `EndStatement.MinPlusProduct` is solved on the word RAM within a constant
times T.

The input is n in cell 0, the first matrix from cell 1 and the second from cell 1 + n².  The product
goes to the n² cells from 1 + 2n², and the free pointer is 1 + 3n² (`minPlusInst`).  The input meets
the task's precondition (`pre_minPlusProduct`).  A solver leaves the list `minPlusList` in the
output cells, and each of its entries is a minimum as `EndStatement.MinPlusProduct` asks for: it is
attained, and it is a lower bound (`post_minPlusProduct`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

/-- The input: the size and the two matrices, row by row. -/
theorem input_minPlusProduct (x : Bounded EndStatement.MinPlusProduct) :
    (ofEnd EndStatement.MinPlusProduct).input x =
      (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2) := by
  simp only [EndStatement.MinPlusProduct, rowByRow_eq]

/-- The input takes 1 + 2n² cells. -/
theorem length_input_minPlusProduct (x : Bounded EndStatement.MinPlusProduct) :
    ((ofEnd EndStatement.MinPlusProduct).input x).length = 1 + 2 * (x.n * x.n) := by
  rw [input_minPlusProduct, List.length_cons, List.length_append, length_rowMajor,
    length_rowMajor]
  omega

/-- The entries of the two matrices are within the bound. -/
theorem abs_le_of_mem_minPlusProduct (x : Bounded EndStatement.MinPlusProduct) {a : ℤ}
    (ha : a ∈ rowMajor x.x.1 ++ rowMajor x.x.2) : |a| ≤ (x.U : ℤ) :=
  Bounded.abs_le (by simpa only [EndStatement.MinPlusProduct, rowByRow_eq] using ha)

/-- The instance of the task: where the two matrices and the product stand. -/
def minPlusInst (x : Bounded EndStatement.MinPlusProduct) : mpTask.Inst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), rowMajor x.x.1, rowMajor x.x.2⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_minPlusProduct (x : Bounded EndStatement.MinPlusProduct) (hn : 1 ≤ x.n)
    (hU : 1 ≤ x.U) :
    mpTask.Pre (minPlusInst x) (memOf ((ofEnd EndStatement.MinPlusProduct).input x))
      (1 + 3 * (x.n * x.n)) := by
  have hA : (rowMajor x.x.1).length = x.n * x.n := length_rowMajor _
  rw [input_minPlusProduct]
  exact
  { n_pos := hn
    U_pos := hU
    lenA := hA
    lenB := length_rowMajor _
    segA := seg_first _ _ _
    segB := by
      have := seg_second (x.n : ℤ) (rowMajor x.x.1) (rowMajor x.x.2)
      rwa [hA] at this
    leA := fun a (ha : a ∈ rowMajor x.x.1) => abs_le_of_mem_minPlusProduct x (by simp [ha])
    leB := fun a (ha : a ∈ rowMajor x.x.2) => abs_le_of_mem_minPlusProduct x (by simp [ha])
    belowA := by simp only [minPlusInst]; omega
    belowB := by simp only [minPlusInst]; omega
    belowC := by simp only [minPlusInst]; omega
    apartA := Or.inl (by simp only [minPlusInst]; omega)
    apartB := Or.inl (by simp only [minPlusInst]; omega) }

/-- What the task leaves in the output cells is the (min,+)-product as the end statement asks for
it. -/
theorem post_minPlusProduct (x : Bounded EndStatement.MinPlusProduct) (r : ℤ) (μ' : ℕ → ℤ)
    (hn : 1 ≤ x.n)
    (h : mpTask.Post (minPlusInst x) (memOf ((ofEnd EndStatement.MinPlusProduct).input x))
      (1 + 3 * (x.n * x.n)) r μ') :
    (ofEnd EndStatement.MinPlusProduct).IsAnswer x (verdictOf false 1) fun i =>
      μ' (((ofEnd EndStatement.MinPlusProduct).input x).length + i) := by
  have hseg : Seg μ' (1 + 2 * (x.n * x.n)) (minPlusList x.n (rowMajor x.x.1) (rowMajor x.x.2)) :=
    h.1
  refine ⟨by simp [verdictOf, EndStatement.MinPlusProduct], fun i j => ?_⟩
  -- the output cell of the pair (i, j) holds the entry of the list
  have hcell : μ' (((ofEnd EndStatement.MinPlusProduct).input x).length +
      ((i : ℕ) * x.n + (j : ℕ))) = minPlusEntry x.n (rowMajor x.x.1) (rowMajor x.x.2) i j := by
    rw [length_input_minPlusProduct,
      hseg.getD (by rw [length_minPlusList]; exact Nat.mul_add_lt_mul i.isLt j.isLt) 0]
    exact entry_minPlusList _ _ i.isLt j.isLt
  obtain ⟨l, hl, hmin⟩ := exists_minPlusEntry_eq hn (rowMajor x.x.1) (rowMajor x.x.2) i j
  refine ⟨⟨⟨l, hl⟩, hcell.trans ?_⟩, fun l' => hcell.le.trans ?_⟩
  · -- the entry is attained
    rw [hmin, entry, entry, getD_rowMajor x.x.1 i ⟨l, hl⟩, getD_rowMajor x.x.2 ⟨l, hl⟩ j]
  · -- the entry is a lower bound
    have := minPlusEntry_le x.n (rowMajor x.x.1) (rowMajor x.x.2) i j l'.isLt
    rwa [entry, entry, getD_rowMajor x.x.1 i l', getD_rowMajor x.x.2 l' j] at this

/-- What connects the (min,+)-product in the layout of the end statement with the task.  The program
always accepts: the answer is in the output cells. -/
def wrapMinPlus : Wrap EndStatement.MinPlusProduct mpTask false where
  args := [v 1, v 2, k 1, ((Light.Expr.op Light.Op.add) (k 1) (v 3)), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 2) (v 3))), ((Light.Expr.op Light.Op.add) (k 1) ((Light.Expr.op Light.Op.mul) (k 3) (v 3)))]
  inst := minPlusInst
  fr x := 1 + 3 * (x.n * x.n)
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by omega
  vals x σ hn hU hnn := by simp [mpTask, minPlusInst, hn, hU, hnn]
  safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
  zero x hn _ := ⟨⟨fun _ => trivial, fun _ => rfl⟩, fun i => absurd i.isLt (by omega)⟩
  pre := pre_minPlusProduct
  post := post_minPlusProduct







end Light.Sec3

end

end

section
-- Source module: Definitions.Def_APSPSource_ThreeSumApsp_Sec4_Corollary26


set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Corollary 26: the parameters `L = 21m`, `t = ⌈m/9⌉`

The proof of Corollary 26 from Theorem 30, in the five steps of the paper. The parts of these steps
that hold for all `L` and `t` are proved before (`Corollary26.setting_up` to
`dominated_cost8_of_eq_10`), and Corollary 31 uses them too. The exponents `γ` and `q` of the proof
are written `gammaOf 21 (1 / 9)` and `qOf (1 / 9)`: they are the `γ` and `q` of Corollary 31 at
`c = 21` and `θ = 1/9` (`Corollary26.gamma_eq`, `Corollary26.q_eq`). The result is
`Corollary26.costs`: for `N ≥ D^18` and `m = ⌈log_4 D⌉ ≥ 60` the hypothesis `N ≥ √K N₀` of Theorem
30 holds at `L = 21m` and `t = ⌈m/9⌉`, its preprocessing cost (8) (`cost8`) is `O(N²/D^{0.063})`,
and its query cost `L ∑_{d ≤ t} α_d` (`costQuery`) is `O(D^{0.437})`.

* Setting up. The inner dimension is padded to `D = 4^m` (`Corollary26.setting_up`). This changes no
  entry of the product (`Corollary26.padding`), it changes the bounds by a constant factor
  (`padded_le`), and the hypothesis reads `N ≥ 4^{18(m-1)}` (`Corollary26.hypothesis`). The number
  `t = ⌈m/9⌉` is `switchOf (1 / 9) m`, and `t ≤ m` (`switchOf_le`).
* Boxes. `ρ < 9/20` and `ρ^t ≤ (9/20)^{m/9} = D^{-γ}` with `γ = 0.0640…` (`Corollary26.rho_lt`,
  `Corollary26.rho_pow_le`, `Corollary26.gamma_digits`), so the first term of (8) is `O(m² N²/D^γ)`
  (`Corollary26.first_term`).
* Queries. `∑_{d ≤ t} α_d ≤ 72^t (9/8)^m < 72 D^q` with `q = 0.4277…` (`sum_alpha_le`,
  `Corollary26.sum_alpha_lt`, `Corollary26.q_digits`), so a query costs `O(m D^q)`
  (`Corollary26.query_cost`).
* Encodings. Inequality (10) bounds the last term of (8) and gives the hypothesis of Theorem 30
  (`Equation10.last_term`, `Equation10.tile_fits`). The standard bound on `K` (`Corollary26.le_K`)
  shows that the left-hand side of (10) is at most `√(21m+1) Λ^m` (`Corollary26.lhs10_le`);
  `Λ = 4.198… · 10^10` is below `4^18 = 6.871… · 10^10` by a factor of more than 1.63
  (`baseLambda_numeric`, `four_pow_eighteen_numeric`, `baseLambda_mul_lt`), and
  `1.63^m ≥ 4^18 √(21m+1)` for `m ≥ 60` (`Corollary26.threshold`). Together they give (10) for all
  `m ≥ 60` (`eq_10_corollary_26`).
* Conclusion. For `m ≥ 60` the hypothesis `N ≥ √K N₀` holds and (8) is `O(m² N²/D^γ)`
  (`Corollary26.tile_fits`, `dominated_cost8_of_eq_10`, `Corollary26.preprocessing`), the powers of
  `m` are absorbed into the exponents (`dominated_pow_mul_D_rpow`, `Corollary26.conclusion`), and
  the bounds are stated in the given `D` (`Corollary26.costs`). For `|W| ≤ N²/√D` queries the total
  is `O(N²/D^{0.063})` (`corollary_26_W`).

Bounds "up to a constant" are written with `Dominated`, in the one parameter `m` or in the record
`Sizes` of the given `D`, of `N` and of `m`. Two sentences of the proof are proved with the programs
(`wordRam_corollary_26`, `wordRam_corollary_26_wanted`): "(For m < 60, D is bounded by a constant,
and the corollary holds trivially.)" and "The bound for a set W follows by asking |W| queries." The
last section shows that the parameters of this proof are those of Corollary 31 and of Table 2 at
`c = 21` and `θ = 1/9`; nothing else rests on it.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Setting up -/








/-! ### Boxes -/






































































/-! ### Queries -/
































































/-! ### Encodings -/


























/-- The base `Λ` of the proof of Corollary 26: "Λ := 10^21 · (20/9)^{1/9} / ((21^21/20^20)^{1/2} ·
3^20)". -/
noncomputable def baseLambda : ℝ :=
  10 ^ 21 * (20 / 9 : ℝ) ^ (1 / 9 : ℝ) / (Real.sqrt (21 ^ 21 / 20 ^ 20) * 3 ^ 20)






































































































/-! ### Conclusion -/

/-- The range of the step "Conclusion": "m ≥ 60", and "N ≥ 4^{18(m-1)}". -/
structure Sizes.Large26 (p : Sizes) : Prop where
  m_ge : 60 ≤ p.m
  N_ge : 4 ^ (18 * (p.m - 1)) ≤ p.N
















































/-- The instances of Corollary 26 from the threshold on: `N ≥ D^{18}` and `m = ⌈log_4 D⌉ ≥ 60`. -/
structure Sizes.Corollary26 (p : Sizes) : Prop where
  N_ge : p.D₀ ^ 18 ≤ p.N
  m_eq : p.m = ⌈Real.logb 4 (p.D₀ : ℝ)⌉₊
  m_ge : 60 ≤ p.m


































































/-! ### The parameters `c = 21` and `θ = 1/9` of Corollary 31 and Table 2

The sentence before Corollary 26 says: "It is the entry c = 21, q = 0.43 of Table 2". The parameters
of the proof above are those of Corollary 31 at `c = 21`, `θ = 1/9`: this holds for `L`
(`levelsOf_21`), for `γ` and `q` (`Corollary26.gamma_eq` and `Corollary26.q_eq` above), and for `Λ`
(`baseLambda_eq_exp_lnΛ`). The condition `ε < R_c(γ)` holds at `ε = 1/18` (`Corollary26.Rc_digits`),
and `N ≥ D^18` gives the condition `D ≤ N^{0.056}` of the row `c = 21` of the table, which is
`table_2_c21` (`Corollary26.row_condition`). Nothing else rests on this section. -/



























































end ThreeSumApsp

end

end


