-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle008
-- name    : ThreeSum1960614_Machine_Bundle008
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:19:38.429982+00:00
-- url     : https://prove2.me/theorems/e4ee4b58-4f3e-4ae5-8137-a7161a98682d
-- title:
--   Compiler contracts, reusable tasks, and trimmed block encodings
-- statement:
--   For a finite Light program $P$, a verdict mode $\delta$, and a Light step count $c$, the compiled step budget is the affine function
--
--   $$T_{P,\delta}(c)=\operatorname{startCost}(P,\delta)+\operatorname{stepsPerStep}(\operatorname{dispPos}(P,\delta))c.$$
--
--   Stack-space and negative-address bounds depend on the program text and the allowed call depth. The compiler input contract represents the Light memory in word-RAM cells and puts two bounded integer arguments into designated cells. Its outcome contract represents the final memory and result, preserves the argument cells, and preserves cells beyond the allowed positive and negative working regions. The bundle also defines segment-copy, constant-fill, and entrywise linear-combination programs and the associated program-proof tactic interface.
--
--   A procedure need consists of a word bound, extra cell count, and extra call depth. For a free pointer $f$ and current depth $d$, it is admissible when these requirements fit the run limits, including $f+\mathrm{cells}\le\mathrm{space}$ and $d+\mathrm{depth}\le\mathrm{maxDepth}$. Polynomial need bounds have the form $2^s((n+1)(U+1))^k$, for fixed natural exponents $s,k$. A task-solving specification requires the procedure contract to hold in every extension of its finite program, for every permitted input, memory, bound, and free pointer; its real-valued runtime form also bounds the natural execution budget uniformly for $n,U\ge1$ and every real upper bound $u\ge U$.
--
--   For each input size $n$, the executable band size is $B=\lceil R/D\rceil$, where $R$ is the integer ceiling of the square root of the typed output count and $D=2^{\lfloor62656016\mu(n)/1000000000\rfloor}$. The included rounding facts give $0<B$ and $R\le DB<R+D$. Block endpoint encodings flatten $J$ local subsets of $464h$ coordinates. Left and right admissibility independently require exactly $h$ coordinates per block and a hash bucket within its cap. Disjoint admissible endpoints reconstruct retained choice tuples. Their natural-number histograms count indices in finite sets whose integer residues match the positional endpoint encoding, with an additional offset on the right.
--
--   These contracts connect reusable imperative procedures, exact rounded parameters, and independently trimmed combinatorial histograms in the deterministic integer 3SUM runtime proof. The compiler and routine interfaces retain the pinned upstream attribution.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/WholeProgram.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Copy.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Tactics.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Tasks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BandScales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BlockEncoding.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LightArray.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Filter
end Filter
namespace Finset
end Finset
namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace Light.Copy
end Light.Copy
namespace Light.Fill
end Light.Fill
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.Light.Copy
end ThreeSum1960614.Machine.Light.Copy
namespace ThreeSum1960614.Machine.Light.Fill
end ThreeSum1960614.Machine.Light.Fill
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec

variable {W : ℕ}

/-! ## The verdict -/







/-! ## Time and space of the compiled program -/

/-- A bound for the number of steps of the compiled program outside the outermost statement:
`dispPos` + `frameSize` + 9 before it (`steps_start`), at most three after it (`steps_tail`), and
the verdict. -/
def startCost (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : ℕ := _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec + _root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 13

/-- A bound for the number of steps of the compiled program, for c steps of the light program. -/
def _root_.ThreeSum1960614.Machine.Light.ramSteps (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) (c : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.startCost P dec + _root_.Light.Compiler.stepsPerStep (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) * c

/-- The number of cells of the stack that a run within the limits needs. -/
def stackCells (P : _root_.ThreeSum1960614.Machine.Light.Program) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) : ℕ :=
  _root_.Light.Compiler.mainFrame + (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1) * (lim.depth + 1)

/-- A bound for the extent of the negative cells that the compiled program uses: the stack ends
before the cell -2 · stackCells, and the pool, which reaches further down than the temporaries, ends
at the cell -(25 + 4 · dispPos). -/
def lowCell (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) : ℕ :=
  max (2 * _root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim) (25 + 4 * _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec)



/-! ## The setting of the simulation theorem -/

section setting

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p0 : ℕ} {dec : Bool}



variable (hfit : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) (_root_.ThreeSum1960614.Machine.Light.Compiler.stackCells P lim))





end setting

/-! ## The theorem -/

/-- The cells 0, 1, 2, … of the memory m of the machine hold the memory μ of the light language,
and μ holds words. -/
structure Holds (W : ℕ) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (μ : ℕ → ℤ) (m : ℤ → BitVec W) : Prop where
  rep : ∀ a : ℕ, m (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (μ a)
  bounded : ∀ a, |μ a| ≤ lim.word

/-- What a run of a compiled program needs in the memory m: the memory μ of the light language, and
the arguments i and j, which are words, in their two cells. -/
structure Input (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (μ : ℕ → ℤ) (i j : ℤ) (m : ℤ → BitVec W) : Prop
    extends _root_.ThreeSum1960614.Machine.Light.Compiler.Holds W lim μ m where
  arg1 : m _root_.Light.Compiler.cARG1 = _root_.ThreeSumApsp.WordRam.wd W i
  arg2 : m _root_.Light.Compiler.cARG2 = _root_.ThreeSumApsp.WordRam.wd W j
  arg1_le : |i| ≤ lim.word
  arg2_le : |j| ≤ lim.word

/-- What a run of a compiled program from the memory m leaves in the memory m', if the light run
ends in σ'. -/
structure Outcome (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) (m : ℤ → BitVec W) (σ' : _root_.ThreeSum1960614.Machine.Light.State)
    (m' : ℤ → BitVec W) : Prop where
  /-- The cells 0, 1, 2, … hold the final memory. -/
  holds : _root_.ThreeSum1960614.Machine.Light.Compiler.Holds W lim σ'.mem m'
  /-- The cell for the result holds the result. -/
  result : (m' _root_.Light.Compiler.cRESULT).toInt = σ'.loc 0
  /-- The first argument is still there. -/
  arg1 : m' _root_.Light.Compiler.cARG1 = m _root_.Light.Compiler.cARG1
  /-- The second argument is still there. -/
  arg2 : m' _root_.Light.Compiler.cARG2 = m _root_.Light.Compiler.cARG2
  /-- The cells far below 0 and the cells from lim.space on are unchanged. -/
  far : ∀ a : ℤ, a < -(_root_.ThreeSum1960614.Machine.Light.Compiler.lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a → m' a = m a



end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## copy -/

namespace Copy
open _root_.Light.Copy







end Copy

open _root_.Light.Copy
open _root_.ThreeSum1960614.Machine.Light.Copy in
/-- copy(src, dst, n): for i < n, dst[i] := src[i]. -/
def copyBody : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.pass _root_.Light.Copy.Idx (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Copy.Len) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Copy.Dst) (_root_.ThreeSum1960614.Machine.Light.M (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Copy.Src) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Copy.Idx))))





/-! ## fill -/

namespace Fill
open _root_.Light.Fill







end Fill

open _root_.Light.Fill
open _root_.ThreeSum1960614.Machine.Light.Fill in
/-- fill(dst, n, x): for i < n, dst[i] := x. -/
def fillBody : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.pass _root_.Light.Fill.Idx (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Fill.Len) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Fill.Dst) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Fill.Val)





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Tactics for proofs about programs

A proof about a program follows the text of the program from top to bottom.  The goal is always
`Ends lim P d s ⟨frame l, μ⟩ T Q`, and the statement at the head of `s` decides what comes next:

| the head of the program | what to write                  | what it is told                       |
|-------------------------|--------------------------------|---------------------------------------|
| `x := e`                | `light_set z`                  | the value `z` of `e`                  |
| `mem[a] := e`           | `light_store b z`              | the address `b` and the value `z`     |
| `if c then … else …`    | `light_if h₁ h₂ : p`           | what the test says, and two names     |
| `x := p(args)`          | `light_call fact with …`       | what the procedure does (`Meets`)     |
| a piece with a lemma    | `light_piece fact with …`      | what the piece does (`Ends`)          |
| `skip`, nothing else    | `light_skip`                   |                                       |
| a loop, nothing else    | `refine Ends.forFrame …`       | invariant and number of rounds        |
| a loop, then more       | `refine Ends.next _ (…)`       | the loop's rule with `(hT := le_rfl)` |

Each tactic works whether or not more program follows, hands the steps that are left to the rest of
the program, and proves the side conditions (the expressions stay within the limits and have the
values that were given, the time suffices) by `light_side` and `light_time`.  What is left is the
goal about the rest of the program, or `Q` of the last state.  After `light_if` there are two goals,
first the one in which the test holds.  The patterns after `with` take apart, as those of `rintro`
do, what holds after the call or the piece.  Goals for holes `?_` in a `fact` come before the goal
about the rest of the program.

The side conditions are decided by linear arithmetic over the hypotheses in the context.
`light_facts H` puts the fields of a record `H` there.  What a side condition needs beyond that is
named after `using`: the content of a cell that is read, a definition to be unfolded, a running time
to be unfolded: `light_set K[j] using hkey`.

A program that is a definition is replaced by its text when a single statement is treated.  A
definition that stands at the head of a sequence stays closed: it is a piece, for `light_piece`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Records -/



/-! ## One statement -/





























end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-! ## Limits -/

/-- What a run needs: the largest absolute value it forms, the number of cells it uses from the free
pointer on, and the number of levels of calls below the procedure. -/
structure Need : Type where
  word : ℕ
  cells : ℕ
  depth : ℕ

/-- The limits allow for the need of a procedure that is called at depth `d` with the free pointer
`fr`.  An address always fits in a word. -/
structure Need.Ok (r : _root_.ThreeSum1960614.Machine.Light.Need) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (fr d : ℕ) : Prop where
  word : (r.word : ℤ) ≤ lim.word
  cells : fr + r.cells ≤ lim.space
  space : (lim.space : ℤ) ≤ lim.word
  depth : d + r.depth ≤ lim.depth



/-- A need that depends on a size and a bound is polynomially bounded in the two: by
`2^s ((n + 1) (U + 1))^k`. -/
def PolyNeed (need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need) : Prop :=
  ∃ s k : ℕ, ∀ n U : ℕ, (need n U).word ≤ _root_.Light.polyBound s k [n, U] ∧ (need n U).cells ≤
    _root_.Light.polyBound s k [n, U] ∧
    (need n U).depth ≤ _root_.Light.polyBound s k [n, U]

/-! ## Specifications of single routines -/



/-! ## Tasks and solvers -/



/-- **Procedure `p` of the program `P` solves the task** within `T (size) (bound)` steps, whenever
the limits allow for `need (size) (bound)`; and so it does in every program that begins with `P`. -/
def Solves (task : _root_.Light.Task) (P : _root_.ThreeSum1960614.Machine.Light.Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need) : Prop :=
  ∃ body, P[p]? = some body ∧
    ∀ (R : _root_.ThreeSum1960614.Machine.Light.Program) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (d : ℕ) (x : task.Inst) (μ : ℕ → ℤ) (fr : ℕ), task.Pre x μ fr →
      (need (task.size x) (task.bound x)).Ok lim fr d →
      _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d body ⟨_root_.Light.frame (task.args x ++ [(fr : ℤ)]), μ⟩
        (T (task.size x) (task.bound x))
        fun σ' => task.Post x μ fr (σ'.loc 0) σ'.mem





/-- "The task is solved in time `T`", for a real-valued `T` whose second argument is an upper bound
on the numbers: some solver with a polynomially bounded need takes at most `T n u` steps on every
instance of size `n ≥ 1` with a bound `1 ≤ U ≤ u`. -/
def SolvedIn (task : _root_.Light.Task) (T : ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : _root_.ThreeSum1960614.Machine.Light.Program) (p : ℕ) (Tn : ℕ → ℕ → ℕ) (need : ℕ → ℕ → _root_.ThreeSum1960614.Machine.Light.Need), _root_.ThreeSum1960614.Machine.Light.PolyNeed need ∧
    _root_.ThreeSum1960614.Machine.Light.Solves task P p Tn need ∧
    ∀ (n U : ℕ) (u : ℝ), 1 ≤ n → 1 ≤ U → (U : ℝ) ≤ u → (Tn n U : ℝ) ≤ T n u











/-! ## Hosts -/





/-! ## Tasks with a list of parameters -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^floor(-bandShift*mu)`.
Euclidean division computes the rational exponent with bounded error.
-/

namespace ThreeSum.BandScales
open _root_.ThreeSum.BandScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology

def bandRoot (n : ℕ) : ℕ := _root_.ThreeSum.LocalCoverBounds.rootCeiling (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n)

def bandExponent (n : ℕ) : ℕ := 62656016 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n / 1000000000
def bandDivisor (n : ℕ) : ℕ := 2 ^ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandExponent n

def bandSize (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n ⌈/⌉ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n





theorem bandRoot_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n := _root_.ThreeSum.LocalCoverBounds.rootCeiling_pos _

theorem bandDivisor_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor
  positivity

theorem bandSize_mul_bounds (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n * _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n) (b := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n)
      (c := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n + _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n - 1) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n)
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n)]
    have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor_pos n
    omega

theorem bandSize_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n := by
  have hl := (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize_mul_bounds n).1
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot_pos n
  by_contra h
  have hb : _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n = 0 := by omega
  rw [hb, Nat.mul_zero] at hl
  omega

noncomputable section

def unroundedBand (n : ℕ) : ℝ := (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n





















end

end ThreeSum.BandScales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows

abbrev Occurrences (h J : ℕ) := Fin J → _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h

def outputOccurrences {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J := fun i => (q i).1

def leftSubset {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h)) :=
  _root_.ThreeSum.BlockRows.flat fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1

def rightSubset {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h)) :=
  _root_.ThreeSum.BlockRows.flat fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.2

def outputSubset {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h)) :=
  _root_.ThreeSum.BlockRows.flat fun i => (q i).2.val





















def LeftAllowed {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) : Prop :=
  ∀ i, (_root_.ThreeSum.BlockRows.row S i).card = h ∧
    _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o i))
      (_root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o i)) (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row S i))) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h

def RightAllowed {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) : Prop :=
  ∀ i, (_root_.ThreeSum.BlockRows.row S i).card = h ∧
    _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o i))
      (_root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o i)) (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row S i))) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h

instance instDecidableLeftAllowed {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) :
    Decidable (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed; infer_instance

instance instDecidableRightAllowed {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) :
    Decidable (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o S) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed; infer_instance

def endpointLeft {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) : ℤ :=
  _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) id
    (List.ofFn fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o i)) (_root_.ThreeSum.LocalGraph.leftWord (_root_.ThreeSum.BlockRows.row S i)))

def endpointRight {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) : ℤ :=
  _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) id
    (List.ofFn fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (o i)) (_root_.ThreeSum.LocalGraph.rightWord (_root_.ThreeSum.BlockRows.row S i)))











/-- Actual retained pairs can be reconstructed from independently trimmed
opposite block subsets. No shared-edge trimming premise is required. -/
def fromSubsets {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (S V : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h)))
    (hS : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S) (hV : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o V) (hd : Disjoint S V) : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J :=
  fun i => ⟨(o i, ⟨(_root_.ThreeSum.BlockRows.row S i, _root_.ThreeSum.BlockRows.row V i), _root_.ThreeSum.LayerCounts.mem_edgeSet.mpr
    ⟨(hS i).1, (hV i).1, Finset.disjoint_left.mpr (fun _ hx hy =>
      Finset.disjoint_left.mp hd (_root_.ThreeSum.BlockRows.mem_row.mp hx) (_root_.ThreeSum.BlockRows.mem_row.mp hy))⟩⟩),
    ⟨(hS i).2, (hV i).2⟩⟩







section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftWeights {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) : ℕ :=
  if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S then
    ∑ j ∈ B, if _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b j % P - _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointLeft o S then 1 else 0
  else 0

def rightWeights {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (V : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) : ℕ :=
  if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o V then
    ∑ j ∈ C, if _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c j % P + d - _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o V then 1 else 0
  else 0









end Histograms

end ThreeSum.BlockEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray
open _root_.ThreeSum.LightArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





/-- linear(srcA, srcB, dst, n, c): dst[i] := srcA[i] + c*srcB[i]. -/
def linearBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.pass 5 (_root_.ThreeSum1960614.Machine.Light.v 3) (_root_.ThreeSum1960614.Machine.Light.v 2) (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v 4) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 1) (_root_.ThreeSum1960614.Machine.Light.v 5))))))









end ThreeSum.LightArray

end ThreeSum1960614.Machine


