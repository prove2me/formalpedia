-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeSchemeInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:08:10.732486+00:00
-- url     : https://prove2.me/theorems/a6e12509-eb24-4dbe-802e-5824dbfb4672
-- title:
--   Native rational optimization and independent-set execution interfaces
-- statement:
--   This module defines the operational interfaces used to implement the weighted independent-set approximation algorithm with finite programs and exact rational arithmetic.
--
--   For a bounded structured command $c$, environments $\sigma,\tau$ and a natural cost bound $K$, its execution predicate means
--   $$\operatorname{Run}_B(c,\sigma,\tau,K)\iff
--   \exists k\le K,\ \operatorname{BigStep}_B(c,\sigma,\tau,k).$$
--   Every evaluated operand must satisfy the word bound. The definitions also specify the structured compiler layout, finite local tape interpreter, rational LP certificates, product-demand flow-cut certificates, relaxation coordinates, rounded updates and recursive stack protocols.
--
--   A fixed class implementation package records the selected finite backends and the precise correctness and resource propositions they must satisfy. Its existence and all algorithmic correctness and runtime bounds are separate theorem obligations. These definitions provide a common interface for those obligations and the final weighted finite-machine theorem.
--
--   **Formalization Note** The only supporting proofs in this definition file are elementary constructor facts for bounded instruction indices and the finite coordinate catalogue.
-- source:
--   Bonnet–Chang, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf, Sections 2–6. Native MWIS interfaces: https://github.com/EdouardBonnet/lax-263307/tree/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1. Rational LP interfaces: https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864. Flow-cut interfaces: https://github.com/EdouardBonnet/lax-455465/tree/9988b9c5399185cfb3ca2129ca7c807fd80c2885. Finite interpreter: https://github.com/szymtor/RAM-TM/tree/134e398cef46599371df99f10c9007bc34ba3868. Structured compiler: https://github.com/lax-archive/lax-submissions/tree/9394e531cc51cb67a0214bca3f9264dfe97ba5c7/word-ram.

import Mathlib.Tactic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.DeriveFintype
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.List.Count
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Dedup
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Sqrt
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_EdgeSublinearMWIS_Main_NativeWordRAM
set_option maxErrors 1000

-- Solutions.RAM_Lax808846Proofs_Imp
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
IMP+: a structured while-language with scalar variables and named
arrays, given a big-step semantics indexed by a cost. It is the layer
at which the flatness of the machine is dealt with once and for all:
the compiler to machine programs lowers control flow to jumps and array
indexing to indirect addressing, and everything above IMP+ reasons
structurally.

IMP+ is the *unbounded* reference semantics: its values are natural
numbers, nothing is ever reduced modulo `2 ^ w`, and the word length
does not occur in this file at all. That is the whole point of the
pipeline — functional correctness and cost are proved on clean
natural-number arithmetic, and the word length enters exactly once, at
the boundary, through the value bound of `Bounds` and the simulation
theorem. The operators are the standard word-RAM operations at the
level of numbers: subtraction is truncated, division rounds down with
`x / 0 = 0`, the bitwise operations are those of `Nat`, and the shifts
are multiplication and division by a power of two. Six of them are
machine instructions; the other three — `or`, `xor` and `shiftr` — are
lowered by the compiler to fixed blocks of three or four instructions,
so the choice of operators here is not a choice about the machine.

Three design points carry the weight.

*Aliasing is impossible by construction.* An environment maps names to
values and names to arrays, so distinct names denote disjoint objects
and no statement anywhere in the pipeline has to reason about overlap.
This is what replaces separation logic.

*Out-of-bounds access is stuck, not defaulted.* Expression evaluation
is `Option`-valued and an out-of-range array read has no value; an
out-of-range store has no derivation. A semantics that defaulted to
zero would diverge from what the flat machine memory returns, and the
layout simulation would then be false.

*Input and output are commands.* The environment carries the two tapes
and `read`/`write` are ordinary constructs, so their cost is part of
the cost of the run and the compiled program needs neither a prologue
that copies the input into memory nor an epilogue that writes the
output out. Array lengths are not declared anywhere: they belong to the
initial environment, because the compiled machine program never
represents them — memory starts zeroed, so an array of any length is
there for free, and its length exists only to make an out-of-range
access stuck.

The cost of a derivation is the number of executed constructs, each
weighted by the size of the expressions it evaluates. Constants are
never tight anywhere in this development; this measure is chosen only
so that it is bounded below by the number of steps of the compiled
machine program divided by a program-dependent constant.

The binary operators are collected into one type `Bop` rather than
given one `Expr` constructor each: they all evaluate the same way and
compile to one block each, so a single `bin` node turns nine cases into
one everywhere downstream, and the six that are machine instructions
are told apart from the three that are lowered in exactly one place,
the compiler's `binCode`.
The nine familiar names are available as abbreviations, so `.add e f`
still writes a sum.
-/

namespace Lax808846Proofs.Imp

/-- The binary operators of IMP+, one for each of the machine's
arithmetic and bitwise instructions. -/
inductive Bop
  /-- Addition. -/
  | add
  /-- Truncated subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division, rounding down, by zero yielding zero. -/
  | div
  /-- Bitwise conjunction. -/
  | and
  /-- Bitwise disjunction. -/
  | or
  /-- Bitwise exclusive or. -/
  | xor
  /-- Left shift, that is multiplication by a power of two. -/
  | shiftl
  /-- Right shift, that is division by a power of two. -/
  | shiftr
  deriving DecidableEq, Repr

/-- The meaning of a binary operator on natural numbers. It is the
meaning of the corresponding machine instruction with the truncation
removed. -/
def Bop.apply : Bop → ℕ → ℕ → ℕ
  | add, m, n => m + n
  | sub, m, n => m - n
  | mul, m, n => m * n
  | div, m, n => m / n
  | and, m, n => Nat.land m n
  | or, m, n => Nat.lor m n
  | xor, m, n => Nat.xor m n
  | shiftl, m, n => m * 2 ^ n
  | shiftr, m, n => m / 2 ^ n











/-- Arithmetic expressions: literals, scalar variables, array reads, and
a binary operator applied to two expressions. -/
inductive Expr
  /-- The literal `n`. -/
  | lit (n : ℕ)
  /-- The value of the scalar variable `x`. -/
  | var (x : String)
  /-- The entry of array `a` at the position given by `i`. -/
  | get (a : String) (i : Expr)
  /-- The operator `op` applied to the values of two expressions. -/
  | bin (op : Bop) (e f : Expr)

/-- The sum of two expressions. -/
abbrev Expr.add (e f : Expr) : Expr := .bin .add e f
/-- The truncated difference of two expressions. -/
abbrev Expr.sub (e f : Expr) : Expr := .bin .sub e f
/-- The product of two expressions. -/
abbrev Expr.mul (e f : Expr) : Expr := .bin .mul e f
/-- The quotient of two expressions. -/
abbrev Expr.div (e f : Expr) : Expr := .bin .div e f
/-- The bitwise conjunction of two expressions. -/
abbrev Expr.and (e f : Expr) : Expr := .bin .and e f
/-- The bitwise disjunction of two expressions. -/
abbrev Expr.or (e f : Expr) : Expr := .bin .or e f
/-- The bitwise exclusive or of two expressions. -/
abbrev Expr.xor (e f : Expr) : Expr := .bin .xor e f
/-- The first expression shifted left by the second. -/
abbrev Expr.shiftl (e f : Expr) : Expr := .bin .shiftl e f
/-- The first expression shifted right by the second. -/
abbrev Expr.shiftr (e f : Expr) : Expr := .bin .shiftr e f











/-- Conditions: equality and strict order of two expressions. -/
inductive Cond
  /-- The two expressions have equal values. -/
  | eq (e f : Expr)
  /-- The first value is smaller than the second. -/
  | lt (e f : Expr)

/-- Commands: the usual structured constructs, a store into an array
cell, and the two tape operations. -/
inductive Com
  /-- Do nothing. -/
  | skip
  /-- Assign the value of `e` to the scalar variable `x`. -/
  | assign (x : String) (e : Expr)
  /-- Store the value of `e` into array `a` at position `i`. -/
  | store (a : String) (i e : Expr)
  /-- Run `c`, then `d`. -/
  | seq (c d : Com)
  /-- Run `c` or `d` according to the condition. -/
  | ite (b : Cond) (c d : Com)
  /-- Run the body while the condition holds. -/
  | while (b : Cond) (c : Com)
  /-- Read the next number of the input into the scalar variable `x`. -/
  | read (x : String)
  /-- Write the value of `e` to the output. -/
  | write (e : Expr)

/-- An environment: the value of every scalar variable, the contents of
every array, and the two tapes. Distinct names are distinct objects, so
no two names can alias. -/
structure Env where
  /-- The value of each scalar variable. -/
  vars : String → ℕ
  /-- The contents of each array. -/
  arrs : String → List ℕ
  /-- The input not yet read. -/
  inp : List ℕ
  /-- The output written so far. -/
  out : List ℕ

/-- The environment with the scalar variable `x` set to `v`. -/
def Env.setVar (σ : Env) (x : String) (v : ℕ) : Env :=
  { σ with vars := fun y => if y = x then v else σ.vars y }

/-- The environment with position `i` of array `a` set to `v`. -/
def Env.setArr (σ : Env) (a : String) (i v : ℕ) : Env :=
  { σ with arrs := fun b => if b = a then (σ.arrs a).set i v else σ.arrs b }



/-- The size of an expression, which is what evaluating it costs. -/
def Expr.size : Expr → ℕ
  | lit _ => 1
  | var _ => 1
  | get _ i => i.size + 1
  | bin _ e f => e.size + f.size + 1



/-- The size of a condition, which is what evaluating it costs. -/
def Cond.size : Cond → ℕ
  | eq e f => e.size + f.size + 1
  | lt e f => e.size + f.size + 1





/-- The initial environment on input `x`: every scalar zero, the array
`a` holding `ext a` zeros, nothing written yet. The array lengths are
chosen by whoever uses the simulation theorem: an array costs nothing,
since the machine's memory starts zeroed, and the lengths exist only to
make an out-of-range access stuck. -/
def initEnv (ext : String → ℕ) (x : List ℕ) : Env where
  vars := fun _ => 0
  arrs := fun a => List.replicate (ext a) 0
  inp := x
  out := []

end Lax808846Proofs.Imp

end

-- Solutions.RAM_Lax808846Proofs_Bounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
The no-overflow side of the pipeline.

The machine reduces every value it produces modulo `2 ^ w`; IMP+ does
not. The two therefore agree exactly when no value of the IMP+ run
reaches `2 ^ w`, and that is the only extra obligation the pipeline
asks of its users. This file says what "no value of the run reaches
`B`" means, in the form the simulation consumes and the reasoning layer
can compose.

The bound is threaded through the big-step derivation. `Expr.evalB B`
is expression evaluation that additionally gets stuck as soon as some
value it produces reaches `B` — not only the value of the whole
expression, but the value of every subexpression, since `sub`, `div`,
the bitwise operators and the right shift can all return a small value
from large arguments, and the machine truncates the arguments too.
`BigStepB B` is then the big-step semantics driven by `Expr.evalB B`,
with the same constructors, the same costs and the same shape; it is a
refinement of `BigStep`, not a competitor to it, and `BigStepB.bigStep`
projects one to the other.

This is one derivation carrying two facts, which is what makes the
reasoning layer cheap: a Hoare-style rule proved for `BigStepB`
establishes cost and boundedness at once, and the plain semantics is
recovered by projection wherever functional correctness is argued.

Values that enter the run from the input tape are not produced by any
expression, so they are bounded separately, by `Env.InpBounded`; this
is the hypothesis that becomes "every entry of the input fits into a
word" at the boundary, where the concept's admissible sets already
carry conditions of that shape.
-/

namespace Lax808846Proofs.Imp

/-- The value `v`, or `none` when `v` does not fit below `B`. -/
def fit (B v : ℕ) : Option ℕ := if v < B then some v else none





/-! ### Bounded evaluation -/

/-- Expression evaluation that also refuses every value reaching `B`.
Every subexpression is checked, not only the outermost one, because the
machine truncates the arguments of an operator as well as its
result. -/
def Expr.evalB (B : ℕ) : Expr → Env → Option ℕ
  | lit n, _ => fit B n
  | var x, σ => fit B (σ.vars x)
  | get a i, σ => (i.evalB B σ).bind fun k => ((σ.arrs a)[k]?).bind (fit B)
  | bin op e f, σ =>
      (e.evalB B σ).bind fun m => (f.evalB B σ).bind fun n => fit B (op.apply m n)







/-- Condition evaluation with the same bound on the two operands. -/
def Cond.evalB (B : ℕ) : Cond → Env → Option Bool
  | eq e f, σ => (e.evalB B σ).bind fun m => (f.evalB B σ).map fun n => m == n
  | lt e f, σ => (e.evalB B σ).bind fun m => (f.evalB B σ).map fun n => decide (m < n)



/-! ### The input tape -/

/-- Every number still on the input tape of `σ` is below `B`. Values
read from the tape are the only ones a run produces that no expression
evaluated, so they are the only ones needing a bound of their own. -/
def Env.InpBounded (B : ℕ) (σ : Env) : Prop := ∀ v ∈ σ.inp, v < B

/-! ### The bounded big-step semantics -/

/-- `BigStepB B c σ σ' k`: the big-step semantics of `Imp`, driven by
bounded evaluation. A derivation is a derivation of `BigStep` in which
every value produced by an expression is below `B`. -/
inductive BigStepB (B : ℕ) : Com → Env → Env → ℕ → Prop
  /-- `skip` changes nothing. -/
  | skip {σ : Env} : BigStepB B .skip σ σ 1
  /-- An assignment evaluates its expression and updates the
  variable. -/
  | assign {σ : Env} {x : String} {e : Expr} {v : ℕ} (h : e.evalB B σ = some v) :
      BigStepB B (.assign x e) σ (σ.setVar x v) (1 + e.size)
  /-- A store evaluates position and value and updates the array; it
  requires the position to be in range. -/
  | store {σ : Env} {a : String} {i e : Expr} {k v : ℕ}
      (hi : i.evalB B σ = some k) (he : e.evalB B σ = some v)
      (hk : k < (σ.arrs a).length) :
      BigStepB B (.store a i e) σ (σ.setArr a k v) (1 + i.size + e.size)
  /-- Costs of a sequence add up. -/
  | seq {c d : Com} {σ σ' σ'' : Env} {k k' : ℕ} :
      BigStepB B c σ σ' k → BigStepB B d σ' σ'' k' →
      BigStepB B (.seq c d) σ σ'' (k + k')
  /-- A conditional whose condition holds runs its first branch. -/
  | ite_true {b : Cond} {c d : Com} {σ σ' : Env} {k : ℕ}
      (hb : b.evalB B σ = some true) (hc : BigStepB B c σ σ' k) :
      BigStepB B (.ite b c d) σ σ' (1 + b.size + k)
  /-- A conditional whose condition fails runs its second branch. -/
  | ite_false {b : Cond} {c d : Com} {σ σ' : Env} {k : ℕ}
      (hb : b.evalB B σ = some false) (hd : BigStepB B d σ σ' k) :
      BigStepB B (.ite b c d) σ σ' (1 + b.size + k)
  /-- A loop whose condition holds runs its body once and then again. -/
  | while_true {b : Cond} {c : Com} {σ σ' σ'' : Env} {k k' : ℕ}
      (hb : b.evalB B σ = some true) (hc : BigStepB B c σ σ' k)
      (hw : BigStepB B (.while b c) σ' σ'' k') :
      BigStepB B (.while b c) σ σ'' (1 + b.size + k + k')
  /-- A loop whose condition fails does nothing. -/
  | while_false {b : Cond} {c : Com} {σ : Env} (hb : b.evalB B σ = some false) :
      BigStepB B (.while b c) σ σ (1 + b.size)
  /-- A read takes the next number off the input. -/
  | read {σ : Env} {x : String} {v : ℕ} {rest : List ℕ} (h : σ.inp = v :: rest) :
      BigStepB B (.read x) σ { σ.setVar x v with inp := rest } 1
  /-- A write appends the value of its expression to the output. -/
  | write {σ : Env} {e : Expr} {v : ℕ} (h : e.evalB B σ = some v) :
      BigStepB B (.write e) σ { σ with out := σ.out ++ [v] } (1 + e.size)







end Lax808846Proofs.Imp

end

-- Solutions.RAM_Lax808846Proofs_Compile
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
The compiler from IMP+ to word-machine programs.

Its whole content is the memory layout, because the machine has no
structure at all: cells addressed by number, an instruction per cell
transfer, absolute jumps. Three regions, all at statically known
addresses since the machine's memory starts empty
(`Lax808846.Ram.initState`):

* cells `0 … temps+1` hold temporaries, one per nesting depth of the
  expression being evaluated plus the two the deepest one needs beside
  it;
* cell `temps + 2 + i` holds the `i`-th scalar variable;
* cell `temps + 2 + p + j + q * i` holds entry `i` of the `j`-th array,
  where `p` is the number of scalars and `q` the number of arrays.

The arrays are *interleaved* rather than laid out in blocks. Their
lengths are not known to the compiler, so blocks would start at
addresses known only at run time; striding by the number of arrays keeps
every address an affine function of the index with statically known
coefficients, at the price of one multiplication per access and a factor
`q` of address space. Address space is nearly free: there is no space
measure, and the only cost is that the word length has to be large
enough to address the last cell, which is what `Layout.span` measures.

Jump targets are absolute, so the compiler takes the address at which
the block it emits will be placed, and the length of a block has to be
known before it is emitted. `size` computes it, and `compile_length`
says the two agree.

### Depths

An expression compiled at depth `d` leaves its value *in cell `d`*, and
may use the cells from `d` upwards. It uses `d + 1` for whichever
operand it compiles second, and the three operators that are not machine
instructions use `d + 2` as well, because both operands have to stay
live while the intermediate `b ∧ c` or `2 ^ c` is formed. `Expr.Ok`
demands `d < L.temps` of every node that has a subexpression, so a
compiled expression writes only cells `d … L.temps + 1` — which is why
the layout reserves `L.temps + 2` cells rather than `L.temps`, and why
every layout literal downstream keeps the `temps` it always had.

The operands of a binary operator are compiled at consecutive depths,
the second operand first: `f` into cell `d`, then `e` into cell `d + 1`,
which cannot disturb cell `d`, and then one block reading `d + 1` and
`d`. Six of the nine operators are machine instructions and their block
is that one instruction; `or`, `xor` and `shiftr` are lowered to the
three- and four-instruction blocks the concept's notes tabulate, whose
correctness is the three identities of `Machine.lean`. This is what
`binCode` is, and it is the only place in the pipeline where the difference
between the reference language's operators and the machine's shows.

Conditions leave *zero exactly when they hold* in cell `0`, so both are
followed by the same `jzero 0`; truncated subtraction is what makes this
possible without a comparison instruction, and it is the reason the
model keeps monus.
-/

namespace Lax808846Proofs.Compile

open Lax808846.Ram Lax808846Proofs.Imp

/-! ### Layouts -/

/-- A memory layout: the scalar names and the array names it can
address, and the number of temporary cells reserved below them. The
cells actually reserved for temporaries are `temps + 2`; see the depth
discipline above. -/
structure Layout where
  /-- The scalar variables, in the order of their cells. -/
  scalars : List String
  /-- The arrays, in the order of their cells. -/
  arrays : List String
  /-- The nesting depth of expressions the layout admits; the cells
  `0 … temps + 1` are the temporaries. -/
  temps : ℕ

/-- The cell holding the scalar variable `x`. -/
def Layout.varAddr (L : Layout) (x : String) : ℕ :=
  L.temps + 2 + L.scalars.idxOf x

/-- The cell holding entry `0` of the array `a`. -/
def Layout.arrBase (L : Layout) (a : String) : ℕ :=
  L.temps + 2 + L.scalars.length + L.arrays.idxOf a



/-- One past every cell the layout addresses, when every index stays
below `B`. -/
def Layout.span (L : Layout) (B : ℕ) : ℕ :=
  L.temps + 2 + L.scalars.length + L.arrays.length * B

/-- The layout runs on words of length `w` when values stay below `B`:
the values fit into a word, and so does every cell the layout
addresses. This is the whole of the word-length hypothesis of the
simulation theorem; it is where the model's `% 2 ^ w` is paid for, and
it is stated as an explicit inequality against `2 ^ w`, as everything
about word lengths in this development is. -/
structure Layout.FitsWords (L : Layout) (B w : ℕ) : Prop where
  /-- The bound admits at least the values `0` and `1`, which the
  compiled comparisons need. -/
  one_lt : 1 < B
  /-- Every value the run produces is a word. -/
  bound : B ≤ 2 ^ w
  /-- Every cell the layout addresses is a word. -/
  span : L.span B ≤ 2 ^ w















/-! ### The block of a binary operator

Six of the nine operators are machine instructions; the other three are
the blocks of the concept's notes. All of them read the second operand
from cell `d + 1` and the first from cell `d`, and leave the result in
cell `d`; the lowered ones use cell `d + 2` as scratch, and `xor` uses
cell `d` itself for the intermediate `b ∨ c`, which is why it needs no
further cell. -/

/-- The instructions computing `op` of the cells `d + 1` and `d` into
cell `d`. -/
def binCode : Bop → ℕ → Program
  | .add, d => [.add d (d + 1) d]
  | .sub, d => [.sub d (d + 1) d]
  | .mul, d => [.mul d (d + 1) d]
  | .div, d => [.div d (d + 1) d]
  | .and, d => [.and d (d + 1) d]
  | .shiftl, d => [.shiftl d (d + 1) d]
  | .or, d => [.and (d + 2) (d + 1) d, .sub (d + 2) d (d + 2), .add d (d + 1) (d + 2)]
  | .xor, d =>
      [.and (d + 2) (d + 1) d, .sub d d (d + 2), .add d (d + 1) d, .sub d d (d + 2)]
  | .shiftr, d => [.set (d + 2) 1, .shiftl (d + 2) (d + 2) d, .div d (d + 1) (d + 2)]

/-- The length of `binCode`. -/
def binLen : Bop → ℕ
  | .or => 3
  | .xor => 4
  | .shiftr => 3
  | _ => 1





/-! ### Code -/

/-- The code turning the index of an entry of `a`, held in the
temporary `d`, into the address of that entry, left in `d`. Cell
`d + 1` is scratch. -/
def Layout.idxCode (L : Layout) (a : String) (d : ℕ) : Program :=
  [.set (d + 1) L.arrays.length, .mul d d (d + 1),
    .set (d + 1) (L.arrBase a), .add d d (d + 1)]

/-- The length of `Layout.idxCode`. -/
def Layout.idxLen (_L : Layout) : ℕ := 4

/-- The constant of the simulation theorem: the compiled program takes
at most this many machine steps per unit of IMP+ cost. It depends
neither on the layout — an array access is four instructions whatever
the number of arrays — nor on the program, the input or the word
length; it is a function of the layout only because every statement
downstream writes it as one. Nothing about it is tight: what forces it
up to ten is the equality condition, which compiles both differences of
its operands, each of which may be a variable read, two instructions
against one unit of IMP+ cost. -/
def Layout.const (_L : Layout) : ℕ := 10

/-- The code evaluating `e` into the temporary `d`, using the
temporaries from `d` upwards. -/
def compileExpr (L : Layout) : Expr → ℕ → Program
  | .lit n, d => [.set d n]
  | .var x, d => [.set d (L.varAddr x), .load d d]
  | .get a i, d => compileExpr L i d ++ L.idxCode a d ++ [.load d d]
  | .bin op e f, d => compileExpr L f d ++ compileExpr L e (d + 1) ++ binCode op d

/-- The number of instructions of `compileExpr`. -/
def esize (L : Layout) : Expr → ℕ
  | .lit _ => 1
  | .var _ => 2
  | .get _ i => esize L i + L.idxLen + 1
  | .bin op e f => esize L f + esize L e + binLen op

/-- The arithmetic expression that is zero exactly when the condition
holds. Truncated subtraction is what makes both conditions expressible,
and it is why the machine needs no comparison instruction; compiling a
condition is then compiling this expression, and the `jzero` that
follows needs to know nothing else. -/
def condExpr : Cond → Expr
  | .eq e f => .bin .add (.bin .sub e f) (.bin .sub f e)
  | .lt e f => .bin .sub (.lit 1) (.bin .sub f e)

/-- The code leaving zero in the temporary `d` exactly when `b`
holds. -/
def compileCond (L : Layout) (b : Cond) (d : ℕ) : Program :=
  compileExpr L (condExpr b) d

/-- The number of instructions of `compileCond`. -/
def bsize (L : Layout) (b : Cond) : ℕ := esize L (condExpr b)

/-- The number of instructions of `compile`. -/
def size (L : Layout) : Com → ℕ
  | .skip => 0
  | .assign _ e => esize L e + 2
  | .store _ i e => esize L i + L.idxLen + esize L e + 1
  | .seq c d => size L c + size L d
  | .ite b c d => bsize L b + 1 + size L d + 1 + size L c
  | .while b c => bsize L b + 2 + size L c + 1
  | .read _ => 1
  | .write e => esize L e + 1

/-- The code running `c`, laid out at address `a`. -/
def compile (L : Layout) : Com → ℕ → Program
  | .skip, _ => []
  | .assign x e, _ => compileExpr L e 0 ++ [.set 1 (L.varAddr x), .store 1 0]
  | .store a i e, _ =>
      compileExpr L i 0 ++ L.idxCode a 0 ++ compileExpr L e 1 ++ [.store 0 1]
  | .seq c d, a => compile L c a ++ compile L d (a + size L c)
  | .ite b c d, a =>
      compileCond L b 0 ++ [.jzero 0 (a + bsize L b + 1 + size L d + 1)] ++
        compile L d (a + bsize L b + 1) ++
        [.jump (a + bsize L b + 1 + size L d + 1 + size L c)] ++
        compile L c (a + bsize L b + 1 + size L d + 1)
  | .while b c, a =>
      compileCond L b 0 ++
        [.jzero 0 (a + bsize L b + 2), .jump (a + bsize L b + 2 + size L c + 1)] ++
        compile L c (a + bsize L b + 2) ++ [.jump a]
  | .read x, _ => [.read (L.varAddr x)]
  | .write e, _ => compileExpr L e 0 ++ [.write 0]

/-- The whole machine program for `c`: its code, then a halt. -/
def compileProgram (L : Layout) (c : Com) : Program :=
  compile L c 0 ++ [.halt]

/-! ### Compilability -/

/-- `e` can be compiled by `L` at depth `d`: every name it mentions is
in the layout, and the temporaries it uses are there. -/
def Expr.Ok (L : Layout) : Expr → ℕ → Prop
  | .lit _, _ => True
  | .var x, _ => x ∈ L.scalars
  | .get a i, d => a ∈ L.arrays ∧ Expr.Ok L i d ∧ d < L.temps
  | .bin _ e f, d => Expr.Ok L f d ∧ Expr.Ok L e (d + 1) ∧ d < L.temps

/-- `b` can be compiled by `L` at depth `d`. -/
def Cond.Ok (L : Layout) (b : Cond) (d : ℕ) : Prop := Expr.Ok L (condExpr b) d

/-- `c` can be compiled by `L`. -/
def Com.Ok (L : Layout) : Com → Prop
  | .skip => True
  | .assign x e => x ∈ L.scalars ∧ Expr.Ok L e 0
  | .store a i e => a ∈ L.arrays ∧ Expr.Ok L i 0 ∧ Expr.Ok L e 1 ∧ 0 < L.temps
  | .seq c d => Com.Ok L c ∧ Com.Ok L d
  | .ite b c d => Cond.Ok L b 0 ∧ Com.Ok L c ∧ Com.Ok L d
  | .while b c => Cond.Ok L b 0 ∧ Com.Ok L c
  | .read x => x ∈ L.scalars
  | .write e => Expr.Ok L e 0 ∧ 0 < L.temps

/-! ### The equations of `Ok`

A definition written by pattern matching gets its equation lemmas —
and, with them, the `splitter` of its match — only when something first
asks for them, and they are created *in the module that asks*. Checking
a concrete program against `Ok` is `simp [Com.Ok, Cond.Ok, Expr.Ok]`,
and every consumer of this kit does it, so without the three lemmas
below the first consumer creates the equations; a consumer in another
package then holds declarations named under `Lax808846Proofs`, which the
archive's namespace rule rejects. Asking here, where the definitions
live, is enough: a later `simp [Com.Ok]` anywhere finds the equations
among its imports and creates nothing.

The splitters carry the names `compileExpr.match_1` and `size.match_1`
rather than `Expr.Ok`'s and `Com.Ok`'s, because Lean shares one matcher
between all matches of the same shape and those two came first.

The statements themselves are the trivial cases of `Ok`, which is all
that is wanted from them; only the `simp` in the proof matters. -/







/-! ### Code lengths

Block lengths are what the absolute jump targets are computed from, so
the emitted code has to have the length `size` predicted, whatever
address it is emitted at. -/









/-! ### The layout is injective

Distinct names, and distinct entries of an array, get distinct cells;
temporaries are below everything else. This is the only place where the
interleaving of the arrays has to be argued: the entry `i` of the `j`-th
array sits at `j + q * i`, and `j < q` recovers both `j` and `i` from
that number as its remainder and quotient. -/

















/-! ### Conditions under the bound

`condExpr` computes with differences of the two operands only, so it
stays below the bound as soon as the operands do — with the single
exception of the literal `1` of `lt`, which is why `FitsWords` asks for
`1 < B`. -/



end Lax808846Proofs.Compile

end

-- Solutions.RAM_Lax808846Proofs_Reasoning
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
The reasoning kit: how an algorithm is actually proved in this stack.

A big-step derivation is the wrong object to hand a user. It fixes the
cost *on the nose* — the constructors produce sums like
`1 + b.size + k + k'`, which no bound is definitionally equal to — and
it forces every loop to be re-proved by hand from the two `while`
constructors. This layer fixes both, and nothing else:

`Run B c σ σ' K` says that `c`, started in `σ`, terminates in `σ'` at a
cost of **at most** `K`, with every value it produces below `B`. Every
construct gets a rule, the rules compose by adding bounds, and slack can
be introduced at any point (`Run.mono`) instead of being pushed to the
end.

The judgment is built on `BigStepB`, not on `BigStep`: one derivation
carries functional correctness, cost and the value bound together, so a
user proves one thing where the alternative — a `BigStep` derivation
plus a separately established bound on the values of the same run —
would have them build the same derivation twice and then argue that the
two are the same. Where a plain-semantics fact is wanted, it is
projected out by `BigStepB.bigStep` (`Run.bigStep` here); that is how
`Run.out_eq` is proved.

The bound is not an extra hypothesis on any rule. Every rule already
asks for the value of the expression it evaluates, and it asks for it in
the bounded form `e.evalB B σ = some v`; the `simp` lemmas of the first
sections turn such a goal, on concrete syntax, into arithmetic — the
value of the expression and of each of its subexpressions is below `B` —
which is exactly the obligation the design intends and no more.

The loop rule is the only one with content. It takes an invariant `I`
and a **potential** `Φ : Env → ℕ`, and asks that one iteration —
condition test included — pay for itself out of the potential:
`1 + b.size + K + Φ σ' ≤ Φ σ`. Termination and the cost bound then come
out together, because a potential that pays for a nonzero cost is also
a variant; the loop costs at most `Φ σ + 1 + b.size`, the extra term
being the test that fails. Amortized arguments are the reason for the
potential form: a graph scan cannot bound the cost of one outer
iteration by a constant, but it can pay for it out of "queue entries
left plus adjacency slots left". `Run.while_count` is the uniform-cost
special case, an invariant and a variant, for the loops where that
suffices.
-/

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

/-! ### Reading an updated environment

Every rule below produces an environment written as a chain of updates,
and every use reads a variable back out of such a chain. These are the
lemmas that collapse the chain; they are `simp` lemmas, so the reader
of an algorithm proof sees `simp` where a proof against the raw
semantics had explicit `Env.setVar` unfolding at every step. -/



















/-! ### Arrays as functions

An IMP+ array is a list, but an invariant wants to say what is *at*
each position, not what the list is. `arrOf n f` is the array of length
`n` whose entry `i` is `f i`; an invariant then names the function, a
store updates the function at a point, and a read is a function
application. -/















/-! ### Bounded evaluation of concrete syntax

The side condition of every rule below is a bounded evaluation
`e.evalB B σ = some v`. On the concrete syntax of an actual program
these lemmas reduce such a goal to arithmetic: the value of every
subexpression is exhibited, and what is left to prove is that each of
them is below `B`. This is the whole of the value-bound obligation the
pipeline asks for, and it arrives one expression at a time, where the
values are in front of the reader, rather than as a separate pass over
the program. -/













/-! ### Introducing a bounded evaluation

The lemmas above are what `simp` needs; these are what `exact` needs.
The side condition of a rule is `e.evalB B σ = some v` with `v` already
named by the caller, and the side condition of the loop rule is the
weaker `∃ v, b.evalB B σ = some v` — a condition whose two operands
have values has one too, whichever it is. Stated as introduction rules
these are discharged by naming the value of each subexpression and its
bound, which is what a caller has in hand, instead of by first guessing
the truth value of the condition and then unfolding it again. -/





















/-! ### Counting the size of concrete syntax

An algorithm proof should never be told what a concrete expression
costs; with these the cost of a straight-line block is arithmetic on
numerals. The nine named operators get a lemma each alongside the one
for `bin`, so that a cost computation on a program written with the
abbreviations is simplified by lemmas carrying the same names. -/

















/-! ### The bounded judgment -/

/-- `Run B c σ σ' K`: started in `σ`, the command `c` terminates in `σ'`
at a cost of at most `K`, every value it produces staying below `B`.
This is the judgment every algorithm proof is written in; the cost is a
bound rather than a value, so the arithmetic of the cost model never has
to be matched syntactically. -/
def Run (B : ℕ) (c : Com) (σ σ' : Env) (K : ℕ) : Prop := ∃ k ≤ K, BigStepB B c σ σ' k





























/-! ### The loop rule -/





/-! ### The one frame condition that is worth having generically

A phase lemma states its own frame conditions on the variables and
arrays it touches, because those differ from phase to phase. The output
tape is the exception: almost every phase leaves it alone, and it is
syntactically evident which ones do. So it is stated once, for all
commands that contain no `write`, and no invariant has to carry it. -/









end Lax808846Proofs.Reasoning

end

-- Solutions.RAM_Lax759944Proofs_Microcode
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

/-!
Proof-internal accumulator microcode for the Turing simulator. Based on the
Lax759944Proofs.Legacy accumulator semantics at d35ba57ad420ce6a6d3c763aa7f6a4a8be1d406d,
with a word-complement operation added for the cell-to-cell translation.

This is NOT the public RAM model. Public programs and executions use
`Lax759944Proofs.Legacy.Ram`; a separate checked translation must connect them to this
intermediate language. The accumulator is represented by a Turing work tape.
-/

namespace Lax759944Proofs.Microcode

/-- An operand: a literal, the contents of a memory cell, or the
contents of the cell addressed by a memory cell. -/
inductive Op
  /-- The literal number `n`. -/
  | lit (n : ℕ)
  /-- The contents of cell `a`. -/
  | mem (a : ℕ)
  /-- The contents of the cell whose address is the contents of cell
  `a`. -/
  | ind (a : ℕ)

/-- An instruction: tape transfers, accumulator transfers, arithmetic,
bitwise operations, jumps, and halting. -/
inductive Instr
  /-- Read the next number of the input tape into cell `a`. -/
  | read (a : ℕ)
  /-- Append the value of the operand to the output tape. -/
  | write (o : Op)
  /-- Load the operand into the accumulator. -/
  | load (o : Op)
  /-- Store the accumulator into cell `a`. -/
  | store (a : ℕ)
  /-- Store the accumulator into the cell addressed by cell `a`. -/
  | storeInd (a : ℕ)
  /-- Add the operand to the accumulator, wrapping around modulo
  `2 ^ w`. -/
  | add (o : Op)
  /-- Subtract the operand from the accumulator, truncated at zero
  rather than wrapping around. -/
  | sub (o : Op)
  /-- Multiply the accumulator by the operand, wrapping around modulo
  `2 ^ w`. -/
  | mul (o : Op)
  /-- Divide the accumulator by the operand, rounding towards zero;
  division by zero yields zero. -/
  | div (o : Op)
  /-- Replace the accumulator by its bitwise conjunction with the
  operand. -/
  | and (o : Op)
  /-- Replace the accumulator by its bitwise disjunction with the
  operand. -/
  | or (o : Op)
  /-- Replace the accumulator by its bitwise exclusive or with the
  operand. -/
  | xor (o : Op)
  /-- Complement the accumulator's low word; the operand is ignored. -/
  | compl (o : Op)
  /-- Shift the accumulator left by the operand many bits, wrapping
  around modulo `2 ^ w`; a shift by `w` or more yields zero. -/
  | shiftl (o : Op)
  /-- Shift the accumulator right by the operand many bits, discarding
  the bits shifted out. -/
  | shiftr (o : Op)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if the accumulator is zero. -/
  | jzero (l : ℕ)
  /-- Continue at instruction `l` if the accumulator is positive. -/
  | jgtz (l : ℕ)
  /-- Halt. -/
  | halt

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr



/-- The value of an operand in a memory, at word length `w`: every
address is taken modulo `2 ^ w` before the cell it names is read. -/
def Op.value (w : ℕ) : Op → (ℕ → ℕ) → ℕ
  | lit n, _ => n
  | mem a, m => m (a % 2 ^ w)
  | ind a, m => m (m (a % 2 ^ w) % 2 ^ w)













end Lax759944Proofs.Microcode


end

-- Solutions.RAM_Lax759944Proofs_RamToTM_SparseMemory
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

/-- A finite association list representing the nonzero/touched fragment of
RAM memory. Missing cells read as zero. -/
def SparseMemory := List (ℕ × ℕ)

def SparseMemory.read : SparseMemory → ℕ → ℕ
  | [], _ => 0
  | (a, v) :: m, b => if b = a then v else SparseMemory.read m b











/-- Word-normalized sparse write, matching the RAM's address and value
normalization.  The sparse representation is a write log: the newest binding
is prepended, and `read` selects the first matching address.  Keeping stale
bindings is extensionally harmless and makes a concrete TM write a constant
number of word transfers instead of a scan through memory. -/
def SparseMemory.write (w : ℕ) (m : SparseMemory) (a v : ℕ) : SparseMemory :=
  (a % 2 ^ w, v % 2 ^ w) :: m









/-- A RAM state whose memory is represented sparsely. -/
structure SparseState where
  pc : ℕ
  acc : ℕ
  mem : SparseMemory
  inp : List ℕ
  out : List ℕ













def sparseValue (w : ℕ) (o : Op) (m : SparseMemory) : ℕ :=
  o.value w m.read

def sparseEffect (w : ℕ) : Instr → SparseState → Option SparseState
  | .read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := s.mem.write w a v, inp := s.inp.tail }
  | .write o, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [sparseValue w o s.mem % 2 ^ w] }
  | .load o, s =>
      some { s with pc := s.pc + 1, acc := sparseValue w o s.mem % 2 ^ w }
  | .store a, s =>
      some { s with pc := s.pc + 1, mem := s.mem.write w a s.acc }
  | .storeInd a, s =>
      some { s with pc := s.pc + 1, mem := s.mem.write w (s.mem.read (a % 2 ^ w)) s.acc }
  | .add o, s =>
      some { s with pc := s.pc + 1, acc := (s.acc + sparseValue w o s.mem) % 2 ^ w }
  | .sub o, s =>
      some { s with pc := s.pc + 1, acc := (s.acc - sparseValue w o s.mem) % 2 ^ w }
  | .mul o, s =>
      some { s with pc := s.pc + 1, acc := (s.acc * sparseValue w o s.mem) % 2 ^ w }
  | .div o, s =>
      some { s with pc := s.pc + 1, acc := (s.acc / sparseValue w o s.mem) % 2 ^ w }
  | .and o, s =>
      some { s with pc := s.pc + 1, acc := Nat.land s.acc (sparseValue w o s.mem) % 2 ^ w }
  | .or o, s =>
      some { s with pc := s.pc + 1, acc := Nat.lor s.acc (sparseValue w o s.mem) % 2 ^ w }
  | .xor o, s =>
      some { s with pc := s.pc + 1, acc := Nat.xor s.acc (sparseValue w o s.mem) % 2 ^ w }
  | .compl _, s =>
      some { s with pc := s.pc + 1, acc := (2 ^ w - 1 - s.acc % 2 ^ w) % 2 ^ w }
  | .shiftl o, s =>
      some { s with pc := s.pc + 1, acc := s.acc * 2 ^ sparseValue w o s.mem % 2 ^ w }
  | .shiftr o, s =>
      some { s with pc := s.pc + 1, acc := s.acc / 2 ^ sparseValue w o s.mem % 2 ^ w }
  | .jump l, s => some { s with pc := l }
  | .jzero l, s => some { s with pc := if s.acc = 0 then l else s.pc + 1 }
  | .jgtz l, s => some { s with pc := if 0 < s.acc then l else s.pc + 1 }
  | .halt, _ => none





def sparseStep (w : ℕ) (p : Program) (s : SparseState) : Option SparseState :=
  p[s.pc]?.bind fun i => sparseEffect w i s

















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FixedWord
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM



/-- The low `w` bits of `n`, padded to exactly `w` bits. -/
def fixedBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => n.bodd :: fixedBits w n.div2































/-- One-bit full adder, returning `(sum, carry)`. -/
def fullAdder (a b carry : Bool) : Bool × Bool :=
  (xor (xor a b) carry, (a && b) || (carry && xor a b))



















/-- One-bit full subtractor, returning `(difference, borrow)`. -/
def fullSubtractor (a b borrow : Bool) : Bool × Bool :=
  (xor (xor a b) borrow,
    ((!a) && (b || borrow)) || (b && borrow))























































































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_BitMacros
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve definition unfolding in generated Fintype instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-- Finite local control used by the ripple-carry TM2 statement. -/
structure AddControl where
  carry : Bool
  left : Option Bool
  right : Option Bool
  deriving DecidableEq, Fintype, Inhabited

def AddControl.setLeft (s : AddControl) (a : Option Bool) : AddControl :=
  { s with left := a }

def AddControl.setRight (s : AddControl) (b : Option Bool) : AddControl :=
  { s with right := b }

def AddControl.sumBit (s : AddControl) : Bool :=
  (fullAdder (s.left.getD false) (s.right.getD false) s.carry).1

def AddControl.advance (s : AddControl) : AddControl :=
  { carry := (fullAdder (s.left.getD false) (s.right.getD false) s.carry).2,
    left := none, right := none }

/-- One TM2 statement implementing a complete iteration of ripple-carry
addition. The two operands are popped from their stacks and the result bit is
pushed onto a third (therefore reversed) stack. Empty left input exits to
`done`. Equal operand lengths are an invariant of callers. -/
def addIteration {K Λ : Type} [DecidableEq K]
    (left right result : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ AddControl :=
  .pop left AddControl.setLeft <|
    .branch (fun s => s.left.isNone)
      (.goto fun _ => done)
      (.pop right AddControl.setRight <|
        .push result AddControl.sumBit <|
          .load AddControl.advance <|
            .goto fun _ => loop)





/-! A concrete finite TM2 component and its whole-loop correctness theorem.
This component is later embedded into the RAM interpreter's larger control
graph. -/

inductive AddStack | left | right | result
  deriving DecidableEq, Fintype, Inhabited

inductive AddLabel | loop | done
  deriving DecidableEq, Fintype, Inhabited



















/-! Stack reversal/move macro. -/

structure MoveControl where
  held : Option Bool
  deriving DecidableEq, Fintype, Inhabited

def moveIteration {K Λ : Type} [DecidableEq K]
    (source target : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ MoveControl :=
  .pop source (fun _ b => ⟨b⟩) <|
    .branch (fun s => s.held.isNone)
      (.goto fun _ => done)
      (.push target (fun s => s.held.getD false) <|
        .load (fun _ => ⟨none⟩) <|
          .goto fun _ => loop)





















/-! Pointwise binary Boolean-operation macro (`and`, `or`, and `xor`). -/

structure ZipControl where
  left : Option Bool
  right : Option Bool
  deriving DecidableEq, Fintype, Inhabited

def zipIteration {K Λ : Type} [DecidableEq K] (f : Bool → Bool → Bool)
    (left right result : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ ZipControl :=
  .pop left (fun s a => { s with left := a }) <|
    .branch (fun s => s.left.isNone)
      (.goto fun _ => done)
      (.pop right (fun s b => { s with right := b }) <|
        .push result (fun s => f (s.left.getD false) (s.right.getD false)) <|
          .load (fun _ => ⟨none, none⟩) <|
            .goto fun _ => loop)

















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CompareMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 definition unfolding during elaboration.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure CompareControl where
  less : Bool
  left : Option Bool
  right : Option Bool
  deriving DecidableEq, Fintype, Inhabited



























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_SubtractMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure SubControl where
  borrow : Bool
  left : Option Bool
  right : Option Bool
  deriving DecidableEq, Fintype, Inhabited

def SubControl.differenceBit (s : SubControl) : Bool :=
  (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).1

def SubControl.advance (s : SubControl) : SubControl :=
  { borrow := (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).2,
    left := none, right := none }

def subIteration {K Λ : Type} [DecidableEq K]
    (left right result : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ SubControl :=
  .pop left (fun s a => { s with left := a }) <|
    .branch (fun s => s.left.isNone)
      (.goto fun _ => done)
      (.pop right (fun s b => { s with right := b }) <|
        .push result SubControl.differenceBit <|
          .load SubControl.advance <|
            .goto fun _ => loop)



















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ShiftMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive ShiftStack | source | temp | result
  deriving DecidableEq, Fintype, Inhabited

inductive ShiftLabel | first | discard | second | prepend | done
  deriving DecidableEq, Fintype, Inhabited

def shiftMachine : Turing.FinTM2 where
  K := ShiftStack
  k₀ := .source
  k₁ := .result
  Γ _ := Bool
  Λ := ShiftLabel
  main := .first
  σ := MoveControl
  initialState := default
  m
    | .first => moveIteration .source .temp .first .discard
    | .discard => .pop .temp (fun _ _ => ⟨none⟩) (.goto fun _ => .second)
    | .second => moveIteration .temp .result .second .prepend
    | .prepend => .push .result (fun _ => false) (.goto fun _ => .done)
    | .done => .halt



























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_SparseEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

/-- Finite work alphabet for serialized word lists and sparse memory. -/
inductive SparseSymbol
  | bit (value : Bool)
  | wordEnd
  | cellEnd
  | memoryEnd
  | inputEnd
  | outputEnd
  deriving DecidableEq, Fintype, Inhabited

def encodeFixedWord (w n : ℕ) : List SparseSymbol :=
  (fixedBits w n).map SparseSymbol.bit ++ [.wordEnd]



def encodeWordList (w : ℕ) (xs : List ℕ) : List SparseSymbol :=
  xs.flatMap (encodeFixedWord w)



def encodeSparseCell (w : ℕ) (cell : ℕ × ℕ) : List SparseSymbol :=
  encodeFixedWord w cell.1 ++ encodeFixedWord w cell.2 ++ [.cellEnd]



def encodeSparseMemory (w : ℕ) (m : SparseMemory) : List SparseSymbol :=
  m.flatMap (encodeSparseCell w)











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_WordTransferMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure WordTransferControl where
  held : Option SparseSymbol
  deriving DecidableEq, Fintype, Inhabited

























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_SparseInvariant
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

def SparseMemory.Normalized (w : ℕ) : SparseMemory → Prop
  | [] => True
  | (a, v) :: m => a < 2 ^ w ∧ v < 2 ^ w ∧ Normalized w m



















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_SymbolMoveMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure SymbolMoveControl where
  held : Option SparseSymbol
  deriving DecidableEq, Fintype, Inhabited

def symbolMoveIteration {K Λ : Type} [DecidableEq K]
    (source target : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => SparseSymbol) Λ SymbolMoveControl :=
  .pop source (fun _ a => ⟨a⟩) <|
    .branch (fun s => s.held.isNone)
      (.goto fun _ => done)
      (.push target (fun s => s.held.getD (.bit false)) <|
        .load (fun _ => default) <| .goto fun _ => loop)

inductive SymbolMoveStack | source | target
  deriving DecidableEq, Fintype, Inhabited

inductive SymbolMoveLabel | loop | done
  deriving DecidableEq, Fintype, Inhabited

def symbolMoveMachine : Turing.FinTM2 where
  K := SymbolMoveStack
  k₀ := .source
  k₁ := .target
  Γ _ := SparseSymbol
  Λ := SymbolMoveLabel
  main := .loop
  σ := SymbolMoveControl
  initialState := default
  m
    | .loop => symbolMoveIteration .source .target .loop .done
    | .done => .halt

























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_LookupCellMachine
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure LookupCellControl where
  held : Option SparseSymbol
  equal : Bool
  left : Option SparseSymbol
  right : Option SparseSymbol
  deriving DecidableEq, Fintype, Inhabited





def LookupCellControl.clearHeld (s : LookupCellControl) : LookupCellControl :=
  { s with held := none }

def LookupCellControl.compareAdvance (s : LookupCellControl) : LookupCellControl :=
  { held := none, equal := s.equal && decide (s.left = s.right),
    left := none, right := none }

def lookupCellWordIteration {K Λ : Type} [DecidableEq K]
    (source target backup : K) (loop next : Λ) :
    TM2.Stmt (fun _ : K => SparseSymbol) Λ LookupCellControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held = some .wordEnd)
      (.push backup (fun _ => .wordEnd) <|
        .load LookupCellControl.clearHeld <| .goto fun _ => next)
      (.push target (fun s => s.held.getD (.bit false)) <|
        .push backup (fun s => s.held.getD (.bit false)) <|
          .load LookupCellControl.clearHeld <| .goto fun _ => loop)

def lookupCellCompareIteration {K Λ : Type} [DecidableEq K]
    (left right leftBackup rightBackup : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => SparseSymbol) Λ LookupCellControl :=
  .pop left (fun s a => { s with left := a }) <|
    .branch (fun s => s.left.isNone)
      (.goto fun _ => done)
      (.pop right (fun s b => { s with right := b }) <|
        .push leftBackup (fun s => s.left.getD (.bit false)) <|
          .push rightBackup (fun s => s.right.getD (.bit false)) <|
            .load LookupCellControl.compareAdvance <| .goto fun _ => loop)

































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_LookupScanMachine
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive LookupScanStack
  | source | address | value | cellBackup | query | addressBackup | queryBackup
  | processed | trash
  deriving DecidableEq, Fintype, Inhabited

inductive LookupScanLabel
  | scan | address | value | cellEnd | compare | decide
  | restoreQuery | discardAddress | discardValue | preserveCell | moveCell
  | afterCleanup | afterMove
  | restoreFound | restoreMissing | found | missing
  deriving DecidableEq, Fintype, Inhabited

def lookupScanMoveIteration {K Λ : Type} [DecidableEq K]
    (source target : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => SparseSymbol) Λ LookupCellControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load LookupCellControl.clearHeld <| .goto fun _ => done)
      (.push target (fun s => s.held.getD (.bit false)) <|
        .load LookupCellControl.clearHeld <| .goto fun _ => loop)

def lookupScanDiscardIteration {K Λ : Type} [DecidableEq K]
    (source : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => SparseSymbol) Λ LookupCellControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load LookupCellControl.clearHeld <| .goto fun _ => done)
      (.load LookupCellControl.clearHeld <| .goto fun _ => loop)

def lookupScanMachine : Turing.FinTM2 where
  K := LookupScanStack
  k₀ := .source
  k₁ := .value
  Γ _ := SparseSymbol
  Λ := LookupScanLabel
  main := .scan
  σ := LookupCellControl
  initialState := ⟨none, true, none, none⟩
  m
    | .scan =>
        .peek .source (fun s a => { s with held := a }) <|
          .branch (fun s => s.held = some .memoryEnd)
            (.load LookupCellControl.clearHeld <| .goto fun _ => .restoreMissing)
            (.load (fun s => { (LookupCellControl.clearHeld s) with equal := true }) <|
              .goto fun _ => .address)
    | .address => lookupCellWordIteration .source .address .cellBackup .address .value
    | .value => lookupCellWordIteration .source .value .cellBackup .value .cellEnd
    | .cellEnd =>
        .pop .source (fun s a => { s with held := a }) <|
          .push .cellBackup (fun s => s.held.getD .cellEnd) <|
            .load LookupCellControl.clearHeld <| .goto fun _ => .compare
    | .compare => lookupCellCompareIteration .address .query
        .addressBackup .queryBackup .compare .decide
    | .decide => .branch LookupCellControl.equal
        (.goto fun _ => .restoreQuery) (.goto fun _ => .restoreQuery)
    | .restoreQuery => lookupScanMoveIteration .queryBackup .query
        .restoreQuery .discardAddress
    | .discardAddress => lookupScanDiscardIteration .addressBackup
        .discardAddress .afterCleanup
    | .afterCleanup => .branch LookupCellControl.equal
        (.goto fun _ => .preserveCell) (.goto fun _ => .discardValue)
    | .discardValue => lookupScanDiscardIteration .value .discardValue .preserveCell
    | .preserveCell => lookupScanMoveIteration .cellBackup .trash
        .preserveCell .moveCell
    | .moveCell => lookupScanMoveIteration .trash .processed .moveCell .afterMove
    | .afterMove => .branch LookupCellControl.equal
        (.goto fun _ => .restoreFound) (.goto fun _ => .scan)
    | .restoreFound => lookupScanMoveIteration .processed .source .restoreFound .found
    | .restoreMissing => lookupScanMoveIteration .processed .source .restoreMissing .missing
    | .found => .halt
    | .missing => .halt

































































































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ZeroWordMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure ZeroWordControl where
  held : Option SparseSymbol
  deriving DecidableEq, Fintype, Inhabited

inductive ZeroWordStack | query | backup | result
  deriving DecidableEq, Fintype, Inhabited

inductive ZeroWordLabel | fill | restore | done
  deriving DecidableEq, Fintype, Inhabited

def zeroWordMachine : Turing.FinTM2 where
  K := ZeroWordStack
  k₀ := .query
  k₁ := .result
  Γ _ := SparseSymbol
  Λ := ZeroWordLabel
  main := .fill
  σ := ZeroWordControl
  initialState := default
  m
    | .fill =>
        .pop .query (fun _ a => ⟨a⟩) <|
          .branch (fun s => s.held.isNone)
            (.load (fun _ => default) <| .goto fun _ => .restore)
            (.push .backup (fun s => s.held.getD (.bit false)) <|
              .push .result (fun _ => .bit false) <|
                .load (fun _ => default) <| .goto fun _ => .fill)
    | .restore =>
        .pop .backup (fun _ a => ⟨a⟩) <|
          .branch (fun s => s.held.isNone)
            (.load (fun _ => default) <| .goto fun _ => .done)
            (.push .query (fun s => s.held.getD (.bit false)) <|
              .load (fun _ => default) <| .goto fun _ => .restore)
    | .done => .halt

def zeroWordProgram : ZeroWordLabel →
    TM2.Stmt (fun _ : ZeroWordStack => SparseSymbol)
      ZeroWordLabel ZeroWordControl := zeroWordMachine.m



































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_LiteralWordMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2







inductive LiteralWordStack | query | backup | result
  deriving DecidableEq, Fintype, Inhabited

inductive LiteralWordLabel | emit | restore | done
  deriving DecidableEq, Fintype, Inhabited



























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_PrependCellMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! A sparse write is represented by prepending a serialized cell.  The
address and value inputs are reversed fixed-width words, which is the common
orientation used by the lookup and arithmetic macros. -/

structure PrependCellControl where
  held : Option SparseSymbol
  deriving DecidableEq, Fintype, Inhabited

inductive PrependCellStack | address | value | memory
  deriving DecidableEq, Fintype, Inhabited

inductive PrependCellLabel
  | cellEnd | valueEnd | value | addressEnd | address | done
  deriving DecidableEq, Fintype, Inhabited

def prependCellMoveIteration {K Λ : Type} [DecidableEq K]
    (source target : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => SparseSymbol) Λ PrependCellControl :=
  .pop source (fun _ a => ⟨a⟩) <|
    .branch (fun s => s.held.isNone)
      (.goto fun _ => done)
      (.push target (fun s => s.held.getD (.bit false)) <|
        .load (fun _ => default) <| .goto fun _ => loop)

def prependCellMachine : Turing.FinTM2 where
  K := PrependCellStack
  k₀ := .address
  k₁ := .memory
  Γ _ := SparseSymbol
  Λ := PrependCellLabel
  main := .cellEnd
  σ := PrependCellControl
  initialState := default
  m
    | .cellEnd => .push .memory (fun _ => .cellEnd) <| .goto fun _ => .valueEnd
    | .valueEnd => .push .memory (fun _ => .wordEnd) <| .goto fun _ => .value
    | .value => prependCellMoveIteration .value .memory .value .addressEnd
    | .addressEnd => .push .memory (fun _ => .wordEnd) <| .goto fun _ => .address
    | .address => prependCellMoveIteration .address .memory .address .done
    | .done => .halt



























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_AlphabetEmbedding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! Transport a TM2 statement across a split injection/retraction of its
alphabet.  Correct executions only see encoded symbols; the retraction makes
the transported statement total on arbitrary ambient configurations. -/

def mapAlphabetStmt {α β K Λ σ : Type} [DecidableEq K]
    (encode : α → β) (decode : β → α) :
    TM2.Stmt (fun _ : K => α) Λ σ → TM2.Stmt (fun _ : K => β) Λ σ
  | .push k f q => .push k (fun s => encode (f s))
      (mapAlphabetStmt encode decode q)
  | .peek k f q => .peek k (fun s a => f s (a.map decode))
      (mapAlphabetStmt encode decode q)
  | .pop k f q => .pop k (fun s a => f s (a.map decode))
      (mapAlphabetStmt encode decode q)
  | .load f q => .load f (mapAlphabetStmt encode decode q)
  | .branch f q₁ q₂ => .branch f
      (mapAlphabetStmt encode decode q₁) (mapAlphabetStmt encode decode q₂)
  | .goto f => .goto f
  | .halt => .halt









def mapAlphabetProgram {α β K Λ σ : Type} [DecidableEq K]
    (encode : α → β) (decode : β → α)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ) :
    Λ → TM2.Stmt (fun _ : K => β) Λ σ :=
  fun l => mapAlphabetStmt encode decode (program l)







def sparseBitEncode (b : Bool) : SparseSymbol := .bit b

def sparseBitDecode : SparseSymbol → Bool
  | .bit b => b
  | _ => false



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MultiplyMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! A width-uniform schoolbook multiplier.  The outer loop consumes the
multiplier least-significant bit first.  A true bit performs one ripple add;
every round shifts the multiplicand left once. -/

structure MulControl where
  selected : Option Bool
  carry : Bool
  left : Option Bool
  right : Option Bool
  held : Option Bool
  deriving DecidableEq, Fintype, Inhabited

def MulControl.sumBit (s : MulControl) : Bool :=
  (fullAdder (s.left.getD false) (s.right.getD false) s.carry).1

def MulControl.addAdvance (s : MulControl) : MulControl :=
  { s with
    carry := (fullAdder (s.left.getD false) (s.right.getD false) s.carry).2,
    left := none, right := none }

def MulControl.clearHeld (s : MulControl) : MulControl := { s with held := none }

inductive MulStack
  | multiplier | multiplicand | accumulator | multiplicandBackup | sumReverse | shiftTemp
  deriving DecidableEq, Fintype, Inhabited

inductive MulLabel
  | outer | select | add | restoreMultiplicand | restoreSum
  | shiftFirst | shiftDiscard | shiftSecond | shiftPrepend | done
  deriving DecidableEq, Fintype, Inhabited

def mulMoveIteration {K Λ : Type} [DecidableEq K]
    (source target : K) (loop done : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ MulControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load MulControl.clearHeld <| .goto fun _ => done)
      (.push target (fun s => s.held.getD false) <|
        .load MulControl.clearHeld <| .goto fun _ => loop)















































































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_DivideMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! A width-uniform restoring divider.  The dividend is supplied most
significant bit first, while divisor and remainder words are little endian.
Each round shifts one dividend bit into the remainder and performs one ripple
subtraction.  A borrow restores the old remainder; otherwise the difference
is retained.  Thus the number of machine steps is quadratic in the word
width, independently of the numeric values. -/

structure DivControl where
  held : Option Bool
  selected : Bool
  left : Option Bool
  right : Option Bool
  borrow : Bool
  divisorNonzero : Bool
  deriving DecidableEq, Fintype, Inhabited

def DivControl.clearHeld (s : DivControl) : DivControl := { s with held := none }

def DivControl.diffBit (s : DivControl) : Bool :=
  (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).1

def DivControl.subAdvance (s : DivControl) : DivControl :=
  { s with
    borrow := (fullSubtractor (s.left.getD false) (s.right.getD false) s.borrow).2,
    left := none, right := none }

inductive DivStack
  | dividend | divisor | remainder | quotient
  | divisorBackup | remainderBackup | differenceReverse | shiftTemp
  deriving DecidableEq, Fintype, Inhabited

inductive DivLabel
  | inspectDivisor | restoreInspectedDivisor | dispatch
  | zeroLoop | outer
  | shiftFirst | shiftDiscard | shiftSecond | shiftPrepend
  | subtract | restoreDivisor | choose
  | discardDifference | restoreRemainder
  | discardOldRemainder | restoreDifference | emit
  | done
  deriving DecidableEq, Fintype, Inhabited

def divMoveIteration (source target : DivStack) (loop done : DivLabel) :
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load DivControl.clearHeld <| .goto fun _ => done)
      (.push target (fun s => s.held.getD false) <|
        .load DivControl.clearHeld <| .goto fun _ => loop)

def divDiscardIteration (source : DivStack) (loop done : DivLabel) :
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  .pop source (fun s a => { s with held := a }) <|
    .branch (fun s => s.held.isNone)
      (.load DivControl.clearHeld <| .goto fun _ => done)
      (.load DivControl.clearHeld <| .goto fun _ => loop)

def divMachine : Turing.FinTM2 where
  K := DivStack
  k₀ := .dividend
  k₁ := .quotient
  Γ _ := Bool
  Λ := DivLabel
  main := .inspectDivisor
  σ := DivControl
  initialState := default
  m
    | .inspectDivisor =>
        .pop .divisor (fun s a =>
          { s with
            held := a,
            divisorNonzero := s.divisorNonzero || a.getD false }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .restoreInspectedDivisor)
            (.push .divisorBackup (fun s => s.held.getD false) <|
              .load DivControl.clearHeld <| .goto fun _ => .inspectDivisor)
    | .restoreInspectedDivisor =>
        divMoveIteration .divisorBackup .divisor .restoreInspectedDivisor .dispatch
    | .dispatch => .branch DivControl.divisorNonzero
        (.goto fun _ => .outer) (.goto fun _ => .zeroLoop)
    | .zeroLoop =>
        .pop .dividend (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .done)
            (.push .quotient (fun _ => false) <|
              .load DivControl.clearHeld <| .goto fun _ => .zeroLoop)
    | .outer =>
        .pop .dividend (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DivControl.clearHeld <| .goto fun _ => .done)
            (.load (fun s => { s with selected := s.held.getD false, held := none }) <|
              .goto fun _ => .shiftFirst)
    | .shiftFirst => divMoveIteration .remainder .shiftTemp .shiftFirst .shiftDiscard
    | .shiftDiscard =>
        .pop .shiftTemp (fun s _ => DivControl.clearHeld s) <|
          .goto fun _ => .shiftSecond
    | .shiftSecond => divMoveIteration .shiftTemp .remainder .shiftSecond .shiftPrepend
    | .shiftPrepend =>
        .push .remainder DivControl.selected <|
          .load (fun s => { s with borrow := false, left := none, right := none }) <|
            .goto fun _ => .subtract
    | .subtract =>
        .pop .remainder (fun s a => { s with left := a }) <|
          .branch (fun s => s.left.isNone)
            (.goto fun _ => .restoreDivisor)
            (.pop .divisor (fun s b => { s with right := b }) <|
              .push .remainderBackup (fun s => s.left.getD false) <|
                .push .divisorBackup (fun s => s.right.getD false) <|
                  .push .differenceReverse DivControl.diffBit <|
                    .load DivControl.subAdvance <| .goto fun _ => .subtract)
    | .restoreDivisor =>
        divMoveIteration .divisorBackup .divisor .restoreDivisor .choose
    | .choose => .branch DivControl.borrow
        (.goto fun _ => .discardDifference) (.goto fun _ => .discardOldRemainder)
    | .discardDifference =>
        divDiscardIteration .differenceReverse .discardDifference .restoreRemainder
    | .restoreRemainder =>
        divMoveIteration .remainderBackup .remainder .restoreRemainder .emit
    | .discardOldRemainder =>
        divDiscardIteration .remainderBackup .discardOldRemainder .restoreDifference
    | .restoreDifference =>
        divMoveIteration .differenceReverse .remainder .restoreDifference .emit
    | .emit =>
        .push .quotient (fun s => !s.borrow) <|
          .load (fun s =>
            { s with
              held := none, selected := false, left := none, right := none,
              borrow := false }) <|
            .goto fun _ => .outer
    | .done => .halt





























































































































/-- A single quadratic bound covering both branches. -/
def divRunTimeBound (w : ℕ) : ℕ :=
  (w + 1) * (6 * (w + 1) + 14) + 5









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_DispatcherControl
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

/-! Finite control used by the RAM interpreter.  For a fixed program all
in-range program counters are finite; every out-of-range counter has the same
observable behavior (instruction fetch fails), so they share one sentinel. -/

abbrev BoundedPC (p : Program) := Fin (p.length + 1)

instance (p : Program) : Inhabited (BoundedPC p) := ⟨0, by omega⟩

def boundPC (p : Program) (pc : ℕ) : BoundedPC p :=
  if h : pc < p.length then ⟨pc, by omega⟩ else ⟨p.length, by omega⟩



def BoundedPC.fetch {p : Program} (pc : BoundedPC p) : Option Instr :=
  if pc.val < p.length then p[pc.val]? else none









def nextPC (p : Program) (pc : BoundedPC p) : BoundedPC p :=
  boundPC p (pc.val + 1)

def jumpPC (p : Program) (target : ℕ) : BoundedPC p :=
  boundPC p target





/-- The finite dispatcher only needs the constructor class in its dynamic
control; operands and jump targets are recovered from the fixed program table. -/
inductive InstrClass
  | read | write | load | store | storeInd
  | add | sub | mul | div | and | or | xor | compl | shiftl | shiftr
  | jump | jzero | jgtz | halt
  deriving DecidableEq, Fintype, Inhabited

def instrClass : Instr → InstrClass
  | .read _ => .read
  | .write _ => .write
  | .load _ => .load
  | .store _ => .store
  | .storeInd _ => .storeInd
  | .add _ => .add
  | .sub _ => .sub
  | .mul _ => .mul
  | .div _ => .div
  | .and _ => .and
  | .or _ => .or
  | .xor _ => .xor
  | .compl _ => .compl
  | .shiftl _ => .shiftl
  | .shiftr _ => .shiftr
  | .jump _ => .jump
  | .jzero _ => .jzero
  | .jgtz _ => .jgtz
  | .halt => .halt

















theorem fetch_some_pc_lt {p : Program} {pc : ℕ} {i : Instr}
    (h : p[pc]? = some i) : pc < p.length := by
  by_contra hn
  rw [List.getElem?_eq_none (by omega)] at h
  contradiction



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_InterpreterState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

/-! Canonical stacks at instruction boundaries.  Work stacks are empty there;
individual verified macros may use them between dispatcher labels. -/

inductive CoreStack
  | accumulator | memory | input | output
  | work0 | work1 | work2 | work3 | work4 | work5 | work6 | work7
  deriving DecidableEq, Fintype, Inhabited

def encodeAccumulator (w a : ℕ) : List SparseSymbol :=
  (fixedBits w a).map SparseSymbol.bit

def encodeInputStack (w : ℕ) (input : List ℕ) : List SparseSymbol :=
  encodeWordList w input ++ [.inputEnd]

/-- The output is reversed so appending one RAM word becomes pushing one
reversed encoded word at the top of the stack. -/
def encodeOutputStack (w : ℕ) (output : List ℕ) : List SparseSymbol :=
  (encodeWordList w output).reverse ++ [.outputEnd]

def encodeMemoryStack (w : ℕ) (memory : SparseMemory) : List SparseSymbol :=
  encodeSparseMemory w memory ++ [.memoryEnd]

def coreStacks (w : ℕ) (s : SparseState) : CoreStack → List SparseSymbol
  | .accumulator => encodeAccumulator w s.acc
  | .memory => encodeMemoryStack w s.mem
  | .input => encodeInputStack w s.inp
  | .output => encodeOutputStack w s.out
  | .work0 | .work1 | .work2 | .work3 | .work4 | .work5 | .work6 | .work7 => []





















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ControlDispatcherMachine
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

structure DispatchControl where
  held : Option SparseSymbol
  anyTrue : Bool
  deriving DecidableEq, Fintype, Inhabited

def DispatchControl.observe (s : DispatchControl) (a : Option SparseSymbol) :
    DispatchControl :=
  { s with
    held := a,
    anyTrue := s.anyTrue || match a with | some (.bit true) => true | _ => false }

def DispatchControl.clearHeld (s : DispatchControl) : DispatchControl :=
  { s with held := none }

inductive ControlDispatchLabel (p : Program)
  | fetch (pc : BoundedPC p)
  | scanAccumulator (pc target : BoundedPC p) (jumpOnZero : Bool)
  | restoreAccumulator (pc target : BoundedPC p) (jumpOnZero : Bool)
  | data (pc : BoundedPC p) (kind : InstrClass)
  | stopped
  deriving DecidableEq, Fintype, Inhabited



def controlDispatchMachine (p : Program) : Turing.FinTM2 where
  K := CoreStack
  k₀ := .input
  k₁ := .output
  Γ _ := SparseSymbol
  Λ := ControlDispatchLabel p
  main := .fetch (boundPC p 0)
  σ := DispatchControl
  initialState := default
  m
    | .fetch pc =>
        match pc.fetch with
        | none | some .halt => .goto fun _ => .stopped
        | some (.jump target) => .goto fun _ => .fetch (jumpPC p target)
        | some (.jzero target) =>
            .load (fun _ => default) <|
              .goto fun _ => .scanAccumulator pc (jumpPC p target) true
        | some (.jgtz target) =>
            .load (fun _ => default) <|
              .goto fun _ => .scanAccumulator pc (jumpPC p target) false
        | some i => .goto fun _ => .data pc (instrClass i)
    | .scanAccumulator pc target jumpOnZero =>
        .pop .accumulator DispatchControl.observe <|
          .branch (fun s => s.held.isNone)
            (.load DispatchControl.clearHeld <|
              .goto fun _ => .restoreAccumulator pc target jumpOnZero)
            (.push .work0 (fun s => s.held.getD default) <|
              .load DispatchControl.clearHeld <|
                .goto fun _ => .scanAccumulator pc target jumpOnZero)
    | .restoreAccumulator pc target jumpOnZero =>
        .pop .work0 (fun s a => { s with held := a }) <|
          .branch (fun s => s.held.isNone)
            (.load DispatchControl.clearHeld <|
              .branch (fun s => s.anyTrue == !jumpOnZero)
                (.load (fun _ => default) <| .goto fun _ => .fetch target)
                (.load (fun _ => default) <| .goto fun _ => .fetch (nextPC p pc)))
            (.push .accumulator (fun s => s.held.getD default) <|
              .load DispatchControl.clearHeld <|
                .goto fun _ => .restoreAccumulator pc target jumpOnZero)
    | .data _ _ => .halt
    | .stopped => .halt















































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MacroSpliceInstances
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! Ready-to-use spliced forms of the two macros used by operand evaluation. -/



def lookupScanProgram : LookupScanLabel →
    TM2.Stmt (fun _ : LookupScanStack => SparseSymbol) LookupScanLabel
      LookupCellControl :=
  lookupScanMachine.m











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_StackRenaming
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! A finite local macro may reuse selected stacks of a larger interpreter.
The partial inverse makes this renaming executable and gives the exact update
law needed by the step simulation proof. -/

structure StackRenaming (K K' : Type) where
  encode : K → K'
  decode : K' → Option K
  decode_encode : ∀ k, decode (encode k) = some k
  encode_decode : ∀ {k' k}, decode k' = some k → encode k = k'

































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_InterpreterStackRenamings
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! Concrete, collision-free placements of operand-evaluation macro stacks
inside the global RAM-interpreter stack set. -/

def literalWordCoreEncode : LiteralWordStack → CoreStack
  | .query => .accumulator
  | .backup => .work7
  | .result => .work0

def literalWordCoreDecode : CoreStack → Option LiteralWordStack
  | .accumulator => some .query
  | .work7 => some .backup
  | .work0 => some .result
  | _ => none

def literalWordCoreRenaming : StackRenaming LiteralWordStack CoreStack where
  encode := literalWordCoreEncode
  decode := literalWordCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [literalWordCoreDecode,
      literalWordCoreEncode] at h ⊢

def literalQueryCoreEncode : LiteralWordStack → CoreStack
  | .query => .accumulator
  | .backup => .work7
  | .result => .work1

def literalQueryCoreDecode : CoreStack → Option LiteralWordStack
  | .accumulator => some .query
  | .work7 => some .backup
  | .work1 => some .result
  | _ => none

def literalQueryCoreRenaming : StackRenaming LiteralWordStack CoreStack where
  encode := literalQueryCoreEncode
  decode := literalQueryCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [literalQueryCoreDecode,
      literalQueryCoreEncode] at h ⊢

def zeroWordCoreEncode : ZeroWordStack → CoreStack
  | .query => .accumulator
  | .backup => .work7
  | .result => .work0

def zeroWordCoreDecode : CoreStack → Option ZeroWordStack
  | .accumulator => some .query
  | .work7 => some .backup
  | .work0 => some .result
  | _ => none

def zeroWordCoreRenaming : StackRenaming ZeroWordStack CoreStack where
  encode := zeroWordCoreEncode
  decode := zeroWordCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [zeroWordCoreDecode,
      zeroWordCoreEncode] at h ⊢

def lookupCoreEncode : LookupScanStack → CoreStack
  | .source => .memory
  | .value => .work0
  | .query => .work1
  | .address => .work2
  | .cellBackup => .work3
  | .addressBackup => .work4
  | .queryBackup => .work5
  | .processed => .work6
  | .trash => .work7

def lookupCoreDecode : CoreStack → Option LookupScanStack
  | .memory => some .source
  | .work0 => some .value
  | .work1 => some .query
  | .work2 => some .address
  | .work3 => some .cellBackup
  | .work4 => some .addressBackup
  | .work5 => some .queryBackup
  | .work6 => some .processed
  | .work7 => some .trash
  | _ => none

def lookupCoreRenaming : StackRenaming LookupScanStack CoreStack where
  encode := lookupCoreEncode
  decode := lookupCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [lookupCoreDecode, lookupCoreEncode] at h ⊢























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ArithmeticStackRenamings
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

/-! Concrete placements of the arithmetic macro stacks in `CoreStack`. -/

def binaryCoreEncode : AddStack → CoreStack
  | .left => .accumulator
  | .right => .work1
  | .result => .work0

def binaryCoreDecode : CoreStack → Option AddStack
  | .accumulator => some .left
  | .work1 => some .right
  | .work0 => some .result
  | _ => none

def binaryCoreRenaming : StackRenaming AddStack CoreStack where
  encode := binaryCoreEncode
  decode := binaryCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [binaryCoreDecode, binaryCoreEncode] at h ⊢







def mulCoreEncode : MulStack → CoreStack
  | .multiplier => .work1
  | .multiplicand => .accumulator
  | .accumulator => .work0
  | .multiplicandBackup => .work2
  | .sumReverse => .work3
  | .shiftTemp => .work4

def mulCoreDecode : CoreStack → Option MulStack
  | .work1 => some .multiplier
  | .accumulator => some .multiplicand
  | .work0 => some .accumulator
  | .work2 => some .multiplicandBackup
  | .work3 => some .sumReverse
  | .work4 => some .shiftTemp
  | _ => none

def mulCoreRenaming : StackRenaming MulStack CoreStack where
  encode := mulCoreEncode
  decode := mulCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [mulCoreDecode, mulCoreEncode] at h ⊢















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_BinaryCoreMacros
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseAddCoreProgram : AddLabel →
    TM2.Stmt (fun _ : AddStack => SparseSymbol) AddLabel AddControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (addIteration .left .right .result .loop .done)
  | .done => .halt







def sparseZipCoreProgram (f : Bool → Bool → Bool) : AddLabel →
    TM2.Stmt (fun _ : AddStack => SparseSymbol) AddLabel ZipControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (zipIteration f .left .right .result .loop .done)
  | .done => .halt







def sparseSubCoreProgram : AddLabel →
    TM2.Stmt (fun _ : AddStack => SparseSymbol) AddLabel SubControl
  | .loop => mapAlphabetStmt sparseBitEncode sparseBitDecode
      (subIteration .left .right .result .loop .done)
  | .done => .halt













end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MultiplyCoreMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def mulBaseProgram : MulLabel →
    TM2.Stmt (fun _ : MulStack => Bool) MulLabel MulControl
  | .outer =>
      .pop .multiplier (fun s a => { s with selected := a }) <|
        .branch (fun s => s.selected.isNone)
          (.goto fun _ => .done) (.goto fun _ => .select)
  | .select => .branch (fun s => s.selected.getD false)
      (.load (fun s => { s with carry := false, left := none, right := none }) <|
        .goto fun _ => .add)
      (.goto fun _ => .shiftFirst)
  | .add =>
      .pop .multiplicand (fun s a => { s with left := a }) <|
        .branch (fun s => s.left.isNone)
          (.goto fun _ => .restoreMultiplicand)
          (.pop .accumulator (fun s b => { s with right := b }) <|
            .push .multiplicandBackup (fun s => s.left.getD false) <|
              .push .sumReverse MulControl.sumBit <|
                .load MulControl.addAdvance <| .goto fun _ => .add)
  | .restoreMultiplicand => mulMoveIteration .multiplicandBackup .multiplicand
      .restoreMultiplicand .restoreSum
  | .restoreSum => mulMoveIteration .sumReverse .accumulator
      .restoreSum .shiftFirst
  | .shiftFirst => mulMoveIteration .multiplicand .shiftTemp
      .shiftFirst .shiftDiscard
  | .shiftDiscard =>
      .pop .shiftTemp (fun s _ => MulControl.clearHeld s) <|
        .goto fun _ => .shiftSecond
  | .shiftSecond => mulMoveIteration .shiftTemp .multiplicand
      .shiftSecond .shiftPrepend
  | .shiftPrepend => .push .multiplicand (fun _ => false) <|
      .load (fun _ => default) <| .goto fun _ => .outer
  | .done => .halt

def sparseMulCoreProgram : MulLabel →
    TM2.Stmt (fun _ : MulStack => SparseSymbol) MulLabel MulControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode mulBaseProgram











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_DivideCoreMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def divBaseProgram : DivLabel →
    TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl :=
  fun label => divMachine.m label

def sparseDivCoreProgram : DivLabel →
    TM2.Stmt (fun _ : DivStack => SparseSymbol) DivLabel DivControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode divBaseProgram













end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MemoryWriteCoreMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def prependCoreEncode : PrependCellStack → CoreStack
  | .address => .work0
  | .value => .work1
  | .memory => .memory

def prependCoreDecode : CoreStack → Option PrependCellStack
  | .work0 => some .address
  | .work1 => some .value
  | .memory => some .memory
  | _ => none

def prependCoreRenaming : StackRenaming PrependCellStack CoreStack where
  encode := prependCoreEncode
  decode := prependCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;> simp [prependCoreDecode, prependCoreEncode] at h ⊢

def prependCoreProgram : PrependCellLabel →
    TM2.Stmt (fun _ : PrependCellStack => SparseSymbol)
      PrependCellLabel PrependCellControl :=
  fun label => prependCellMachine.m label







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CoreMoveMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def symbolMoveCoreEncode (source target : CoreStack) : SymbolMoveStack → CoreStack
  | .source => source
  | .target => target

def symbolMoveCoreDecode (source target : CoreStack) : CoreStack → Option SymbolMoveStack :=
  fun k => if k = source then some .source
    else if k = target then some .target else none

def symbolMoveCoreRenaming (source target : CoreStack) (hne : source ≠ target) :
    StackRenaming SymbolMoveStack CoreStack where
  encode := symbolMoveCoreEncode source target
  decode := symbolMoveCoreDecode source target
  decode_encode := by
    intro k
    cases k
    · simp [symbolMoveCoreDecode, symbolMoveCoreEncode]
    · simp [symbolMoveCoreDecode, symbolMoveCoreEncode, hne, Ne.symm hne]
  encode_decode := by
    intro k' k h
    cases k with
    | source =>
        have hs : k' = source := by
          by_cases hs : k' = source
          · exact hs
          · simp [symbolMoveCoreDecode, hs] at h
        exact hs.symm
    | target =>
        have ht : k' = target := by
          by_cases hs : k' = source
          · subst k'
            simp [symbolMoveCoreDecode, hne] at h
          · by_cases ht : k' = target
            · exact ht
            · simp [symbolMoveCoreDecode, hs, ht] at h
        exact ht.symm

def symbolMoveCoreProgram : SymbolMoveLabel →
    TM2.Stmt (fun _ : SymbolMoveStack => SparseSymbol)
      SymbolMoveLabel SymbolMoveControl :=
  fun label => symbolMoveMachine.m label











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_StateLensEmbedding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure StateLens (σ Ω : Type) where
  get : Ω → σ
  put : Ω → σ → Ω
  get_put : ∀ outer inner, get (put outer inner) = inner
  put_get : ∀ outer, put outer (get outer) = outer
  put_put : ∀ outer first second, put (put outer first) second = put outer second





def StateLens.comp {σ τ Ω : Type} (inner : StateLens σ τ)
    (outer : StateLens τ Ω) : StateLens σ Ω where
  get := fun state => inner.get (outer.get state)
  put := fun state value => outer.put state (inner.put (outer.get state) value)
  get_put := by
    intro state value
    rw [outer.get_put, inner.get_put]
  put_get := by
    intro state
    rw [inner.put_get, outer.put_get]
  put_put := by
    intro state first second
    rw [outer.put_put, outer.get_put, inner.put_put]

def lensRenameStmt {α K K' Λ Λx σ Ω : Type} [DecidableEq K]
    [DecidableEq K'] (stackMap : StackRenaming K K') (state : StateLens σ Ω) :
    TM2.Stmt (fun _ : K => α) Λ σ →
      TM2.Stmt (fun _ : K' => α) (Sum Λ Λx) Ω
  | .push k f q => .push (stackMap.encode k) (fun s => f (state.get s))
      (lensRenameStmt stackMap state q)
  | .peek k f q => .peek (stackMap.encode k)
      (fun s a => state.put s (f (state.get s) a))
      (lensRenameStmt stackMap state q)
  | .pop k f q => .pop (stackMap.encode k)
      (fun s a => state.put s (f (state.get s) a))
      (lensRenameStmt stackMap state q)
  | .load f q => .load (fun s => state.put s (f (state.get s)))
      (lensRenameStmt stackMap state q)
  | .branch f q₁ q₂ => .branch (fun s => f (state.get s))
      (lensRenameStmt stackMap state q₁) (lensRenameStmt stackMap state q₂)
  | .goto f => .goto (fun s => .inl (f (state.get s)))
  | .halt => .halt























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_InterpreterMacroState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

set_option maxRecDepth 10000
set_option maxSynthPendingDepth 10000

/-! The monolithic interpreter carries every fixed-size macro controller.
Each phase accesses only its field through a lawful lens. -/

structure InterpreterMacroStateA where
  dispatch : DispatchControl := default
  lookup : LookupCellControl := default
  add : AddControl := default
  zip : ZipControl := default
  deriving DecidableEq, Fintype, Inhabited

structure InterpreterMacroStateB where
  sub : SubControl := default
  mul : MulControl := default
  div : DivControl := default
  move : SymbolMoveControl := default
  deriving DecidableEq, Fintype, Inhabited

structure InterpreterMacroStateC where
  prepend : PrependCellControl := default
  shift : MoveControl := default
  compare : CompareControl := default
  zero : ZeroWordControl := default
  transfer : WordTransferControl := default
  deriving DecidableEq, Fintype, Inhabited

structure InterpreterMacroState where
  a : InterpreterMacroStateA := default
  b : InterpreterMacroStateB := default
  c : InterpreterMacroStateC := default
  deriving DecidableEq, Fintype, Inhabited



def InterpreterMacroState.lookupLens :
    StateLens LookupCellControl InterpreterMacroState where
  get := fun s => s.a.lookup
  put := fun s v => { s with a := { s.a with lookup := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.addLens : StateLens AddControl InterpreterMacroState where
  get := fun s => s.a.add
  put := fun s v => { s with a := { s.a with add := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.zipLens : StateLens ZipControl InterpreterMacroState where
  get := fun s => s.a.zip
  put := fun s v => { s with a := { s.a with zip := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.subLens : StateLens SubControl InterpreterMacroState where
  get := fun s => s.b.sub
  put := fun s v => { s with b := { s.b with sub := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.mulLens : StateLens MulControl InterpreterMacroState where
  get := fun s => s.b.mul
  put := fun s v => { s with b := { s.b with mul := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.divLens : StateLens DivControl InterpreterMacroState where
  get := fun s => s.b.div
  put := fun s v => { s with b := { s.b with div := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.moveLens :
    StateLens SymbolMoveControl InterpreterMacroState where
  get := fun s => s.b.move
  put := fun s v => { s with b := { s.b with move := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.prependLens :
    StateLens PrependCellControl InterpreterMacroState where
  get := fun s => s.c.prepend
  put := fun s v => { s with c := { s.c with prepend := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def InterpreterMacroState.shiftLens : StateLens MoveControl InterpreterMacroState where
  get := fun s => s.c.shift
  put := fun s v => { s with c := { s.c with shift := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl



def InterpreterMacroState.zeroLens :
    StateLens ZeroWordControl InterpreterMacroState where
  get := fun s => s.c.zero
  put := fun s v => { s with c := { s.c with zero := v } }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_LabelEmbedding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def mapLabelStmt {K Λ Λ' σ : Type} {α : K → Type} [DecidableEq K]
    (encode : Λ → Λ') :
    TM2.Stmt α Λ σ → TM2.Stmt α Λ' σ
  | .push k f q => .push k f (mapLabelStmt encode q)
  | .peek k f q => .peek k f (mapLabelStmt encode q)
  | .pop k f q => .pop k f (mapLabelStmt encode q)
  | .load f q => .load f (mapLabelStmt encode q)
  | .branch f q₁ q₂ => .branch f (mapLabelStmt encode q₁) (mapLabelStmt encode q₂)
  | .goto f => .goto fun s => encode (f s)
  | .halt => .halt









def liftRightProgram {α K Λx Λ σ : Type} [DecidableEq K]
    (left : Λx → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ)
    (right : Λ → TM2.Stmt (fun _ : K => α) Λ σ) :
    Sum Λx Λ → TM2.Stmt (fun _ : K => α) (Sum Λx Λ) σ
  | .inl l => left l
  | .inr l => mapLabelStmt Sum.inr (right l)











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_PhaseComposition
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def lensPhaseLeft {α K K' Λ R σ Ω : Type} [DecidableEq K]
    [DecidableEq K'] [DecidableEq Λ] (stackMap : StackRenaming K K')
    (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ) (done : Λ)
    (entry : R) :
    Λ → TM2.Stmt (fun _ : K' => α) (Sum Λ R) Ω :=
  fun label => if label = done then .goto fun _ => .inr entry
    else lensRenameStmt stackMap lens (program label)







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MultiExitPhase
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! A phase may have several halting exits.  This is needed for lookup:
`found` and `missing` are both genuine runtime outcomes of one finite
program. -/





def lensMultiPhaseLeft {α K K' Λ R σ Ω : Type}
    [DecidableEq K] [DecidableEq K']
    (stackMap : StackRenaming K K') (lens : StateLens σ Ω)
    (program : Λ → TM2.Stmt (fun _ : K => α) Λ σ)
    (exit : Λ → Option R) (onExit : Λ → Ω → Ω) :
    Λ → TM2.Stmt (fun _ : K' => α) (Sum Λ R) Ω :=
  fun label => match exit label with
    | some next => .load (onExit label) <| .goto fun _ => .inr next
    | none => lensRenameStmt stackMap lens (program label)









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_BoundedLiteralWordMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

structure BoundedLiteralControl (N : ℕ) where
  held : Option SparseSymbol
  remaining : Fin (N + 1)
  deriving DecidableEq, Fintype



def BoundedLiteralControl.initial {N n : ℕ} (hn : n ≤ N) :
    BoundedLiteralControl N :=
  ⟨none, ⟨n, by omega⟩⟩

def BoundedLiteralControl.advance {N : ℕ}
    (s : BoundedLiteralControl N) : BoundedLiteralControl N :=
  ⟨none, ⟨s.remaining.val.div2,
    lt_of_le_of_lt (Nat.div_le_self _ _) s.remaining.isLt⟩⟩

def boundedLiteralWordProgram (N : ℕ) : LiteralWordLabel →
    TM2.Stmt (fun _ : LiteralWordStack => SparseSymbol)
      LiteralWordLabel (BoundedLiteralControl N)
  | .emit =>
      .pop .query (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .restore)
          (.push .backup (fun s => s.held.getD (.bit false)) <|
            .push .result (fun s => .bit s.remaining.val.bodd) <|
              .load BoundedLiteralControl.advance <| .goto fun _ => .emit)
  | .restore =>
      .pop .backup (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.load (fun s => { s with held := none }) <| .goto fun _ => .done)
          (.push .query (fun s => s.held.getD (.bit false)) <|
            .load (fun s => { s with held := none }) <| .goto fun _ => .restore)
  | .done => .halt

















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_WordCountdownMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CountdownStack | count | temp
  deriving DecidableEq, Fintype, Inhabited

inductive CountdownLabel | scan | restore | zero | positive
  deriving DecidableEq, Fintype, Inhabited

structure CountdownControl where
  held : Option Bool := none
  borrow : Bool := true
  positiveSeen : Bool := false
  deriving DecidableEq, Fintype

instance : Inhabited CountdownControl :=
  ⟨{ held := none, borrow := true, positiveSeen := false }⟩

def countdownOutput (s : CountdownControl) : Bool :=
  (fullSubtractor (s.held.getD false) false s.borrow).1

def countdownAdvance (s : CountdownControl) : CountdownControl :=
  let bit := s.held.getD false
  { held := none
    borrow := (fullSubtractor bit false s.borrow).2
    positiveSeen := s.positiveSeen || bit }

def countdownClearHeld (s : CountdownControl) : CountdownControl :=
  { s with held := none }

def countdownMachine : Turing.FinTM2 where
  K := CountdownStack
  k₀ := .count
  k₁ := .temp
  Γ _ := Bool
  Λ := CountdownLabel
  main := .scan
  σ := CountdownControl
  initialState := default
  m
    | .scan =>
        .pop .count (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.branch (fun s => s.positiveSeen)
            (.goto fun _ => .restore) (.goto fun _ => .zero))
          (.push .temp countdownOutput <|
            .load countdownAdvance <| .goto fun _ => .scan)
    | .restore =>
        .pop .temp (fun s a => { s with held := a }) <|
        .branch (fun s => s.held.isNone)
          (.goto fun _ => .positive)
          (.push .count (fun s => s.held.getD false) <|
            .load countdownClearHeld <| .goto fun _ => .restore)
    | .zero | .positive => .halt

































end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullInterpreterState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

structure FullInterpreterState (N : ℕ) where
  macros : InterpreterMacroState := default
  /-- Dispatcher control is kept outside the resettable arithmetic macro
  bundle, so instruction-local cleanup cannot overwrite the global control
  invariant. -/
  dispatch : DispatchControl := default
  literal : BoundedLiteralControl N := ⟨none, 0⟩
  lookupFound : Bool := false
  subtractForceZero : Bool := false
  countdown : CountdownControl := default
  deriving DecidableEq, Fintype, Inhabited

def FullInterpreterState.macroLens {N : ℕ} :
    StateLens InterpreterMacroState (FullInterpreterState N) where
  get := FullInterpreterState.macros
  put := fun s v => { s with macros := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.literalLens {N : ℕ} :
    StateLens (BoundedLiteralControl N) (FullInterpreterState N) where
  get := FullInterpreterState.literal
  put := fun s v => { s with literal := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.countdownLens {N : ℕ} :
    StateLens CountdownControl (FullInterpreterState N) where
  get := FullInterpreterState.countdown
  put := fun s v => { s with countdown := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.lookupLens {N : ℕ} :
    StateLens LookupCellControl (FullInterpreterState N) :=
  InterpreterMacroState.lookupLens.comp FullInterpreterState.macroLens

def FullInterpreterState.dispatchLens {N : ℕ} :
    StateLens DispatchControl (FullInterpreterState N) where
  get := FullInterpreterState.dispatch
  put := fun s v => { s with dispatch := v }
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl

def FullInterpreterState.zeroLens {N : ℕ} :
    StateLens ZeroWordControl (FullInterpreterState N) :=
  InterpreterMacroState.zeroLens.comp FullInterpreterState.macroLens

def FullInterpreterState.moveLens {N : ℕ} :
    StateLens SymbolMoveControl (FullInterpreterState N) :=
  InterpreterMacroState.moveLens.comp FullInterpreterState.macroLens

def FullInterpreterState.prependLens {N : ℕ} :
    StateLens PrependCellControl (FullInterpreterState N) :=
  InterpreterMacroState.prependLens.comp FullInterpreterState.macroLens

def FullInterpreterState.shiftLens {N : ℕ} :
    StateLens MoveControl (FullInterpreterState N) :=
  InterpreterMacroState.shiftLens.comp FullInterpreterState.macroLens



def FullInterpreterState.subLens {N : ℕ} :
    StateLens SubControl (FullInterpreterState N) :=
  InterpreterMacroState.subLens.comp FullInterpreterState.macroLens

def FullInterpreterState.divLens {N : ℕ} :
    StateLens DivControl (FullInterpreterState N) :=
  InterpreterMacroState.divLens.comp FullInterpreterState.macroLens

def coreIdentityRenaming : StackRenaming CoreStack CoreStack where
  encode := id
  decode := some
  decode_encode := by intro k; rfl
  encode_decode := by
    intro k' k h
    simpa using h.symm



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_DiscardStackMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! A small but important cleanup macro.  Unlike `SymbolMoveMacro`, this
macro consumes a work stack without leaving its contents on another tape.
This gives the compound interpreter honest clean phase boundaries. -/

inductive DiscardStack
  | data
  deriving DecidableEq, Fintype, Inhabited

inductive DiscardLabel
  | loop | done
  deriving DecidableEq, Fintype, Inhabited

def discardProgram : DiscardLabel →
    TM2.Stmt (fun _ : DiscardStack => SparseSymbol)
      DiscardLabel SymbolMoveControl
  | .loop =>
      .pop .data (fun _ a => ⟨a⟩) <|
        .branch (fun s => s.held.isNone)
          (.load (fun _ => default) <| .goto fun _ => .done)
          (.load (fun _ => default) <| .goto fun _ => .loop)
  | .done => .halt























def discardCoreRenaming (target : CoreStack) :
    StackRenaming DiscardStack CoreStack where
  encode := fun _ => target
  decode := fun k => if k = target then some .data else none
  decode_encode := by intro k; cases k; simp
  encode_decode := by
    intro k' k h
    cases k
    by_cases hk : k' = target
    · exact hk.symm
    · simp [hk] at h



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_UnifiedLookupPhase
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev UnifiedLookupTail (R : Type) := Sum DiscardLabel R
abbrev UnifiedLookupLabel (R : Type) :=
  Sum LookupScanLabel (UnifiedLookupTail R)

def lookupExit {R : Type} : LookupScanLabel → Option (UnifiedLookupTail R)
  | .found | .missing => some (Sum.inl DiscardLabel.loop)
  | _ => none

def lookupRecordOutcome {N : ℕ} (label : LookupScanLabel)
    (state : FullInterpreterState N) : FullInterpreterState N :=
  { state with lookupFound := decide (label = .found) }



def unifiedLookupProgram {N : ℕ} {R : Type}
    (right : UnifiedLookupTail R →
      TM2.Stmt (fun _ : CoreStack => SparseSymbol)
        (UnifiedLookupTail R) (FullInterpreterState N)) :
    UnifiedLookupLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedLookupLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensMultiPhaseLeft lookupCoreRenaming FullInterpreterState.lookupLens
      lookupScanProgram lookupExit lookupRecordOutcome)
    right









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_UnifiedCleanLookup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive LookupDecisionLabel
  | decide
  deriving DecidableEq, Fintype, Inhabited

abbrev UnifiedCleanFinish (R : Type) := Sum ZeroWordLabel R
abbrev UnifiedCleanAfter (R : Type) :=
  Sum LookupDecisionLabel (UnifiedCleanFinish R)
abbrev UnifiedCleanTail (R : Type) :=
  Sum DiscardLabel (UnifiedCleanAfter R)
abbrev UnifiedCleanLookupLabel (R : Type) :=
  Sum LookupScanLabel (UnifiedCleanTail R)

def unifiedCleanFinishProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanFinish R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanFinish R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done returnLabel)
    right

def lookupDecisionProgram {N : ℕ} {R : Type} (returnLabel : R) :
    LookupDecisionLabel → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanAfter R) (FullInterpreterState N)
  | .decide =>
      .branch FullInterpreterState.lookupFound
        (.goto fun _ => .inr (.inr returnLabel))
        (.goto fun _ => .inr (.inl ZeroWordLabel.fill))

def unifiedCleanAfterProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanAfter R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanAfter R) (FullInterpreterState N) :=
  liftRightProgram (lookupDecisionProgram returnLabel)
    (unifiedCleanFinishProgram returnLabel right)

def unifiedCleanTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanTail R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl LookupDecisionLabel.decide))
    (unifiedCleanAfterProgram returnLabel right)

def unifiedCleanLookupProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    UnifiedCleanLookupLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (UnifiedCleanLookupLabel R) (FullInterpreterState N) :=
  unifiedLookupProgram (unifiedCleanTailProgram returnLabel right)



















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_QueryTransferPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! Preserve a reversed word while changing its work tape.  One stack move
reverses, so indirect addressing uses two moves via `work2`. -/



abbrev QueryTransferTail (R : Type) := Sum SymbolMoveLabel R
abbrev QueryTransferLabel (R : Type) :=
  Sum SymbolMoveLabel (QueryTransferTail R)

def queryTransferTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    QueryTransferTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (QueryTransferTail R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def queryTransferProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    QueryTransferLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (QueryTransferLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (queryTransferTailProgram returnLabel right)





end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_DirectOperandPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive LookupInitLabel
  | init
  deriving DecidableEq, Fintype, Inhabited

abbrev DirectOperandTail (R : Type) :=
  Sum LookupInitLabel (UnifiedCleanLookupLabel R)
abbrev DirectOperandLabel (R : Type) :=
  Sum LiteralWordLabel (DirectOperandTail R)

def lookupInitialControl : LookupCellControl :=
  ⟨none, true, none, none⟩

def lookupInitProgram {N : ℕ} {R : Type} :
    LookupInitLabel → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N)
  | .init =>
      .load (fun state =>
        FullInterpreterState.lookupLens.put state lookupInitialControl) <|
      .goto fun _ => .inr (Sum.inl LookupScanLabel.scan)

def directOperandTailProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DirectOperandTail R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (DirectOperandTail R) (FullInterpreterState N) :=
  liftRightProgram lookupInitProgram
    (unifiedCleanLookupProgram returnLabel right)

def directOperandProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DirectOperandLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (DirectOperandLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft literalQueryCoreRenaming
      FullInterpreterState.literalLens (boundedLiteralWordProgram N)
      .done (Sum.inl LookupInitLabel.init))
    (directOperandTailProgram returnLabel right)























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_LiteralOperandPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

/-! The literal branch of operand evaluation, with exactly the same boundary
contract as the memory branches: the accumulator and encoded memory are
preserved, all scratch stacks are empty, and the low word of the operand is
returned (least-significant end first) on `work0`.  The quotient retained in
the finite control records whether a program literal exceeded the word. -/

def literalOperandProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    Sum LiteralWordLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (Sum LiteralWordLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft literalWordCoreRenaming FullInterpreterState.literalLens
      (boundedLiteralWordProgram N) .done returnLabel)
    right









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_AddPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2



abbrev AddFinishLabel (R : Type) := Sum SymbolMoveLabel R
abbrev AddTailLabel (R : Type) := Sum AddLabel (AddFinishLabel R)
abbrev AddPipelineLabel (R : Type) := Sum SymbolMoveLabel (AddTailLabel R)

def addResultMoveProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AddFinishLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddFinishLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def addTailProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AddTailLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddTailLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.addLens
      sparseAddCoreProgram .done (Sum.inl .loop))
    (addResultMoveProgram returnLabel right)

def addPipelineProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AddPipelineLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddPipelineLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done (Sum.inl .loop))
    (addTailProgram returnLabel right)











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullAddMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev FullAddLabel := AddPipelineLabel Unit

def closedAddPipelineProgram : FullAddLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) FullAddLabel
      InterpreterMacroState :=
  addPipelineProgram () (fun _ => .halt)

def closedAddDone : FullAddLabel :=
  Sum.inr (Sum.inr (Sum.inr ()))



abbrev FullAddPhaseLabel (R : Type) := Sum FullAddLabel R

def fullAddPhaseProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullAddPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullAddPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedAddPipelineProgram closedAddDone returnLabel)
    right















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_IndirectOperandPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev IndirectTransferLabel (R : Type) :=
  QueryTransferLabel (DirectOperandTail R)
abbrev IndirectOperandLabel (R : Type) :=
  DirectOperandLabel (IndirectTransferLabel R)

def indirectTransferProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    IndirectTransferLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (IndirectTransferLabel R) (FullInterpreterState N) :=
  queryTransferProgram (Sum.inl LookupInitLabel.init)
    (directOperandTailProgram returnLabel right)

def indirectOperandProgram {N : ℕ} {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    IndirectOperandLabel R → TM2.Stmt
      (fun _ : CoreStack => SparseSymbol)
      (IndirectOperandLabel R) (FullInterpreterState N) :=
  directOperandProgram (Sum.inl SymbolMoveLabel.loop)
    (indirectTransferProgram returnLabel right)

























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_OperandEvaluator
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def operandArgument : Op -> Nat
  | .lit n | .mem n | .ind n => n

def OperandEvalLabel (o : Op) (R : Type) : Type :=
  match o with
  | .lit _ => Sum LiteralWordLabel R
  | .mem _ => DirectOperandLabel R
  | .ind _ => IndirectOperandLabel R



instance (o : Op) (R : Type) [Fintype R] : Fintype (OperandEvalLabel o R) := by
  cases o <;> dsimp [OperandEvalLabel] <;> infer_instance



def operandEvalProgram {N : Nat} {R : Type} (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    OperandEvalLabel o R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (OperandEvalLabel o R) (FullInterpreterState N) :=
  match o with
  | .lit _ => literalOperandProgram returnLabel right
  | .mem _ => directOperandProgram returnLabel right
  | .ind _ => indirectOperandProgram returnLabel right





def operandEvalBound (w : Nat) (m : SparseMemory) : Nat :=
  2 * (m.length * (12 * w + 22)) + 28 * w + 61







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_AccumulatorInstallPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev AccInstallTailLabel (R : Type) := Sum SymbolMoveLabel R
abbrev AccInstallLabel (R : Type) := Sum SymbolMoveLabel (AccInstallTailLabel R)

def accInstallTailProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AccInstallTailLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AccInstallTailLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def accInstallProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    AccInstallLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AccInstallLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (accInstallTailProgram returnLabel right)













end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullLoadMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev ClosedAccInstallLabel := AccInstallLabel Unit

def closedAccInstallProgram : ClosedAccInstallLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ClosedAccInstallLabel
      InterpreterMacroState :=
  accInstallProgram () (fun _ => .halt)

def closedAccInstallDone : ClosedAccInstallLabel :=
  Sum.inr (Sum.inr ())



abbrev FullLoadFinishLabel (R : Type) := Sum DiscardLabel R
abbrev FullLoadLabel (R : Type) :=
  Sum ClosedAccInstallLabel (FullLoadFinishLabel R)

def fullLoadFinishProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullLoadFinishLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullLoadFinishLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work7)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

def fullLoadProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullLoadLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullLoadLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedAccInstallProgram closedAccInstallDone
      (Sum.inl DiscardLabel.loop))
    (fullLoadFinishProgram returnLabel right)









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_LoadInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive LoadResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev LoadInstructionTailLabel (R : Type) :=
  Sum LoadResetLabel (FullLoadLabel R)

abbrev LoadInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (LoadInstructionTailLabel R)

def loadResetProgram {N : Nat} {R : Type} : LoadResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (LoadInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

def loadInstructionTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LoadInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (LoadInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram loadResetProgram (fullLoadProgram returnLabel right)

def loadInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    LoadInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (LoadInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl LoadResetLabel.reset)
    (loadInstructionTailProgram returnLabel right)







def loadInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_AddInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive AddResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev AddInstructionTailLabel (R : Type) :=
  Sum AddResetLabel (FullAddPhaseLabel R)

abbrev AddInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (AddInstructionTailLabel R)

def addResetProgram {N : Nat} {R : Type} : AddResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (AddInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

def addInstructionTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    AddInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (AddInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram addResetProgram (fullAddPhaseProgram returnLabel right)

def addInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    AddInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (AddInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl AddResetLabel.reset)
    (addInstructionTailProgram returnLabel right)



def addInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ZipPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2





abbrev ZipFinishLabel (R : Type) := Sum SymbolMoveLabel R
abbrev ZipTailLabel (R : Type) := Sum AddLabel (ZipFinishLabel R)
abbrev ZipPipelineLabel (R : Type) := Sum SymbolMoveLabel (ZipTailLabel R)

def zipResultMoveProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    ZipFinishLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipFinishLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def zipTailProgram {R : Type} (f : Bool → Bool → Bool) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    ZipTailLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipTailLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming InterpreterMacroState.zipLens
      (sparseZipCoreProgram f) .done (Sum.inl .loop))
    (zipResultMoveProgram returnLabel right)

def zipPipelineProgram {R : Type} (f : Bool → Bool → Bool) (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    ZipPipelineLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipPipelineLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done (Sum.inl .loop))
    (zipTailProgram f returnLabel right)











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullZipMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev ClosedZipLabel := ZipPipelineLabel Unit

def closedZipProgram (f : Bool -> Bool -> Bool) : ClosedZipLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ClosedZipLabel
      InterpreterMacroState :=
  zipPipelineProgram f () (fun _ => .halt)

def closedZipDone : ClosedZipLabel :=
  Sum.inr (Sum.inr (Sum.inr ()))



abbrev FullZipPhaseLabel (R : Type) := Sum ClosedZipLabel R

def fullZipPhaseProgram {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullZipPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullZipPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      (closedZipProgram f) closedZipDone returnLabel)
    right









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ZipInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive ZipResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev ZipInstructionTailLabel (R : Type) :=
  Sum ZipResetLabel (FullZipPhaseLabel R)

abbrev ZipInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (ZipInstructionTailLabel R)

def zipResetProgram {N : Nat} {R : Type} : ZipResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ZipInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

def zipInstructionTailProgram {N : Nat} {R : Type}
    (f : Bool -> Bool -> Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ZipInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ZipInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram zipResetProgram (fullZipPhaseProgram f returnLabel right)

def zipInstructionProgram {N : Nat} {R : Type} (f : Bool -> Bool -> Bool)
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ZipInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ZipInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl ZipResetLabel.reset)
    (zipInstructionTailProgram f returnLabel right)



def zipInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8



inductive BitwiseKind
  | and | or | xor | compl
  deriving DecidableEq, Fintype, Inhabited

def BitwiseKind.boolFn : BitwiseKind -> Bool -> Bool -> Bool
  | .and => fun a b => a && b
  | .or => fun a b => a || b
  | .xor => Bool.xor
  | .compl => fun a _ => !a





def bitwiseInstructionProgram {N : Nat} {R : Type} (kind : BitwiseKind)
    (o : Op) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  zipInstructionProgram kind.boolFn o returnLabel right



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MultiplyPipeline
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev MulInstallLabel (R : Type) := Sum SymbolMoveLabel R
abbrev MulClearLabel (R : Type) := Sum SymbolMoveLabel (MulInstallLabel R)
abbrev MulReverseLabel (R : Type) := Sum SymbolMoveLabel (MulClearLabel R)
abbrev MulArithmeticLabel (R : Type) := Sum MulLabel (MulReverseLabel R)
abbrev MulZeroLabel (R : Type) := Sum ZeroWordLabel (MulArithmeticLabel R)
abbrev MulPipelineLabel (R : Type) := Sum SymbolMoveLabel (MulZeroLabel R)

def mulInstallProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulInstallLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulInstallLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work2 .accumulator (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def mulClearProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulClearLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulClearLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (mulInstallProgram returnLabel right)

def mulReverseProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulReverseLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulReverseLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work2 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (mulClearProgram returnLabel right)

def mulArithmeticProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulArithmeticLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulArithmeticLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft mulCoreRenaming InterpreterMacroState.mulLens
      sparseMulCoreProgram .done (Sum.inl SymbolMoveLabel.loop))
    (mulReverseProgram returnLabel right)

def mulZeroProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulZeroLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulZeroLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft zeroWordCoreRenaming InterpreterMacroState.zeroLens
      zeroWordProgram .done (Sum.inl MulLabel.outer))
    (mulArithmeticProgram returnLabel right)

def mulPipelineProgram {R : Type} (returnLabel : R)
    (right : R → TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      InterpreterMacroState) :
    MulPipelineLabel R → TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulPipelineLabel R) InterpreterMacroState :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      InterpreterMacroState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (mulZeroProgram returnLabel right)

























end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullMultiplyMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev ClosedMulLabel := MulPipelineLabel Unit

noncomputable local instance : DecidableEq ClosedMulLabel := Classical.decEq _

def closedMulProgram : ClosedMulLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ClosedMulLabel
      InterpreterMacroState :=
  mulPipelineProgram () (fun _ => .halt)

def closedMulDone : ClosedMulLabel :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))))



abbrev FullMulFinishLabel (R : Type) := Sum DiscardLabel R
abbrev FullMulLabel (R : Type) := Sum ClosedMulLabel (FullMulFinishLabel R)

def fullMulFinishProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work7)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

noncomputable def fullMulProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming FullInterpreterState.macroLens
      closedMulProgram closedMulDone (Sum.inl DiscardLabel.loop))
    (fullMulFinishProgram returnLabel right)









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_MultiplyInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive MulResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev MulInstructionTailLabel (R : Type) :=
  Sum MulResetLabel (FullMulLabel R)

abbrev MulInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (MulInstructionTailLabel R)

def mulResetProgram {N : Nat} {R : Type} : MulResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (MulInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.macroLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl (Sum.inl SymbolMoveLabel.loop))

noncomputable def mulInstructionTailProgram {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram mulResetProgram (fullMulProgram returnLabel right)

noncomputable def mulInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  operandEvalProgram o (Sum.inl MulResetLabel.reset)
    (mulInstructionTailProgram returnLabel right)



def mulInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + w * (5 * w + 8) + 7 * w + 17



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_WriteInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive WriteResetLabel | reset
  deriving DecidableEq, Fintype, Inhabited
inductive WriteFinishLabel | finish
  deriving DecidableEq, Fintype, Inhabited

abbrev WriteAfterLabel (R : Type) := Sum WriteFinishLabel R
abbrev WriteMove2Label (R : Type) := Sum SymbolMoveLabel (WriteAfterLabel R)
abbrev WriteMove1Label (R : Type) := Sum SymbolMoveLabel (WriteMove2Label R)
abbrev WriteTailLabel (R : Type) := Sum WriteResetLabel (WriteMove1Label R)
abbrev WriteInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (WriteTailLabel R)



def writeFinishProgram {N : Nat} {R : Type} (returnLabel : R) :
    WriteFinishLabel -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (WriteAfterLabel R) (FullInterpreterState N)
  | .finish => .push .output (fun _ => .wordEnd) <|
      .goto fun _ => Sum.inr returnLabel

def writeAfterProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram (writeFinishProgram returnLabel) right

def writeMove2Program {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work1 .output (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl WriteFinishLabel.finish))
    (writeAfterProgram returnLabel right)

def writeMove1Program {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram
    (lensPhaseLeft (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (writeMove2Program returnLabel right)

def writeResetProgram {N : Nat} {R : Type} : WriteResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (WriteTailLabel R) (FullInterpreterState N)
  | .reset => .load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl SymbolMoveLabel.loop)

def writeTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  liftRightProgram writeResetProgram (writeMove1Program returnLabel right)

def writeInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :=
  operandEvalProgram o (Sum.inl WriteResetLabel.reset)
    (writeTailProgram returnLabel right)

















def writeInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 2 * w + 6







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CopyStackMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CopyStack | source | destination | backup
  deriving DecidableEq, Fintype, Inhabited

inductive CopyLabel | scan | restore | done
  deriving DecidableEq, Fintype, Inhabited

def copyProgram : CopyLabel ->
    TM2.Stmt (fun _ : CopyStack => SparseSymbol) CopyLabel SymbolMoveControl
  | .scan =>
      .pop .source (fun s a => { s with held := a }) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .restore)
        (.push .destination (fun s => s.held.getD default) <|
          .push .backup (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .scan)
  | .restore =>
      .pop .backup (fun s a => { s with held := a }) <|
      .branch (fun s => s.held.isNone)
        (.load (fun _ => default) <| .goto fun _ => .done)
        (.push .source (fun s => s.held.getD default) <|
          .load (fun _ => default) <| .goto fun _ => .restore)
  | .done => .halt























def copyCoreRenaming (source destination backup : CoreStack)
    (hsd : source ≠ destination) (hsb : source ≠ backup)
    (hdb : destination ≠ backup) : StackRenaming CopyStack CoreStack where
  encode
    | .source => source
    | .destination => destination
    | .backup => backup
  decode := fun k => if k = source then some .source
    else if k = destination then some .destination
    else if k = backup then some .backup else none
  decode_encode := by
    intro k
    cases k <;> simp [hsd, hsb, hdb, Ne.symm hsd, Ne.symm hsb, Ne.symm hdb]
  encode_decode := by
    intro k' k h
    cases k <;> simp only at h ⊢
    all_goals
      split at h <;> simp_all
    all_goals
      split at h <;> simp_all
    all_goals
      split at h <;> simp_all

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullCopyMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev FullCopyLabel (R : Type) := Sum CopyLabel R

def fullCopyProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullCopyLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullCopyLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (copyCoreRenaming .accumulator .work1 .work7 (by decide) (by decide)
        (by decide))
      FullInterpreterState.moveLens copyProgram .done returnLabel)
    right













end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullPrependMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev FullPrependLabel (R : Type) := Sum PrependCellLabel R

def fullPrependProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullPrependLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullPrependLabel R) (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft prependCoreRenaming FullInterpreterState.prependLens
      prependCoreProgram .done returnLabel)
    right









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullStoreMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive StorePrependResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev StorePrependTailLabel (R : Type) :=
  Sum StorePrependResetLabel (FullPrependLabel R)

abbrev FullStoreLabel (R : Type) :=
  FullCopyLabel (StorePrependTailLabel R)

def storePrependResetProgram {N : Nat} {R : Type} :
    StorePrependResetLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StorePrependTailLabel R)
      (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.prependLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl PrependCellLabel.cellEnd)

def storePrependTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StorePrependTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StorePrependTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram storePrependResetProgram
    (fullPrependProgram returnLabel right)

def fullStoreProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullStoreLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullStoreLabel R)
      (FullInterpreterState N) :=
  fullCopyProgram (Sum.inl StorePrependResetLabel.reset)
    (storePrependTailProgram returnLabel right)











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_StoreInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive StoreResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev StoreInstructionTailLabel (R : Type) :=
  Sum StoreResetLabel (FullStoreLabel R)

abbrev StoreInstructionLabel (address : Nat) (R : Type) :=
  OperandEvalLabel (.lit address) (StoreInstructionTailLabel R)

def storeResetProgram {N : Nat} {R : Type} : StoreResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (StoreInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => Sum.inr (Sum.inl CopyLabel.scan)

def storeInstructionTailProgram {N : Nat} {R : Type}
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StoreInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StoreInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram storeResetProgram (fullStoreProgram returnLabel right)

def storeInstructionProgram {N : Nat} {R : Type} (address : Nat)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StoreInstructionLabel address R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StoreInstructionLabel address R)
      (FullInterpreterState N) :=
  operandEvalProgram (.lit address) (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right)





def storeInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 4 * w + 11



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ReadInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive ReadTransferLabel
  | initializeState | loop
  deriving DecidableEq, Fintype, Inhabited

abbrev ReadTailLabel (R : Type) := Sum ReadTransferLabel (FullPrependLabel R)

abbrev ReadInstructionLabel (address : Nat) (R : Type) :=
  OperandEvalLabel (.lit address) (ReadTailLabel R)

def readTransferLeftProgram {N : Nat} {R : Type} (exhaustedLabel : R) :
    ReadTransferLabel -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N)
  | .initializeState =>
      .load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => Sum.inl .loop
  | .loop =>
      .pop .input (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch
        (fun s => (FullInterpreterState.moveLens.get s).held = some .inputEnd ∨
          (FullInterpreterState.moveLens.get s).held.isNone)
        (.load (fun s => FullInterpreterState.moveLens.put s default) <|
          .goto fun _ => Sum.inr (Sum.inr exhaustedLabel)) <|
      .branch
        (fun s => (FullInterpreterState.moveLens.get s).held = some .wordEnd)
        (.load (fun s => FullInterpreterState.prependLens.put
            (FullInterpreterState.moveLens.put s default) default) <|
          .goto fun _ => Sum.inr (Sum.inl PrependCellLabel.cellEnd))
        (.push .work1
          (fun s => (FullInterpreterState.moveLens.get s).held.getD (.bit false)) <|
          .load (fun s => FullInterpreterState.moveLens.put s default) <|
            .goto fun _ => Sum.inl .loop)

/-- Destructively remove the first encoded input word and place its reversed
bits on `work1`, where the verified prepend-cell macro expects its value. -/
def readTransferProgram {N : Nat} {R : Type} (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ReadTailLabel R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (ReadTailLabel R) (FullInterpreterState N) :=
  liftRightProgram (readTransferLeftProgram exhaustedLabel)
    (fullPrependProgram returnLabel right)

def readInstructionProgram {N : Nat} {R : Type} (address : Nat)
    (exhaustedLabel returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ReadInstructionLabel address R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ReadInstructionLabel address R)
      (FullInterpreterState N) :=
  operandEvalProgram (.lit address) (Sum.inl ReadTransferLabel.initializeState)
    (readTransferProgram exhaustedLabel returnLabel right)

















def readInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + (3 * w + 8)







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CountdownGlobal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseCountdownProgram : CountdownLabel ->
    TM2.Stmt (fun _ : CountdownStack => SparseSymbol)
      CountdownLabel CountdownControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode countdownMachine.m







def countdownCoreEncode : CountdownStack -> CoreStack
  | .count => .work3
  | .temp => .work4

def countdownCoreDecode : CoreStack -> Option CountdownStack
  | .work3 => some .count
  | .work4 => some .temp
  | _ => none

def countdownCoreRenaming : StackRenaming CountdownStack CoreStack where
  encode := countdownCoreEncode
  decode := countdownCoreDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [countdownCoreDecode, countdownCoreEncode] at h ⊢

def countdownExit {R : Type} (zeroLabel positiveLabel : R) :
    CountdownLabel -> Option R
  | .zero => some zeroLabel
  | .positive => some positiveLabel
  | .scan | .restore => none

def countdownOnExit {N : Nat} (_ : CountdownLabel)
    (state : FullInterpreterState N) : FullInterpreterState N := state

def countdownMultiLeft {N : Nat} {R : Type}
    (zeroLabel positiveLabel : R) :
    CountdownLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (Sum CountdownLabel R)
      (FullInterpreterState N) :=
  lensMultiPhaseLeft countdownCoreRenaming FullInterpreterState.countdownLens
    sparseCountdownProgram (countdownExit zeroLabel positiveLabel)
    countdownOnExit







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ShiftRightMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive ShiftRightLabel | discard | prepend | first | second | done
  deriving DecidableEq, Fintype, Inhabited

def shiftRightMachine : Turing.FinTM2 where
  K := ShiftStack
  k₀ := .source
  k₁ := .result
  Γ _ := Bool
  Λ := ShiftRightLabel
  main := .discard
  σ := MoveControl
  initialState := default
  m
    | .discard =>
        .pop .source (fun _ _ => default) (.goto fun _ => .prepend)
    | .prepend =>
        .push .result (fun _ => false) (.goto fun _ => .first)
    | .first => moveIteration .source .temp .first .second
    | .second => moveIteration .temp .result .second .done
    | .done => .halt





















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ShiftCorePrimitives
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def sparseShiftLeftCoreProgram : ShiftLabel ->
    TM2.Stmt (fun _ : ShiftStack => SparseSymbol) ShiftLabel MoveControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode shiftMachine.m





def sparseShiftRightCoreProgram : ShiftRightLabel ->
    TM2.Stmt (fun _ : ShiftStack => SparseSymbol) ShiftRightLabel MoveControl :=
  mapAlphabetProgram sparseBitEncode sparseBitDecode shiftRightMachine.m





end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ShiftLeftRound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def shiftRoundEncode : ShiftStack -> CoreStack
  | .source => .accumulator
  | .temp => .work5
  | .result => .work6

def shiftRoundDecode : CoreStack -> Option ShiftStack
  | .accumulator => some .source
  | .work5 => some .temp
  | .work6 => some .result
  | _ => none

def shiftRoundRenaming : StackRenaming ShiftStack CoreStack where
  encode := shiftRoundEncode
  decode := shiftRoundDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [shiftRoundDecode, shiftRoundEncode] at h ⊢

abbrev ShiftRoundFinalLabel (R : Type) := Sum SymbolMoveLabel R
abbrev ShiftLeftRoundTailLabel (R : Type) :=
  Sum SymbolMoveLabel (ShiftRoundFinalLabel R)
abbrev ShiftLeftRoundLabel (R : Type) :=
  Sum ShiftLabel (ShiftLeftRoundTailLabel R)

def shiftRoundFinalProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftRoundFinalLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftRoundFinalLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def shiftLeftRoundTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftLeftRoundTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftLeftRoundTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work6 .work0 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (shiftRoundFinalProgram returnLabel right)

def shiftLeftRoundProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftLeftRoundLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftLeftRoundLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
      sparseShiftLeftCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (shiftLeftRoundTailProgram returnLabel right)

















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ShiftRightRound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev ShiftRightRoundLabel (R : Type) :=
  Sum ShiftRightLabel (ShiftLeftRoundTailLabel R)

def shiftRightRoundProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftRightRoundLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftRightRoundLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft shiftRoundRenaming FullInterpreterState.shiftLens
      sparseShiftRightCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (shiftLeftRoundTailProgram returnLabel right)













end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CappedShiftController
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive CappedShiftLabel
  | countdown (label : CountdownLabel)
  | fuel
  | left (label : ShiftLeftRoundLabel Unit)
  | right (label : ShiftRightRoundLabel Unit)
  | cleanupFuel
  | cleanupCount
  | cleanupTemp
  | done
  deriving DecidableEq, Fintype, Inhabited

def resetShiftControls {N : Nat} (state : FullInterpreterState N) :
    FullInterpreterState N :=
  FullInterpreterState.shiftLens.put
    (FullInterpreterState.countdownLens.put
      (FullInterpreterState.moveLens.put state default) default) default







def embedCountdownController : Sum CountdownLabel CappedShiftLabel ->
    CappedShiftLabel
  | .inl label => .countdown label
  | .inr label => label

def cappedShiftCleanupStmt {N : Nat} (stack : CoreStack)
    (again next : CappedShiftLabel) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N) :=
  .pop stack
    (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
  .branch (fun s =>
      (FullInterpreterState.moveLens.get s).held.isNone)
    (.goto fun _ => next)
    (.load (fun s => FullInterpreterState.moveLens.put s default) <|
      .goto fun _ => again)

def cappedShiftProgram {N : Nat} (rightShift : Bool) :
    CappedShiftLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) CappedShiftLabel
      (FullInterpreterState N)
  | .countdown label =>
      mapLabelStmt embedCountdownController <|
        countdownMultiLeft .cleanupFuel .fuel label
  | .fuel =>
      .pop .work1
        (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch (fun s =>
          (FullInterpreterState.moveLens.get s).held.isNone)
        (.goto fun _ => .cleanupFuel)
        (.load resetShiftControls <|
          .goto fun _ => if rightShift
            then .right (Sum.inl ShiftRightLabel.discard)
            else .left (Sum.inl ShiftLabel.first))
  | .left (Sum.inr (Sum.inr (Sum.inr ()))) =>
      .load (fun s => FullInterpreterState.countdownLens.put s default) <|
        .goto fun _ => .countdown .scan
  | .left label =>
      mapLabelStmt CappedShiftLabel.left <|
        shiftLeftRoundProgram () (fun _ => .halt) label
  | .right (Sum.inr (Sum.inr (Sum.inr ()))) =>
      .load (fun s => FullInterpreterState.countdownLens.put s default) <|
        .goto fun _ => .countdown .scan
  | .right label =>
      mapLabelStmt CappedShiftLabel.right <|
        shiftRightRoundProgram () (fun _ => .halt) label
  | .cleanupFuel =>
      cappedShiftCleanupStmt .work1 .cleanupFuel .cleanupCount
  | .cleanupCount =>
      cappedShiftCleanupStmt .work3 .cleanupCount .cleanupTemp
  | .cleanupTemp =>
      cappedShiftCleanupStmt .work4 .cleanupTemp .done
  | .done => .halt





end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CappedShiftCorrect
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2







































































def cappedShiftLoopBound (w : Nat) : Nat -> Nat
  | 0 => 3 * w + 7
  | fuel + 1 => 6 * w + 14 + cappedShiftLoopBound w fuel





















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_StoreIndInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

abbrev StoreIndInstructionLabel (address : Nat) (R : Type) :=
  OperandEvalLabel (.mem address) (StoreInstructionTailLabel R)

def storeIndInstructionProgram {N : Nat} {R : Type} (address : Nat)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    StoreIndInstructionLabel address R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (StoreIndInstructionLabel address R)
      (FullInterpreterState N) :=
  operandEvalProgram (.mem address) (Sum.inl StoreResetLabel.reset)
    (storeInstructionTailProgram returnLabel right)

def storeIndInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 4 * w + 11



end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ConditionalSubtractInstall
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2

inductive ConditionalInstallLabel
  | loop | done
  deriving DecidableEq, Fintype, Inhabited

def subtractInstallZero {N : Nat} (state : FullInterpreterState N) : Bool :=
  (FullInterpreterState.subLens.get state).borrow || state.subtractForceZero

def conditionalInstallProgram (N : Nat) : ConditionalInstallLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ConditionalInstallLabel
      (FullInterpreterState N)
  | .loop =>
      .pop .work0
        (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch (fun s => (FullInterpreterState.moveLens.get s).held.isNone)
        (.load (fun s => FullInterpreterState.moveLens.put s default) <|
          .goto fun _ => .done)
        (.push .accumulator (fun s =>
            if subtractInstallZero s then .bit false
            else (FullInterpreterState.moveLens.get s).held.getD (.bit false)) <|
          .load (fun s => FullInterpreterState.moveLens.put s default) <|
            .goto fun _ => .loop)
  | .done => .halt

















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullSubtractMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def fullStateIdentityLens (N : Nat) :
    StateLens (FullInterpreterState N) (FullInterpreterState N) where
  get := id
  put := fun _ value => value
  get_put := by intros; rfl
  put_get := by intros; rfl
  put_put := by intros; rfl

abbrev SubtractInstallPhaseLabel (R : Type) :=
  Sum ConditionalInstallLabel R

abbrev FullSubtractTailLabel (R : Type) :=
  Sum AddLabel (SubtractInstallPhaseLabel R)

abbrev FullSubtractLabel (R : Type) :=
  Sum SymbolMoveLabel (FullSubtractTailLabel R)

def subtractInstallPhaseProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    SubtractInstallPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (SubtractInstallPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming (fullStateIdentityLens N)
      (conditionalInstallProgram N) .done returnLabel)
    right

def fullSubtractTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullSubtractTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullSubtractTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft binaryCoreRenaming FullInterpreterState.subLens
      sparseSubCoreProgram .done (Sum.inl ConditionalInstallLabel.loop))
    (subtractInstallPhaseProgram returnLabel right)

def fullSubtractProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullSubtractLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullSubtractLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl AddLabel.loop))
    (fullSubtractTailProgram returnLabel right)

















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_SubtractInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive SubtractResetLabel
  | reset
  deriving DecidableEq, Fintype, Inhabited

abbrev SubtractInstructionTailLabel (R : Type) :=
  Sum SubtractResetLabel (FullSubtractLabel R)

abbrev SubtractInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (SubtractInstructionTailLabel R)

def operandForcesSubtractionZero {N : Nat} (o : Op)
    (state : FullInterpreterState N) : Bool :=
  match o with
  | .lit _ => (FullInterpreterState.literalLens.get state).remaining.val != 0
  | .mem _ | .ind _ => false

def subtractResetProgram {N : Nat} {R : Type} (o : Op) : SubtractResetLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (SubtractInstructionTailLabel R) (FullInterpreterState N)
  | .reset =>
      .load (fun s => FullInterpreterState.moveLens.put
        (FullInterpreterState.subLens.put
          { s with subtractForceZero := operandForcesSubtractionZero o s }
          default) default) <|
      .goto fun _ => Sum.inr (Sum.inl SymbolMoveLabel.loop)

def subtractInstructionTailProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    SubtractInstructionTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (SubtractInstructionTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram (subtractResetProgram o) (fullSubtractProgram returnLabel right)

def subtractInstructionProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    SubtractInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (SubtractInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl SubtractResetLabel.reset)
    (subtractInstructionTailProgram o returnLabel right)



def subtractInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + 3 * w + 8







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullDivideCore
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

def preparedDivEncode : DivStack -> CoreStack
  | .dividend => .work7
  | .divisor => .work1
  | .remainder => .work2
  | .quotient => .accumulator
  | .divisorBackup => .work3
  | .remainderBackup => .work4
  | .differenceReverse => .work5
  | .shiftTemp => .work6

def preparedDivDecode : CoreStack -> Option DivStack
  | .work7 => some .dividend
  | .work1 => some .divisor
  | .work2 => some .remainder
  | .accumulator => some .quotient
  | .work3 => some .divisorBackup
  | .work4 => some .remainderBackup
  | .work5 => some .differenceReverse
  | .work6 => some .shiftTemp
  | _ => none

def preparedDivRenaming : StackRenaming DivStack CoreStack where
  encode := preparedDivEncode
  decode := preparedDivDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [preparedDivDecode, preparedDivEncode] at h ⊢



















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullDivideCleanup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2

abbrev DivideCleanupFinalLabel (R : Type) := Sum DiscardLabel R
abbrev DivideCleanupTailLabel (R : Type) :=
  Sum DiscardLabel (DivideCleanupFinalLabel R)
abbrev FullDivideCleanLabel (R : Type) := Sum DivLabel (DivideCleanupTailLabel R)

def divideCleanupFinalProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideCleanupFinalLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideCleanupFinalLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work2)
      FullInterpreterState.moveLens discardProgram .done returnLabel)
    right

def divideCleanupTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideCleanupTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideCleanupTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft (discardCoreRenaming .work1)
      FullInterpreterState.moveLens discardProgram .done
      (Sum.inl DiscardLabel.loop))
    (divideCleanupFinalProgram returnLabel right)

def fullDivideCleanProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDivideCleanLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDivideCleanLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft preparedDivRenaming FullInterpreterState.divLens
      sparseDivCoreProgram .done (Sum.inl DiscardLabel.loop))
    (divideCleanupTailProgram returnLabel right)













end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullDivideMacro
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2



def divideZeroEncode : ZeroWordStack -> CoreStack
  | .query => .work1
  | .backup => .work3
  | .result => .work2

def divideZeroDecode : CoreStack -> Option ZeroWordStack
  | .work1 => some .query
  | .work3 => some .backup
  | .work2 => some .result
  | _ => none

def divideZeroRenaming : StackRenaming ZeroWordStack CoreStack where
  encode := divideZeroEncode
  decode := divideZeroDecode
  decode_encode := by intro k; cases k <;> rfl
  encode_decode := by
    intro k' k h
    cases k' <;> cases k <;>
      simp [divideZeroDecode, divideZeroEncode] at h ⊢

inductive DividePrepareLabel
  | pushExtension
  deriving DecidableEq, Fintype, Inhabited

abbrev DivideZeroTailLabel (R : Type) :=
  Sum ZeroWordLabel (FullDivideCleanLabel R)
abbrev DivideDividendTailLabel (R : Type) :=
  Sum SymbolMoveLabel (DivideZeroTailLabel R)
abbrev DivideDivisorTailLabel (R : Type) :=
  Sum SymbolMoveLabel (DivideDividendTailLabel R)
abbrev FullDivideLabel (R : Type) :=
  Sum DividePrepareLabel (DivideDivisorTailLabel R)

def dividePrepareReset {N : Nat} (state : FullInterpreterState N) :
    FullInterpreterState N :=
  FullInterpreterState.zeroLens.put
    (FullInterpreterState.divLens.put
      (FullInterpreterState.moveLens.put state default) default) default

def dividePrepareProgram {N : Nat} {R : Type} : DividePrepareLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol)
      (FullDivideLabel R) (FullInterpreterState N)
  | .pushExtension =>
      .push .work0 (fun _ => .bit false) <|
      .load dividePrepareReset <|
      .goto fun _ => Sum.inr (Sum.inl SymbolMoveLabel.loop)

def divideZeroTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideZeroTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideZeroTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft divideZeroRenaming FullInterpreterState.zeroLens
      zeroWordProgram .done (Sum.inl DivLabel.inspectDivisor))
    (fullDivideCleanProgram returnLabel right)

def divideDividendTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideDividendTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideDividendTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .accumulator .work7 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl ZeroWordLabel.fill))
    (divideZeroTailProgram returnLabel right)

def divideDivisorTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideDivisorTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideDivisorTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .work1 (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done
      (Sum.inl SymbolMoveLabel.loop))
    (divideDividendTailProgram returnLabel right)

def fullDivideProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDivideLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDivideLabel R)
      (FullInterpreterState N) :=
  liftRightProgram dividePrepareProgram
    (divideDivisorTailProgram returnLabel right)





















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ConditionalAccumulatorZero
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

def operandLiteralOversized {N : Nat} (o : Op)
    (state : FullInterpreterState N) : Bool :=
  match o with
  | .lit _ => (FullInterpreterState.literalLens.get state).remaining.val != 0
  | .mem _ | .ind _ => false

inductive ConditionalZeroLabel
  | rewrite | done
  deriving DecidableEq, Fintype, Inhabited

def conditionalZeroProgram (N : Nat) (o : Op) : ConditionalZeroLabel ->
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) ConditionalZeroLabel
      (FullInterpreterState N)
  | .rewrite =>
      .pop .accumulator
        (fun s a => FullInterpreterState.moveLens.put s ⟨a⟩) <|
      .branch (fun s => (FullInterpreterState.moveLens.get s).held.isNone)
        (.load (fun s => FullInterpreterState.moveLens.put s default) <|
          .goto fun _ => .done)
        (.push .work0 (fun s =>
            if operandLiteralOversized o s then .bit false
            else (FullInterpreterState.moveLens.get s).held.getD (.bit false)) <|
          .load (fun s => FullInterpreterState.moveLens.put s default) <|
            .goto fun _ => .rewrite)
  | .done => .halt















end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ConditionalAccumulatorZeroPhase
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

abbrev ConditionalZeroTailLabel (R : Type) := Sum SymbolMoveLabel R
abbrev ConditionalZeroPhaseLabel (R : Type) :=
  Sum ConditionalZeroLabel (ConditionalZeroTailLabel R)

def conditionalZeroTailProgram {N : Nat} {R : Type} (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ConditionalZeroTailLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ConditionalZeroTailLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft
      (symbolMoveCoreRenaming .work0 .accumulator (by decide))
      FullInterpreterState.moveLens symbolMoveCoreProgram .done returnLabel)
    right

def conditionalZeroPhaseProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ConditionalZeroPhaseLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ConditionalZeroPhaseLabel R)
      (FullInterpreterState N) :=
  liftRightProgram
    (lensPhaseLeft coreIdentityRenaming (fullStateIdentityLens N)
      (conditionalZeroProgram N o) .done (Sum.inl SymbolMoveLabel.loop))
    (conditionalZeroTailProgram returnLabel right)











end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ShiftInstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

inductive ShiftSetupLabel
  | initializeState
  | move (label : SymbolMoveLabel)
  | copy (label : CopyLabel)
  | controller (label : CappedShiftLabel)
  deriving DecidableEq, Fintype, Inhabited

def embedSetupMove : Sum SymbolMoveLabel Unit -> ShiftSetupLabel
  | .inl label => .move label
  | .inr () => .copy .scan

def embedSetupCopy : Sum CopyLabel Unit -> ShiftSetupLabel
  | .inl label => .copy label
  | .inr () => .controller (.countdown .scan)

def shiftSetupProgram {N : Nat} (rightShift : Bool) :
    ShiftSetupLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) ShiftSetupLabel
      (FullInterpreterState N)
  | .initializeState =>
      .load resetShiftControls <| .goto fun _ => .move .loop
  | .move label =>
      mapLabelStmt embedSetupMove <|
        lensPhaseLeft
          (symbolMoveCoreRenaming .work0 .work3 (by decide))
          FullInterpreterState.moveLens symbolMoveCoreProgram .done () label
  | .copy label =>
      mapLabelStmt embedSetupCopy <|
        lensPhaseLeft
          (copyCoreRenaming .accumulator .work1 .work7
            (by decide) (by decide) (by decide))
          FullInterpreterState.moveLens copyProgram .done () label
  | .controller label =>
      mapLabelStmt ShiftSetupLabel.controller
        (cappedShiftProgram rightShift label)





def shiftSetupBound (w : Nat) : Nat := 3 * w + 6

























def shiftCoreBound (w : Nat) : Nat :=
  shiftSetupBound w + cappedShiftLoopBound w w





abbrev FullShiftLabel (R : Type) :=
  Sum ShiftSetupLabel (ConditionalZeroPhaseLabel R)

def fullShiftLeft {N : Nat} {R : Type} (rightShift : Bool) :
    ShiftSetupLabel -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N)
  | .controller .done =>
      .load (fun s => FullInterpreterState.moveLens.put s default) <|
        .goto fun _ => Sum.inr (Sum.inl ConditionalZeroLabel.rewrite)
  | label => mapLabelStmt Sum.inl (shiftSetupProgram rightShift label)

def fullShiftProgram {N : Nat} {R : Type} (o : Op) (rightShift : Bool)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullShiftLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullShiftLabel R)
      (FullInterpreterState N) :=
  liftRightProgram (fullShiftLeft (R := R) rightShift)
    (conditionalZeroPhaseProgram o returnLabel right)







def fullShiftBound (w : Nat) : Nat := shiftCoreBound w + 2 * w + 5









abbrev ShiftInstructionLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (FullShiftLabel R)

def shiftInstructionProgram {N : Nat} {R : Type} (o : Op)
    (rightShift : Bool) (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    ShiftInstructionLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (ShiftInstructionLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl ShiftSetupLabel.initializeState)
    (fullShiftProgram o rightShift returnLabel right)

def shiftInstructionBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + fullShiftBound w









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_ProgramBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

/-- The only unbounded data occurring in a fixed RAM instruction which must
be emitted by the TM interpreter's finite control. -/
def instrArgument : Instr -> Nat
  | .read a | .store a | .storeInd a => a
  | .write o | .load o | .add o | .sub o | .mul o | .div o
  | .and o | .or o | .xor o | .compl o | .shiftl o | .shiftr o => operandArgument o
  | .jump _ | .jzero _ | .jgtz _ | .halt => 0

/-- A uniform finite bound for every literal/address embedded in `p`. -/
def programArgumentBound (p : Program) : Nat :=
  (p.map instrArgument).foldr max 0

theorem instrArgument_le_programArgumentBound {p : Program} {pc : Nat}
    {i : Instr} (hfetch : p[pc]? = some i) :
    instrArgument i <= programArgumentBound p := by
  have hpc : pc < p.length := fetch_some_pc_lt hfetch
  have hi : p[pc] = i := by
    simpa [List.getElem?_eq_getElem hpc] using hfetch
  have himem : i ∈ p := by
    rw [← hi]
    exact List.getElem_mem hpc
  apply List.le_max_of_le' 0 (List.mem_map.mpr ⟨i, himem, rfl⟩)
  exact le_rfl

/-- Finite syntax for an operand whose numeric parameter is at most `N`. -/
inductive BoundedOp (N : Nat)
  | lit (argument : Fin (N + 1))
  | mem (argument : Fin (N + 1))
  | ind (argument : Fin (N + 1))
  deriving DecidableEq, Fintype, Inhabited

def BoundedOp.toOp {N : Nat} : BoundedOp N -> Op
  | .lit n => .lit n
  | .mem n => .mem n
  | .ind n => .ind n



def BoundedOp.ofOp {N : Nat} (o : Op) (h : operandArgument o <= N) :
    BoundedOp N :=
  match o with
  | .lit n => .lit ⟨n, by simpa [operandArgument] using Nat.lt_succ_of_le h⟩
  | .mem n => .mem ⟨n, by simpa [operandArgument] using Nat.lt_succ_of_le h⟩
  | .ind n => .ind ⟨n, by simpa [operandArgument] using Nat.lt_succ_of_le h⟩

@[simp] theorem BoundedOp.toOp_ofOp {N : Nat} (o : Op)
    (h : operandArgument o <= N) : (BoundedOp.ofOp o h).toOp = o := by
  cases o <;> rfl



def operandEvalStartLabel {R : Type} (o : Op) : OperandEvalLabel o R := by
  cases o <;> exact Sum.inl LiteralWordLabel.emit





end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullDividePost
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

abbrev FullDividePostLabel (R : Type) :=
  FullDivideLabel (ConditionalZeroPhaseLabel R)

def fullDividePostProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    FullDividePostLabel R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FullDividePostLabel R)
      (FullInterpreterState N) :=
  fullDivideProgram (Sum.inl ConditionalZeroLabel.rewrite)
    (conditionalZeroPhaseProgram o returnLabel right)









end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_DivideInstructionTotal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

abbrev DivideInstructionTotalLabel (o : Op) (R : Type) :=
  OperandEvalLabel o (FullDividePostLabel R)

def divideInstructionTotalProgram {N : Nat} {R : Type} (o : Op)
    (returnLabel : R)
    (right : R -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) R
      (FullInterpreterState N)) :
    DivideInstructionTotalLabel o R -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (DivideInstructionTotalLabel o R)
      (FullInterpreterState N) :=
  operandEvalProgram o (Sum.inl DividePrepareLabel.pushExtension)
    (fullDividePostProgram o returnLabel right)

def divideInstructionTotalBound (w : Nat) (m : SparseMemory) : Nat :=
  operandEvalBound w m + divRunTimeBound w + 8 * w + 22





end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_InterpreterDispatcher
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section













def boundedAddress {N : Nat} (a : Nat) (h : a <= N) : Fin (N + 1) :=
  ⟨a, Nat.lt_succ_of_le h⟩

theorem instrArgument_le_of_boundedFetch {p : Program} (pc : BoundedPC p)
    {i : Instr} (hfetch : pc.fetch = some i) :
    instrArgument i <= programArgumentBound p := by
  have hlt : pc.val < p.length := by
    by_contra h
    simp [BoundedPC.fetch, h] at hfetch
  have hp : p[pc.val]? = some i := by
    simpa [BoundedPC.fetch, hlt] using hfetch
  exact instrArgument_le_programArgumentBound hp













def stmtIsHalt {α K Λ σ : Type} : TM2.Stmt (fun _ : K => α) Λ σ -> Bool
  | .halt => true
  | _ => false



































end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FiniteDispatcher
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section

abbrev LocalCode (L : Type) [Fintype L] := Fin (Fintype.card L)

def localCodeEquiv (L : Type) [Fintype L] : L ≃ LocalCode L :=
  Fintype.equivFin _

inductive FiniteInterpreterLabel (p : Program) (N : Nat)
  | fetch (pc : BoundedPC p)
  | read (pc : BoundedPC p) (address : Fin (N + 1))
      (code : LocalCode
        (ReadInstructionLabel address.val (Sum (BoundedPC p) Unit)))
  | write (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (WriteInstructionLabel o.toOp (BoundedPC p)))
  | load (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (LoadInstructionLabel o.toOp (BoundedPC p)))
  | store (pc : BoundedPC p) (address : Fin (N + 1))
      (code : LocalCode (StoreInstructionLabel address.val (BoundedPC p)))
  | storeInd (pc : BoundedPC p) (address : Fin (N + 1))
      (code : LocalCode (StoreIndInstructionLabel address.val (BoundedPC p)))
  | add (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (AddInstructionLabel o.toOp (BoundedPC p)))
  | sub (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (SubtractInstructionLabel o.toOp (BoundedPC p)))
  | mul (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (MulInstructionLabel o.toOp (BoundedPC p)))
  | div (pc : BoundedPC p) (o : BoundedOp N)
      (code : LocalCode (DivideInstructionTotalLabel o.toOp (BoundedPC p)))
  | bitwise (pc : BoundedPC p) (kind : BitwiseKind) (o : BoundedOp N)
      (code : LocalCode (ZipInstructionLabel o.toOp (BoundedPC p)))
  | shift (pc : BoundedPC p) (rightShift : Bool) (o : BoundedOp N)
      (code : LocalCode (ShiftInstructionLabel o.toOp (BoundedPC p)))
  | control (label : ControlDispatchLabel p)
  deriving Fintype, Inhabited





def encodeReadLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (address : Fin (N + 1))
    (label : ReadInstructionLabel address.val (Sum (BoundedPC p) Unit)) :
    FiniteInterpreterLabel p N :=
  match label with
  | .inr (.inr (.inr (.inr ()))) => .control .stopped
  | label => .read pc address (localCodeEquiv _ label)

def encodeWriteLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : WriteInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .write pc o (localCodeEquiv _ label)

def encodeLoadLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : LoadInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .load pc o (localCodeEquiv _ label)

def encodeStoreLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (address : Fin (N + 1))
    (label : StoreInstructionLabel address.val (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .store pc address (localCodeEquiv _ label)

def encodeStoreIndLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (address : Fin (N + 1))
    (label : StoreIndInstructionLabel address.val (BoundedPC p)) :
    FiniteInterpreterLabel p N :=
  .storeInd pc address (localCodeEquiv _ label)

def encodeAddLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : AddInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .add pc o (localCodeEquiv _ label)

def encodeSubLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : SubtractInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .sub pc o (localCodeEquiv _ label)

def encodeMulLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N) (label : MulInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .mul pc o (localCodeEquiv _ label)

def encodeDivLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (o : BoundedOp N)
    (label : DivideInstructionTotalLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .div pc o (localCodeEquiv _ label)

def encodeBitwiseLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (kind : BitwiseKind) (o : BoundedOp N)
    (label : ZipInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .bitwise pc kind o (localCodeEquiv _ label)

def encodeShiftLabel {p : Program} {N : Nat} (pc : BoundedPC p)
    (rightShift : Bool) (o : BoundedOp N)
    (label : ShiftInstructionLabel o.toOp (BoundedPC p)) :
    FiniteInterpreterLabel p N := .shift pc rightShift o (localCodeEquiv _ label)

def wrapFiniteLocal {p : Program} {N : Nat} {L : Type} [Fintype L]
    (encode : L -> FiniteInterpreterLabel p N) (next : BoundedPC p)
    (program : L -> TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) (code : LocalCode L) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  let label := (localCodeEquiv L).symm code
  let stmt := program label
  if stmtIsHalt stmt then .goto fun _ => .fetch next
  else mapLabelStmt encode stmt

def finiteEmbedControlLabel {p : Program} {N : Nat} :
    ControlDispatchLabel p -> FiniteInterpreterLabel p N
  | .fetch pc => .fetch pc
  | .scanAccumulator pc target z => .control (.scanAccumulator pc target z)
  | .restoreAccumulator pc target z => .control (.restoreAccumulator pc target z)
  | .data pc kind => .control (.data pc kind)
  | .stopped => .control .stopped

def finiteControlStmt {p : Program} {N : Nat} (label : ControlDispatchLabel p) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  mapLabelStmt
    (fun
      | Sum.inl l => finiteEmbedControlLabel l
      | Sum.inr e => nomatch e)
    (lensRenameStmt (Λx := Empty) coreIdentityRenaming
      FullInterpreterState.dispatchLens ((controlDispatchMachine p).m label))

def finiteInitializeEntry {p : Program} {N : Nat} (n : Nat) (hn : n <= N)
    (entry : FiniteInterpreterLabel p N) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  .load (fun s => FullInterpreterState.literalLens.put s
    (BoundedLiteralControl.initial hn)) (.goto fun _ => entry)

def finitePrepareInstr (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p)
    (i : Instr) (hfetch : pc.fetch = some i) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) := by
  have hi := instrArgument_le_of_boundedFetch pc hfetch
  have harg : instrArgument i <= N := hi.trans hbound
  cases i with
  | read a =>
          let address := boundedAddress a (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry a (by simpa [instrArgument] using harg)
            (encodeReadLabel pc address (operandEvalStartLabel (.lit a)))
  | write o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeWriteLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | load o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeLoadLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | store a =>
          let address := boundedAddress a (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry a (by simpa [instrArgument] using harg)
            (encodeStoreLabel pc address (operandEvalStartLabel (.lit a)))
  | storeInd a =>
          let address := boundedAddress a (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry a (by simpa [instrArgument] using harg)
            (encodeStoreIndLabel pc address (operandEvalStartLabel (.mem a)))
  | add o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeAddLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | sub o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeSubLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | mul o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeMulLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | div o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeDivLabel pc bo (by simpa [bo] using operandEvalStartLabel o))
  | and o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .and bo
              (by simpa [bo] using operandEvalStartLabel o))
  | or o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .or bo
              (by simpa [bo] using operandEvalStartLabel o))
  | xor o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .xor bo
              (by simpa [bo] using operandEvalStartLabel o))
  | compl o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeBitwiseLabel pc .compl bo
              (by simpa [bo] using operandEvalStartLabel o))
  | shiftl o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeShiftLabel pc false bo
              (by simpa [bo] using operandEvalStartLabel o))
  | shiftr o =>
          let bo := BoundedOp.ofOp o (by simpa [instrArgument] using harg)
          exact finiteInitializeEntry (operandArgument o) (by simpa [instrArgument] using harg)
            (encodeShiftLabel pc true bo
              (by simpa [bo] using operandEvalStartLabel o))
  | jump _ | jzero _ | jgtz _ | halt => exact .halt

def finitePrepareEntry (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) (pc : BoundedPC p) :
    TM2.Stmt (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) :=
  match hfetch : pc.fetch with
  | none => .halt
  | some i => finitePrepareInstr p N hbound pc i hfetch



def finiteInterpreterProgram (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) :
    FiniteInterpreterLabel p N -> TM2.Stmt
      (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N)
  | .fetch pc => finiteControlStmt (.fetch pc)
  | .control (.data pc _) => finitePrepareEntry p N hbound pc
  | .control label => finiteControlStmt label
  | .read pc address code => wrapFiniteLocal (encodeReadLabel pc address)
      (nextPC p pc) (readInstructionProgram address.val (.inr ())
        (.inl (nextPC p pc)) (fun _ => .halt)) code
  | .write pc o code => wrapFiniteLocal (encodeWriteLabel pc o)
      (nextPC p pc) (writeInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .load pc o code => wrapFiniteLocal (encodeLoadLabel pc o)
      (nextPC p pc) (loadInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .store pc address code => wrapFiniteLocal (encodeStoreLabel pc address)
      (nextPC p pc) (storeInstructionProgram address.val (nextPC p pc) (fun _ => .halt)) code
  | .storeInd pc address code => wrapFiniteLocal (encodeStoreIndLabel pc address)
      (nextPC p pc) (storeIndInstructionProgram address.val (nextPC p pc) (fun _ => .halt)) code
  | .add pc o code => wrapFiniteLocal (encodeAddLabel pc o)
      (nextPC p pc) (addInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .sub pc o code => wrapFiniteLocal (encodeSubLabel pc o)
      (nextPC p pc) (subtractInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .mul pc o code => wrapFiniteLocal (encodeMulLabel pc o)
      (nextPC p pc) (mulInstructionProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .div pc o code => wrapFiniteLocal (encodeDivLabel pc o)
      (nextPC p pc) (divideInstructionTotalProgram o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .bitwise pc kind o code => wrapFiniteLocal (encodeBitwiseLabel pc kind o)
      (nextPC p pc) (bitwiseInstructionProgram kind o.toOp (nextPC p pc) (fun _ => .halt)) code
  | .shift pc rightShift o code => wrapFiniteLocal (encodeShiftLabel pc rightShift o)
      (nextPC p pc) (shiftInstructionProgram o.toOp rightShift (nextPC p pc) (fun _ => .halt)) code



def finiteInterpreterCfg {p : Program} {N : Nat}
    (label : FiniteInterpreterLabel p N) (state : FullInterpreterState N)
    (tapes : CoreStack -> List SparseSymbol) :
    TM2.Cfg (fun _ : CoreStack => SparseSymbol) (FiniteInterpreterLabel p N)
      (FullInterpreterState N) := ⟨some label, state, tapes⟩























end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FiniteSimulation
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Turing TM2 Lax759944Proofs.Microcode

noncomputable section



















































































































































































/-- A deliberately coarse uniform bound for simulating any data instruction.
It is a sum rather than a maximum so each instruction bound discharges by
linear arithmetic and the eventual polynomial estimate stays transparent. -/
def finiteDataStepBound (w : Nat) (m : SparseMemory) : Nat :=
  3 + readInstructionBound w m + writeInstructionBound w m +
    loadInstructionBound w m + storeInstructionBound w m +
    storeIndInstructionBound w m + addInstructionBound w m +
    subtractInstructionBound w m + mulInstructionBound w m +
    divideInstructionTotalBound w m + zipInstructionBound w m +
    shiftInstructionBound w m

















































def finiteStepBound (w : Nat) (m : SparseMemory) : Nat :=
  finiteDataStepBound w m + (2 * w + 4)





























end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax263307_GraphClasses
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Hereditary graph classes
type: definition
---
A class of finite simple graphs is hereditary if it is closed under taking
induced subgraphs and under isomorphism.

# Formalization notes

Graphs are represented on vertex sets $\{0,\ldots,n-1\}$. Closure under
induced embeddings includes both induced subgraphs and all relabelings.
No algorithm for recognizing membership in the class is assumed.
-/

namespace Lax263307.GraphClasses

/-- A class of finite simple graphs, represented on numbered vertex sets. -/
abbrev GraphClass := (n : ℕ) → Set (SimpleGraph (Fin n))

/-- Every graph that embeds as an induced subgraph of a member also belongs. -/
def IsHereditary (C : GraphClass) : Prop :=
  ∀ (m n : ℕ) (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)),
    G ∈ C n → Nonempty (H ↪g G) → H ∈ C m

end Lax263307.GraphClasses

end

-- Solutions.RAM_Lax263307_EdgeSublinearSeparators
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Strongly edge-sublinear separators
type: definition
---
A balanced separator of an $n$-vertex graph $G$ is a vertex set $S$ such
that every connected component of $G-S$ has at most $2n/3$ vertices.
A graph class has strongly edge-sublinear separators if there are constants
$c>0$ and $0\le b<1$ such that each of its $m$-edge graphs has a balanced
separator of size at most $c(m+1)^b$.

# Formalization notes

The $+1$ makes the paper's asymptotic bound $O(m^b)$ meaningful at $m=0$:
a singleton graph needs a separator of size one under the stated balance
condition. For $m\ge1$ this normalization is equivalent to $O(m^b)$;
edgeless graphs of order at least two have an empty balanced separator.
Edges are counted as unordered pairs, using mathlib's edge set.
The balance inequality uses integers, $3|K|\le2n$, without rounding.
Heredity is a separate hypothesis in the main theorem.
-/

namespace Lax263307.EdgeSublinearSeparators

open GraphClasses

/-- Each component after deleting `S` contains at most two thirds of the vertices. -/
def IsBalancedSeparator {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  ∀ K : (G.induce (↑S : Set (Fin n))ᶜ).ConnectedComponent,
    3 * K.supp.ncard ≤ 2 * n

/-- A uniform separator bound sublinear in the number of edges. -/
def HasStronglyEdgeSublinearSeparators (C : GraphClass) : Prop :=
  ∃ (b c : ℝ), 0 ≤ b ∧ b < 1 ∧ 0 < c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧
        (S.card : ℝ) ≤ c * Real.rpow ((G.edgeSet.ncard : ℝ) + 1) b

end Lax263307.EdgeSublinearSeparators

end

-- Solutions.RAM_Lax263307_WeightedIndependentSet
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Weighted independent sets
type: definition
---
An instance consists of a finite simple graph and rational vertex weights.
A solution is a vertex set together with its ambient number of vertices.
The ambient number allows solutions for graphs of different orders to share
one type; feasibility requires it to agree with the instance.

An $(1-\varepsilon)$-approximation has weight at least
$(1-\varepsilon)w(J)$ for every independent set $J$.
Weights may be negative, and the empty set is always feasible.
All definitions here concern mathematical objects, independently of their
machine representations.
-/

namespace Lax263307.WeightedIndependentSet





/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

end Lax263307.WeightedIndependentSet

end

-- Solutions.RAM_Lax263307_IndependentSetEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Canonical representations of weighted graphs and vertex sets
type: definition
---
An instance is represented by its order, row-major adjacency matrix, and
rational vertex weights in vertex order. Each rational contributes its sign,
absolute numerator, and positive denominator. The resulting list uses the
registered structural list presentation. A vertex set is represented by its
zero-one membership vector, whose length records the ambient graph order.

These encoders inspect only the supplied graph, weights, and vertex set.
The private injectivity proofs certify the representations without introducing
any graph or weight decoder into the mathematical problem.
-/

namespace Lax263307.IndependentSetEncoding

open WeightedIndependentSet
open Lax759944.BinaryWordEncoding (bitSize)
open scoped Classical

/-- Canonical sign, absolute numerator, and denominator of a rational. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- The rational parameters in vertex order, followed by the accuracy. -/
def encodeParameters {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  (List.ofFn w).flatMap encodeRational ++ encodeRational ε

/-- Total binary encoding length of the weights and the accuracy. -/
def rationalBitSize {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℕ :=
  bitSize (encodeParameters w ε)

/-- The full input word, including the row-major adjacency matrix. -/
def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++ encodeParameters w ε

/-- The length-`n` membership vector of the selected independent set. -/
def encodeOutput {n : ℕ} (I : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ I then 1 else 0





end Lax263307.IndependentSetEncoding

end

-- Solutions.RAM_Lax263307_RecursionDepth
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RecursionDepth

open WeightedIndependentSet (IsApproximation)

def depth (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else 1 + depth (2 * n / 3)
termination_by n
decreasing_by omega


end Lax263307.RecursionDepth

end

-- Solutions.RAM_Lax263307_IndependentBlowUp
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Independent blow-ups and projection
type: definition
---
For a graph $G$ and nonnegative integer multiplicities $t_v$, replace vertex
$v$ by an independent set of $t_v$ copies. Copies of distinct vertices are
adjacent exactly when their original vertices are adjacent. Zero multiplicities
omit vertices. Lift a vertex set by taking all of its copies; project a set
of copies by taking the vertices represented by at least one selected copy.

# Formalization notes

A copy is a pair $(v,i)$ with $0\le i< t_v$. This dependent pair type has
exactly $\sum_v t_v$ elements and admits the usual finite-type instances.
The blow-up graph is the comap of $G$ along the projection to $v$.
The cardinality approximation predicate compares the returned independent
set with every independent set in this finite graph.
-/

namespace Lax263307.IndependentBlowUp

/-- The vertices of an independent blow-up, including possibly empty fibres. -/
abbrev Vertex {n : ℕ} (copies : Fin n → ℕ) := (v : Fin n) × Fin (copies v)

/-- Copies are adjacent precisely when their original vertices are adjacent. -/
def graph {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Vertex copies) := G.comap fun v => v.1



/-- Vertices represented by at least one selected copy. -/
def project {n : ℕ} {copies : Fin n → ℕ} (K : Finset (Vertex copies)) : Finset (Fin n) :=
  K.image fun v => v.1



end Lax263307.IndependentBlowUp

end

-- Solutions.RAM_Lax263307_BlowUpClasses
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.BlowUpClasses

open GraphClasses IndependentBlowUp


def blowUpClass (C : GraphClass) : GraphClass :=
  fun m => {H | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n ∧
    ∃ projection : Fin m → Fin n,
      ∀ u v, H.Adj u v ↔ G.Adj (projection u) (projection v)}


end Lax263307.BlowUpClasses

end

-- Solutions.RAM_Lax263307_LinearRelaxation
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The independent-set relaxation and its exact hull
type: definition
---
For an $n$-vertex graph $G$, target $k$, and level $r$, the relaxation
$R_r(G,k)$ has coordinates $y_A$ for vertex sets $|A|\le r+2$ and constraints
$$y_\varnothing=1,\qquad 0\le y_A\le1,$$
$$y_{A\cup\{v\}}\le y_A\quad (|A|\le r+1),$$
$$y_A=0\quad\text{if }A\text{ is not independent},$$
$$\sum_v y_{A\cup\{v\}}=k y_A\quad (|A|\le r+1).$$
The exact hull $P_r(G,k)$ is the convex hull of the vectors
$y_A=\mathbf1[A\subseteq I]$ over independent sets $I$ of size $k$.
For $y_A>0$, conditioning on $A$ gives costs $x_v=y_{A\cup\{v\}}/y_A$.

# Formalization notes

The coordinate type contains exactly the sets of size at most $r+2$;
there are no coordinates for larger sets. The accessor is extended by zero
outside this domain, solely to simplify notation. Every constraint that
uses it supplies a size bound ensuring that it reads an actual coordinate.
The vector space and convex hull are over the reals, as in the paper;
the algorithms will use rational points in this space.
-/

namespace Lax263307.LinearRelaxation

/-- The coordinate sets of the level-`r` relaxation. -/
abbrev Coordinate (n r : ℕ) := {A : Finset (Fin n) // A.card ≤ r + 2}

/-- A vector with precisely the coordinates used by the relaxation. -/
abbrev MomentVector (n r : ℕ) := Coordinate n r → ℝ



/-- The indicator encoding of a vertex set. -/
def indicator {n : ℕ} (r : ℕ) (I : Finset (Fin n)) : MomentVector n r :=
  fun A => if A.val ⊆ I then 1 else 0



/-- The convex hull of encodings of size-`k` independent sets. -/
def independentSetHull {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    Set (MomentVector n r) :=
  convexHull ℝ {y | ∃ I : Finset (Fin n),
    G.IsIndepSet (I : Set (Fin n)) ∧ I.card = k ∧ y = indicator r I}



/-- A certified upper bound on independent sets contained in a vertex set. -/
def IsIndependenceBound {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Finset (Fin n)) (u : ℕ) : Prop :=
  ∀ J : Finset (Fin n), J ⊆ C → G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u

end Lax263307.LinearRelaxation

end

-- Solutions.RAM_Lax263307_SeparatorComponents
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The components left by deleting a separator
type: definition
---
Deleting a vertex set $S$ partitions the remaining vertices into connected
components. Every undeleted vertex belongs to exactly one part, and every
edge with undeleted endpoints has both endpoints in one part. These are the
properties used to combine the recursive independent sets.

# Formalization notes

`Partition` also permits grouping connected components together. Its parts
are finite sets in the original vertex type. The proof package constructs
the canonical partition into connected components of $G-S$.
-/

namespace Lax263307.SeparatorComponents

/-- A partition of the undeleted vertices, closed under undeleted edges. -/
structure Partition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (ι : Type) where
  /-- The original vertices in each part. -/
  vertices : ι → Finset (Fin n)
  /-- Parts exclude the deleted vertices. -/
  outside : ∀ i v, v ∈ vertices i → v ∉ S
  /-- Every undeleted vertex belongs to exactly one part. -/
  unique : ∀ v, v ∉ S → ∃! i, v ∈ vertices i
  /-- No undeleted edge leaves a part. -/
  closed : ∀ i u v, u ∈ vertices i → v ∉ S → G.Adj u v → v ∈ vertices i

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents

end

-- Solutions.RAM_Lax263307_Entropy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Entropy and adjacency mass
type: definition
---
For a probability vector $\pi$ on $n$ vertices, its entropy in bits is
$$H(\pi)=-\sum_v\pi_v\log_2\pi_v,$$
with zero summands at zero probabilities. Its adjacency mass in a graph $G$ is
$$\sum_{u,v:\,uv\in E(G)}\pi_u\pi_v,$$
where ordered adjacent pairs are counted, so each edge contributes twice.

# Formalization notes

The auxiliary natural-log entropy differs by the positive factor $\ln2$.
Both definitions use mathlib's `negMulLog`, whose value at zero is zero.
The adjacency mass is an ordered sum, avoiding choices of edge orientations.
-/

namespace Lax263307.Entropy







/-- Total product probability of ordered adjacent vertex pairs. -/
noncomputable def adjacencyMass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (π : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then π u * π v else 0

/-- Sum of endpoint-cost products over unordered edges. -/
noncomputable def edgeCost {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  adjacencyMass G x / 2

end Lax263307.Entropy

end

-- Solutions.RAM_Lax455465_ProductNetwork
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Product multicommodity networks and sparsest cuts
type: definition
---
A product multicommodity network has nonnegative edge capacities and a
nonnegative weight $\pi(v)$ at each vertex. In an undirected network, the
demand between distinct vertices $u,v$ is $\pi(u)\pi(v)$, shared equally
between the two directions. In a directed network, the demand from $u$ to $v$
is $\pi(u)\pi(v)$ in each direction separately. Uniform demands are the case
$\pi\equiv1$.

The ratio cost of a cut $(S,\overline S)$ is
$$\frac{C(S,\overline S)}{\pi(S)\pi(\overline S)}.$$
Its numerator counts each undirected crossing edge once, or only arcs leaving
$S$ in the directed case. The sparsest-cut value is the infimum of these
ratios over cuts of positive demand. Write $p$ for the number of vertices
of positive weight.

# Formalization notes

Vertices are `Fin n`. A capacity matrix represents parallel edges by their
total capacity and absent edges by zero; loops are excluded. An undirected
network has a symmetric capacity matrix. The same cut formula applies in
both cases. Cuts of zero demand are excluded, including empty cuts. When
$p\ge2$, the set of admissible cuts is finite and nonempty, so its infimum
is a minimum. The theorems impose this hypothesis explicitly.

The logarithmic factor is $\log_2 p$, as in the paper. Stating product
bounds in terms of $p$ also handles the two-terminal case, where the
paper's shorthand $\log k$ vanishes because $k=\binom p2=1$.
-/

open scoped BigOperators NNReal

namespace Lax455465.ProductNetwork

/-- Whether capacities are shared by both directions of an edge or belong
to individual directed arcs. -/
inductive EdgeKind
  /-- One capacity shared by both directions of an undirected edge. -/
  | undirected
  /-- A separate capacity for each directed arc. -/
  | directed
  deriving DecidableEq

/-- A finite loopless network with nonnegative capacities. -/
structure Network (n : ℕ) where
  /-- The capacity of an edge or arc, with zero denoting absence. -/
  capacity : Fin n → Fin n → ℝ≥0
  /-- Loops are absent. -/
  loopless : ∀ v, capacity v v = 0

/-- An undirected network has the same capacity in both directions. -/
def Network.IsUndirected {n : ℕ} (N : Network n) : Prop :=
  ∀ u v, N.capacity u v = N.capacity v u

/-- The nonnegative weights whose products specify the demands. -/
abbrev VertexWeight (n : ℕ) := Fin n → ℝ≥0

/-- The number of vertices with positive weight. -/
noncomputable def supportCount {n : ℕ} (π : VertexWeight n) : ℕ :=
  (Finset.univ.filter fun v => 0 < π v).card

/-- The total vertex weight in a set. -/
def mass {n : ℕ} (π : VertexWeight n) (S : Finset (Fin n)) : ℝ≥0 :=
  ∑ v ∈ S, π v

/-- A cut separates positive total weight on both sides. -/
def AdmissibleCut {n : ℕ} (π : VertexWeight n) (S : Finset (Fin n)) : Prop :=
  0 < mass π S ∧ 0 < mass π Sᶜ

/-- The capacity leaving a cut; symmetric capacities count an undirected
edge exactly once. -/
def cutCapacity {n : ℕ} (N : Network n) (S : Finset (Fin n)) : ℝ≥0 :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.capacity u v

/-- The ratio of cut capacity to separated product demand. -/
noncomputable def ratioCost {n : ℕ} (N : Network n) (π : VertexWeight n)
    (S : Finset (Fin n)) : ℝ≥0 :=
  cutCapacity N S / (mass π S * mass π Sᶜ)





/-- The paper's base-two logarithm. -/
noncomputable def logFactor (p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log 2

end Lax455465.ProductNetwork

end

-- Solutions.RAM_Lax455465_ConcurrentFlow
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Concurrent fractional flow
type: definition
---
A fractional flow can be represented by nonnegative commodity/arc amounts
or by nonnegative amounts on finitely many simple paths.
It is feasible when the total load on every edge is at most its capacity.
Undirected edges carry the sum of the loads in both directions; directed arcs
carry only forward load. A concurrent flow of value $f$ meets $f$ times
every commodity's demand simultaneously. The maximum concurrent flow is the
supremum of feasible values.

# Formalization notes

The ordinary algorithm uses arc amounts with exact supply and conservation,
so its certificate has polynomially many coordinates. The short-path
algorithm uses explicit path records to certify the lengths.

A path is its ordered vertex list. Positive flow is supported only on lists
with at least two vertices and no repeated vertex. Its commodity is determined
by its endpoints, rather than stored separately. Requiring at least the stated
demand allows excess flow; deleting excess gives the usual equality formulation.
Cycles are unnecessary for fractional routing and can be deleted.

For undirected product demand, each ordered pair receives $f\pi(u)\pi(v)/2$;
for directed product demand it receives $f\pi(u)\pi(v)$. Only distinct
endpoints impose demands. An absent edge has zero capacity, so feasibility
prevents a positive-flow path from using it. There are finitely many simple
paths on `Fin n`; with at least two positive-weight vertices, feasible values
form a nonempty bounded set and the supremum is attained.
-/

open scoped BigOperators NNReal

namespace Lax455465.ConcurrentFlow

open Lax455465.ProductNetwork











/-- The demand assigned to an ordered pair of distinct endpoints. -/
noncomputable def pairDemand {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (s t : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => π s * π t / 2
  | .directed => π s * π t





/-- An arc flow records a nonnegative amount for each commodity and arc. -/
abbrev ArcFlow (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ≥0

/-- Aggregate forward capacity consumption in the edge formulation. -/
def totalArcLoad {n : ℕ} (F : ArcFlow n) (u v : Fin n) : ℝ≥0 :=
  ∑ s, ∑ t, F s t u v

/-- Shared or separate capacities in the edge formulation. -/
def totalEdgeLoad {n : ℕ} (kind : EdgeKind) (F : ArcFlow n) (u v : Fin n) : ℝ≥0 :=
  match kind with
  | .undirected => totalArcLoad F u v + totalArcLoad F v u
  | .directed => totalArcLoad F u v

/-- Net required supply at a vertex for one commodity; diagonal commodities
have zero supply at every vertex. -/
noncomputable def requiredSupply {n : ℕ} (kind : EdgeKind) (π : VertexWeight n)
    (f : ℝ≥0) (s t u : Fin n) : ℝ :=
  if s = t then 0 else
    (if u = s then (f * pairDemand kind π s t : ℝ≥0) else 0) -
    (if u = t then (f * pairDemand kind π s t : ℝ≥0) else 0)

/-- Capacity and exact commodity conservation in the polynomial-size arc formulation. -/
def IsArcConcurrentFlow {n : ℕ} (kind : EdgeKind) (N : Network n)
    (π : VertexWeight n) (f : ℝ≥0) (F : ArcFlow n) : Prop :=
  (∀ u v, totalEdgeLoad kind F u v ≤ N.capacity u v) ∧
  ∀ s t u, (∑ v, (F s t u v : ℝ)) - (∑ v, (F s t v u : ℝ)) =
    requiredSupply kind π f s t u

end Lax455465.ConcurrentFlow

end

-- Solutions.RAM_Lax455465_RationalEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Rational flow instances and certificates
type: definition
---
Finite algorithms receive nonnegative rational capacities and vertex weights.
Each rational is encoded by its reduced numerator and positive denominator.
An instance contains its edge model, number of vertices, vertex weights in
vertex order, and full capacity matrix in row order. A cut is encoded by
its length-$n$ membership word. An ordinary flow certificate contains its claimed value and the $n^4$
commodity/arc amounts. A short-path certificate instead contains its value
and a list of paths with rational flow amounts.

# Formalization notes

The dense encoding covers arbitrary rational capacities and weights, including
zero weights and absent edges. The first entry distinguishes directed from
undirected instances. Cut entries are exactly zero or one. A flow certificate
starts with the numerator and denominator of its value and the number of
path records; each record contains its vertex-count, vertex list, numerator,
and denominator. Repeated path records contribute their summed amount.

Algorithms use `Lax759944.RamPolytime.RamPolytime` directly. It quantifies
one actual program, polynomial word and instruction bounds in the binary
input size, and exact execution at every sufficiently large word length on
Lax808846's registered word RAM. The physical tape has the length prefix
specified by that predicate. No new machine or abstract cost oracle is used.
The algorithm's function is total; its output on malformed inputs is unconstrained.
-/

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- A product instance with nonnegative rational capacities and weights. -/
structure RationalInstance (n : ℕ) where
  /-- The rational capacity of each edge or directed arc. -/
  capacity : Fin n → Fin n → ℚ≥0
  /-- Loops have zero capacity. -/
  loopless : ∀ v, capacity v v = 0
  /-- The rational weights specifying product demands. -/
  weight : Fin n → ℚ≥0

/-- Interpret rational capacities as exact nonnegative real capacities. -/
def RationalInstance.network {n : ℕ} (I : RationalInstance n) : Network n where
  capacity u v := (I.capacity u v : ℝ≥0)
  loopless v := by simpa using congrArg (fun q : ℚ≥0 => (q : ℝ≥0)) (I.loopless v)

/-- Interpret rational vertex weights as exact nonnegative real weights. -/
def RationalInstance.weights {n : ℕ} (I : RationalInstance n) : VertexWeight n :=
  fun v => (I.weight v : ℝ≥0)

/-- Encode a nonnegative rational by its canonical numerator and denominator. -/
def encodeRational (q : ℚ≥0) : List ℕ := [q.num, q.den]

/-- Encode the edge model, order, weights, and row-major capacity matrix. -/
def encodeInput {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) : List ℕ :=
  [match kind with | .undirected => 0 | .directed => 1, n] ++
    (List.ofFn I.weight).flatMap encodeRational ++
    (List.ofFn fun u => List.ofFn (I.capacity u)).flatten.flatMap encodeRational

/-- Encode a shore as its length-`n` membership word. -/
def encodeCut {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  List.ofFn fun v => if v ∈ S then 1 else 0







/-- A polynomial-size rational arc-flow certificate for the ordinary theorem. -/
structure ArcCertificate (n : ℕ) where
  /-- The common demand fraction. -/
  value : ℚ≥0
  /-- The amount assigned to each commodity and directed arc. -/
  arcs : Fin n → Fin n → Fin n → Fin n → ℚ≥0

/-- Exact real interpretation of rational commodity/arc amounts. -/
def ArcCertificate.flow {n : ℕ} (certificate : ArcCertificate n) : ArcFlow n :=
  fun s t u v => (certificate.arcs s t u v : ℝ≥0)

/-- The value followed by all n⁴ arc coordinates in index order. -/
def encodeArcs {n : ℕ} (certificate : ArcCertificate n) : List ℕ :=
  encodeRational certificate.value ++
    (List.ofFn fun s => List.ofFn fun t => List.ofFn fun u => List.ofFn fun v =>
      encodeRational (certificate.arcs s t u v)).flatten.flatten.flatten.flatten

end Lax455465.RationalEncoding

end

-- Solutions.RAM_Lax455465_FlowCutCertificate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Exact flow–cut output certificates
type: definition
---
The output contains both a cut and a rational concurrent flow. For a product
instance with $p$ positive-weight vertices, the cut has positive demand, the
flow is feasible, and their values satisfy
$$\operatorname{ratio}(S)\le C\log_2(p)\,f.$$
The same output witnesses both sides of the algorithmic flow–cut guarantee.
A zero-capacity cut and the zero flow are valid when the instance has no
positive concurrent flow.

# Formalization notes

The output starts with the length-$n$ cut membership word, followed by the
existing rational arc-flow encoding. Validity is checked against the input;
an output annotation about its approximation ratio is never trusted.
-/

open scoped NNReal

namespace Lax455465.FlowCutCertificate

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

/-- The cut and rational path flow returned by a flow–cut algorithm. -/
structure Certificate (n : ℕ) where
  /-- One shore of the cut. -/
  cut : Finset (Fin n)
  /-- A concurrent flow with an explicitly claimed value. -/
  flow : ArcCertificate n

/-- The exact output contains the cut followed by the flow certificate. -/
def encodeCertificate {n : ℕ} (certificate : Certificate n) : List ℕ :=
  encodeCut certificate.cut ++ encodeArcs certificate.flow

/-- The joint guarantee for directed and undirected product demands. -/
def IsValid {n : ℕ} (kind : EdgeKind) (I : RationalInstance n) (C : ℝ)
    (certificate : Certificate n) : Prop :=
  AdmissibleCut I.weights certificate.cut ∧
  IsArcConcurrentFlow kind I.network I.weights
    (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
  (ratioCost I.network I.weights certificate.cut : ℝ) ≤
    C * logFactor (supportCount I.weights) * (certificate.flow.value : ℝ)

end Lax455465.FlowCutCertificate

end

-- Solutions.RAM_Lax263307_VertexSplitting
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.VertexSplitting

open Lax455465.FlowCutCertificate (Certificate encodeCertificate)
open Lax759944.RamPolytime (RamPolytime)
open scoped NNReal NNRat
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow


def minus {n : ℕ} (v : Fin n) : Fin (2 * n) :=
  ⟨2 * v.val, Nat.mul_lt_mul_of_pos_left v.isLt (Nat.succ_pos 1)⟩

def plus {n : ℕ} (v : Fin n) : Fin (2 * n) :=
  ⟨2 * v.val + 1, (Nat.mul_succ 2 v.val).symm.trans_le (Nat.mul_le_mul_left 2 v.isLt)⟩

def original {n : ℕ} (v : Fin (2 * n)) : Fin n :=
  ⟨v.val / 2, (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr
    (Nat.mul_comm 2 n ▸ v.isLt)⟩


def splitInstance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) : RationalInstance (2 * n) where
  capacity u v :=
    if u.val % 2 = 0 ∧ v.val = u.val + 1 then x (original u)
    else if u.val % 2 = 1 ∧ v.val + 1 = u.val then large
    else if u.val % 2 = 1 ∧ v.val % 2 = 0 ∧ G.Adj (original u) (original v) then large
    else 0
  loopless v :=
    (if_neg (fun h => Nat.ne_of_lt (Nat.lt_succ_self v.val) h.2)).trans
      ((if_neg (fun h => Nat.ne_of_gt (Nat.lt_succ_self v.val) h.2)).trans
        (if_neg (fun h => h.2.2.ne rfl)))
  weight _ := 1


def leftShore {n : ℕ} (U : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => minus v ∈ U


def rightShore {n : ℕ} (U : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => plus v ∉ U


end Lax263307.VertexSplitting

end

-- Solutions.RAM_Lax263307_PositiveWeights
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.PositiveWeights

open WeightedIndependentSet


def positiveWeights {n : ℕ} (w : Fin n → ℚ) : Fin n → ℚ := fun v => max (w v) 0


def discardNonpositive {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : Finset (Fin n) :=
  I.filter fun v => 0 < w v


end Lax263307.PositiveWeights

end

-- Solutions.RAM_Lax263307_WeightRounding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Scaling weights to integer multiplicities
type: definition
---
For nonnegative rational vertex weights, let $W$ be the maximum weight and
choose $\tau=\varepsilon W/(2n)$. The rounded multiplicity of vertex $v$ is
$t_v=\lfloor w_v/\tau\rfloor$. Vertices with $t_v=0$ are omitted from the
independent blow-up.

# Formalization notes

The maximum includes zero, so it is defined also on the empty graph and on
signed weights before preprocessing. The rounding estimates assume
$n>0$, $W>0$, and $\varepsilon>0$, ensuring $\tau>0$.
The natural-valued floor is computed on exact rational numbers.
-/

namespace Lax263307.WeightRounding

/-- The maximum of the vertex weights and zero. -/
def maximumWeight {n : ℕ} (w : Fin n → ℚ) : ℚ :=
  (insert 0 (Finset.univ.image w)).max' (Finset.insert_nonempty _ _)

/-- The weight unit used by the reduction. -/
def scale {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℚ :=
  ε * maximumWeight w / (2 * n)

/-- Multiplicities at a specified positive weight unit. -/
def roundedCopies {n : ℕ} (w : Fin n → ℚ) (τ : ℚ) : Fin n → ℕ :=
  fun v => ⌊w v / τ⌋₊

/-- The multiplicities chosen for the requested accuracy. -/
def copies {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : Fin n → ℕ :=
  roundedCopies w (scale w ε)

end Lax263307.WeightRounding

end

-- Solutions.RAM_Lax263307_RationalConditioning
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RationalConditioning

open LinearRelaxation Entropy


abbrev RationalVector (n r : ℕ) := Coordinate n r → ℚ





def rationalValue {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) : ℚ :=
  if h : A.card ≤ r + 2 then y ⟨A, h⟩ else 0


def edgeNumerator {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) : ℚ :=
  ∑ u, ∑ v, if G.Adj u v then
    rationalValue y (insert u A) * rationalValue y (insert v A) else 0


def Passes {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Prop :=
  0 < rationalValue y A ∧
    (p : ℚ) * edgeNumerator G y A ≤ 2 * (k : ℚ) ^ 2 * rationalValue y A ^ 2


instance {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Decidable (Passes G k p y A) :=
  inferInstanceAs (Decidable (0 < rationalValue y A ∧
    (p : ℚ) * edgeNumerator G y A ≤ 2 * (k : ℚ) ^ 2 * rationalValue y A ^ 2))


def candidates (n r : ℕ) : List (Finset (Fin n)) :=
  (List.range (r + 1)).flatMap fun j =>
    ((List.finRange n).sublistsLen j).map List.toFinset





end Lax263307.RationalConditioning

end

-- Solutions.RAM_Lax263307_CoordinateCatalog
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax263307.CoordinateCatalog

open LinearRelaxation RationalConditioning

theorem mem_candidates (n r : ℕ) (A : Finset (Fin n)) :
    A ∈ candidates n r ↔ A.card ≤ r :=
  ⟨fun member =>
    let ⟨j, inRange, inSublists⟩ := List.mem_flatMap.mp member
    let ⟨vertices, listed, sameSet⟩ := List.mem_map.mp inSublists
    let sublist := (List.mem_sublistsLen.mp listed).1
    let length := (List.mem_sublistsLen.mp listed).2
    calc
      A.card = vertices.toFinset.card := congrArg Finset.card sameSet.symm
      _ = vertices.length := List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))
      _ = j := length
      _ ≤ r := Nat.le_of_lt_succ (List.mem_range.mp inRange),
   fun bounded =>
    let vertices := (List.finRange n).filter fun v => decide (v ∈ A)
    let sublist : vertices.Sublist (List.finRange n) := List.filter_sublist
    let sameSet : vertices.toFinset = A := Finset.ext fun v =>
      List.mem_toFinset.trans (List.mem_filter.trans
        ⟨fun h => of_decide_eq_true h.2,
         fun h => ⟨List.mem_finRange v, decide_eq_true h⟩⟩)
    let length : vertices.length = A.card :=
      (List.toFinset_card_of_nodup (sublist.nodup (List.nodup_finRange n))).symm.trans
        (congrArg Finset.card sameSet)
    List.mem_flatMap.mpr ⟨A.card, List.mem_range.mpr (Nat.lt_succ_of_le bounded),
      List.mem_map.mpr ⟨vertices, List.mem_sublistsLen.mpr ⟨sublist, length⟩, sameSet⟩⟩⟩

def sets (n r : ℕ) : List (Finset (Fin n)) := (candidates n (r + 2)).dedup

def catalog (n r : ℕ) : List (Coordinate n r) :=
  (sets n r).attach.map (fun A => ⟨A.val,
    (mem_candidates n (r + 2) A.val).mp
      (List.mem_dedup.mp A.property)⟩)

theorem mem_catalog (n r : ℕ) (A : Coordinate n r) : A ∈ catalog n r :=
  let listed : A.val ∈ sets n r :=
    List.mem_dedup.mpr ((mem_candidates n (r + 2) A.val).mpr A.property)
  List.mem_map.mpr ⟨⟨A.val, listed⟩, List.mem_attach _ _, Subtype.ext rfl⟩

theorem catalog_nodup (n r : ℕ) : (catalog n r).Nodup :=
  (List.nodup_dedup _).attach.map fun _ _ equal =>
    Subtype.ext (congrArg (fun coordinate : Coordinate n r => coordinate.val) equal)

def indexing (n r : ℕ) : Fin (catalog n r).length ≃ Coordinate n r :=
  List.Nodup.getEquivOfForallMemList (catalog n r) (catalog_nodup n r) (mem_catalog n r)

end Lax263307.CoordinateCatalog

end

-- Solutions.RAM_Lax109476_LinearProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Linear programs and their duals
type: definition
---
A linear program in inequality form is
$$\max\{c^T x: Ax\le b,\ x\ge0\}.$$
Its dual is
$$\min\{b^T y: A^T y\ge c,\ y\ge0\}.$$
All vector inequalities are componentwise. A feasible maximization program
is bounded above if one finite real number bounds the objective of every
feasible point. A primal point is optimal if it is feasible and no feasible
point has a larger objective.

# Formalization notes

There are `n` variables and `m` inequalities, indexed by `Fin n` and `Fin m`.
The coefficient data are shared by real and rational instances. Feasibility
and objective formulas are the same in either field. Both dimensions may be
zero. No feasibility, boundedness, optimizer, or optimum value is bundled
into the input data. Theorems state the necessary hypotheses explicitly.
Equality constraints and unrestricted variables can be represented by paired
inequalities and differences of nonnegative variables.
-/

open scoped BigOperators

namespace Lax109476.LinearProgram

/-- Coefficients of a maximization program with `m` inequalities and `n`
nonnegative variables. -/
structure Program (K : Type) (m n : ℕ) where
  /-- The constraint matrix. -/
  A : Fin m → Fin n → K
  /-- The upper bounds on the constraint rows. -/
  b : Fin m → K
  /-- The coefficients of the maximized objective. -/
  c : Fin n → K

/-- The value of one constraint row at a primal point. -/
def rowValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) (i : Fin m) : K :=
  ∑ j, P.A i j * x j

/-- One component of the transposed matrix applied to a dual point. -/
def columnValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) (j : Fin n) : K :=
  ∑ i, P.A i j * y i

/-- The primal objective value. -/
def primalValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (x : Fin n → K) : K :=
  ∑ j, P.c j * x j

/-- The dual objective value. -/
def dualValue {K : Type} [Ring K] {m n : ℕ} (P : Program K m n)
    (y : Fin m → K) : K :=
  ∑ i, P.b i * y i

/-- A nonnegative primal point satisfies all row upper bounds. -/
def PrimalFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (x : Fin n → K) : Prop :=
  (∀ j, 0 ≤ x j) ∧ ∀ i, rowValue P x i ≤ P.b i

/-- A nonnegative dual point dominates every objective coefficient. -/
def DualFeasible {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ ∀ j, P.c j ≤ columnValue P y j







end Lax109476.LinearProgram

end

-- Solutions.RAM_Lax109476_FarkasCertificate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Certificates of infeasibility
type: definition
---
For the system $Ax\le b$, $x\ge0$, an infeasibility certificate is a vector
$y$ satisfying
$$y\ge0,\qquad A^T y\ge0,\qquad b^T y<0.$$
Such a vector is incompatible with primal feasibility: multiplying the
constraints by $y$ would give $0\le y^T Ax\le y^T b<0$.

# Formalization notes

The certificate is defined over the same coefficient field as the program,
so rational certificates can be checked exactly. The objective coefficients
are irrelevant to this certificate. Existence of a certificate for every
infeasible real system is the separate Farkas theorem.
-/

namespace Lax109476.FarkasCertificate

open Lax109476.LinearProgram

/-- Nonnegative row multipliers certify an impossible negative upper bound. -/
def IsInfeasibilityCertificate {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (y : Fin m → K) : Prop :=
  (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ columnValue P y j) ∧ dualValue P y < 0

end Lax109476.FarkasCertificate

end

-- Solutions.RAM_Lax109476_RecessionDirection
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Certificates of unboundedness
type: definition
---
An improving recession direction satisfies
$$d\ge0,\qquad Ad\le0,\qquad c^T d>0.$$
Together with any primal feasible point $x$, it certifies unboundedness:
$x+td$ is feasible for every $t\ge0$ and its objective tends to infinity.

# Formalization notes

A direction alone does not certify that the primal is unbounded: the
feasible set could be empty. Certificates therefore include a feasible
base point as well as the direction.
-/

namespace Lax109476.RecessionDirection

open Lax109476.LinearProgram

/-- A nonnegative direction preserves every upper constraint and improves
the maximized objective. -/
def IsImprovingDirection {K : Type} [Ring K] [PartialOrder K] {m n : ℕ}
    (P : Program K m n) (d : Fin n → K) : Prop :=
  (∀ j, 0 ≤ d j) ∧ (∀ i, rowValue P d i ≤ 0) ∧ 0 < primalValue P d

end Lax109476.RecessionDirection

end

-- Solutions.RAM_Lax109476_RationalCertificates
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Exact rational solution certificates
type: definition
---
A rational linear program is a linear program with rational coefficients,
still optimized over real variables. Its outcomes have three certificate forms:

* an optimal primal point and matching dual multipliers;
* nonnegative Farkas multipliers certifying infeasibility;
* a feasible primal point and an improving recession direction certifying
  unboundedness.

Every coordinate in these certificates is rational, and all certificate
conditions can be checked by exact rational arithmetic.

# Formalization notes

The three constructors carry precisely the witnesses needed for their
claims. The predicates use the same row, column, and objective formulas
as the real program. The real interpretation casts the coefficient data
and witness coordinates exactly. No outcome or correctness proof is
assumed as part of the input.
-/

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection





/-- A rational certificate for one of the three possible LP outcomes. -/
inductive Certificate (m n : ℕ)
  /-- Primal and dual points with matching objectives. -/
  | optimal (x : Fin n → ℚ) (y : Fin m → ℚ)
  /-- Separating nonnegative multipliers for an infeasible primal system. -/
  | infeasible (y : Fin m → ℚ)
  /-- A feasible base point and an improving recession direction. -/
  | unbounded (x d : Fin n → ℚ)

/-- The exact rational inequalities and equalities validating a certificate. -/
def IsValidCertificate {m n : ℕ} (P : Program ℚ m n) : Certificate m n → Prop
  | .optimal x y => PrimalFeasible P x ∧ DualFeasible P y ∧ primalValue P x = dualValue P y
  | .infeasible y => IsInfeasibilityCertificate P y
  | .unbounded x d => PrimalFeasible P x ∧ IsImprovingDirection P d



end Lax109476.RationalCertificates

end

-- Solutions.RAM_Lax109476_RationalEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Binary-size encoding of rational linear programs
type: definition
---
An LP input word begins with its number of inequalities $m$ and variables
$n$, followed by the matrix in row order, the vector $b$, and the vector $c$.
A rational is encoded by its numerator sign, numerator magnitude, and
positive denominator, in reduced form. Solution words begin with an outcome
tag and contain the corresponding rational certificate coordinates.

# Formalization notes

The input sign is zero for nonnegative numerators and one for negative
numerators. Output tags zero, one, and two mean optimal, infeasible, and
unbounded. Dimensions are supplied by the input, so witness vectors have
fixed known lengths. Each rational keeps its exact denominator.

The imported `RamPolytime` predicate uses binary word-list size, a single
uniform program, polynomial bounds on sufficient word length and executed
instructions, and correctness at every sufficiently large word length on
Lax808846's registered RAM. Its specified physical tape is length-prefixed.
Malformed logical inputs have no prescribed output, but the solver function
is total. No new machine model or abstract running-time annotation is introduced.
-/

namespace Lax109476.RationalEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Encode a reduced rational by sign, magnitude, and denominator. -/
def encodeRational (q : ℚ) : List ℕ :=
  [if q.num < 0 then 1 else 0, q.num.natAbs, q.den]

/-- Encode all coordinates of a rational vector in index order. -/
def encodeVector {n : ℕ} (x : Fin n → ℚ) : List ℕ :=
  (List.ofFn x).flatMap encodeRational

/-- Encode dimensions, row-major coefficients, row bounds, and objective. -/
def encodeProgram {m n : ℕ} (P : Program ℚ m n) : List ℕ :=
  [m, n] ++ (List.ofFn fun i => List.ofFn (P.A i)).flatten.flatMap encodeRational ++
    encodeVector P.b ++ encodeVector P.c

/-- Encode the outcome tag and all rational certificate coordinates. -/
def encodeCertificate {m n : ℕ} : Certificate m n → List ℕ
  | .optimal x y => [0] ++ encodeVector x ++ encodeVector y
  | .infeasible y => [1] ++ encodeVector y
  | .unbounded x d => [2] ++ encodeVector x ++ encodeVector d

end Lax109476.RationalEncoding

end

-- Solutions.RAM_Lax109476Proofs_RationalSizeBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι : Type*} [Fintype ι]

/-- A common denominator obtained without factorization. -/
def commonDenominator (q : ι → ℚ) : ℕ := ∏ i, (q i).den





def clearedNumerator (q : ι → ℚ) (i : ι) : ℤ :=
  (q i).num * (commonDenominator q / (q i).den : ℕ)

























end Lax109476Proofs.RationalSizeBounds

end

-- Solutions.RAM_Lax109476Proofs_EncodingSize
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.EncodingSize

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding
open Lax109476.LinearProgram



















/-- All rational data occurring in the input, indexed without duplication. -/
def programData {m n : ℕ} (P : Program ℚ m n) :
    ((Fin m × Fin n) ⊕ (Fin m ⊕ Fin n)) → ℚ :=
  Sum.elim (fun ij => P.A ij.1 ij.2) (Sum.elim P.b P.c)









end Lax109476Proofs.EncodingSize

end

-- Solutions.RAM_Lax109476Proofs_IntegerEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RationalSizeBounds EncodingSize

def programDenominator {m n : ℕ} (P : Program ℚ m n) : ℕ :=
  commonDenominator (programData P)

def integerProgram {m n : ℕ} (P : Program ℚ m n) : Program ℤ m n where
  A i j := clearedNumerator (programData P) (.inl (i, j))
  b i := clearedNumerator (programData P) (.inr (.inl i))
  c j := clearedNumerator (programData P) (.inr (.inr j))

def rationalProgram {m n : ℕ} (P : Program ℤ m n) : Program ℚ m n where
  A i j := P.A i j
  b i := P.b i
  c j := P.c j





























end Lax109476Proofs.IntegerEncoding

end

-- Solutions.RAM_Lax808846Proofs_Frame
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
The frame rule: what a run *cannot* have changed, read off its syntax.

Almost every statement about a phase of an algorithm is half functional
and half negative. The functional half says what the phase computed; the
negative half says that everything else is where it was. Written by
hand, the negative half is a universally quantified conjunct per lemma —
`∀ y, y ≠ "ro" → y ≠ "cnted" → ρ'.vars y = ρ.vars y` — which the caller
then has to destructure again at every use, and which has to be
re-established by hand every time two phases are composed.

It need not be written at all. Which scalars a command may assign to,
which arrays it may store into, and whether it touches the input tape
are all *syntactic*, and the environment of `Imp` is aliasing-free, so
the syntactic answer is the true one. This file computes the three
answers as `Com.wvars`, `Com.warrs` and `Com.reads`, and proves the
three frame theorems by the induction that `BigStep.out_eq` already
does for the output tape.

A call site then pays `by decide` — or `by simp`, which is faster on
long lists of string literals — against the concrete syntax of its own
program, in place of carrying and destructuring a quantified hypothesis.
The four `Env` fields are covered uniformly: `vars` by `Run.frame_var`,
`arrs` by `Run.frame_arr`, `inp` by `Run.frame_inp` and `out` by
`Run.out_eq` of `Reasoning`, whose `Com.NoWrite` is the same idea
predating this file.

The lists are over-approximations, deliberately: `wvars` of an `ite`
unions both branches rather than asking which one runs, and `while`
takes its body's whether or not the loop turns at all. A frame condition
is wanted for names the command never mentions, and for those the crude
answer is already exact.
-/

namespace Lax808846Proofs.Imp

/-- The scalar variables a command may assign to. Both branches of an
`ite` count, and the body of a `while` counts once. -/
def Com.wvars : Com → List String
  | .skip => []
  | .assign x _ => [x]
  | .store _ _ _ => []
  | .seq c d => c.wvars ++ d.wvars
  | .ite _ c d => c.wvars ++ d.wvars
  | .while _ c => c.wvars
  | .read x => [x]
  | .write _ => []

/-- The arrays a command may store into. -/
def Com.warrs : Com → List String
  | .skip => []
  | .assign _ _ => []
  | .store a _ _ => [a]
  | .seq c d => c.warrs ++ d.warrs
  | .ite _ c d => c.warrs ++ d.warrs
  | .while _ c => c.warrs
  | .read _ => []
  | .write _ => []











/-! ### Equation lemmas, materialized here

`Com.wvars`, `Com.warrs` and `Com.reads` are defined by `match`, so
their equation lemmas and match splitters are created on first use.
Downstream a first use is `simp [Com.wvars]` inside some algorithm
proof, and creating them there leaves *that* package holding
declarations named under `Lax808846Proofs`, which the archive's namespace
rule rejects. These three trivial statements ask for them here; every
later `simp` finds them among its imports and creates nothing. This is
the standing kit rule, and it applies to every match-defined function
this kit ever exports. -/







end Lax808846Proofs.Imp

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

/-! ### The three frame theorems

Each is the induction of `BigStep.out_eq`, driven by the syntactic
over-approximation instead of by a hand-written predicate. They are
stated on `BigStep` — where the induction lives — and then on `Run`,
which is what an algorithm proof has in hand. -/





















end Lax808846Proofs.Reasoning

end

-- Solutions.RAM_Lax808846Proofs_Spec
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
Specifications: what a phase of a program does, as an object that
composes.

`Run` is a judgment about *one* pair of environments. A phase lemma
written directly in it has to be stated as an existential — "there are
`ρ'` and `K` with `Run B c ρ ρ' K` and `K ≤ 30` and these frame
conditions and this disjunction of cases" — and composing two of them is
`obtain` on the first, `obtain` on the second, and a hand-assembled
`refine` for the result. Every phase lemma in the repo has that shape,
and every use of one pays for it twice: once to take the existential
apart, once to put the successor back together.

`Spec B P c Q K` packages the same content as a *predicate on the
program*: from any state satisfying `P`, the command `c` runs to a state
standing in relation `Q` to it, at a cost of at most `K`. The
existential moves inside the definition, and with it the `obtain`s: two
phases compose by `Spec.seq`, which is a term, not a tactic block.

Three decisions are worth stating, since they are what make the
interface fit this repo rather than a textbook.

* **`Q` is relational.** A phase lemma says `ρ'.vars "ro" = ρ.vars "ro"
  + 1`, not `ρ'.vars "ro" = 7`; a postcondition that could not mention
  the initial environment would force every such statement through an
  auxiliary variable. So `Q : Env → Env → Prop`, initial environment
  first.
* **The cost is one number, an upper bound.** It rides in the `Run`,
  where it is already an upper bound, so `Spec.mono` is slack-taking and
  nothing else. Loops whose cost is amortized state their potential in
  the loop rule and export a constant, which is what the phase lemmas of
  the repo already do.
* **`B` is a parameter of the whole interface**, not an implicit
  argument recovered from the goal. `B` occurs in no hypothesis that
  determines it — a phase lemma with no `< B` side condition left it
  entirely undetermined and the caller had to write `(B := B)` by
  hand. In a `Spec` it is the first explicit argument.

The frame rule of `Frame.lean` enters through `Spec.frame`, which
strengthens any specification with the four frame conditions its command
allows, read off the syntax. A composed phase therefore never
re-establishes a frame condition: it inherits one for the `seq` it is.
-/

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp

variable {B : ℕ} {P P' : Env → Prop} {Q Q' R : Env → Env → Prop} {c d : Com} {K K' : ℕ}

/-- `Spec B P c Q K`: started in any state satisfying `P`, the command
`c` terminates in a state standing in relation `Q` to the one it started
in, at a cost of at most `K`, every value it produces staying below
`B`. -/
def Spec (B : ℕ) (P : Env → Prop) (c : Com) (Q : Env → Env → Prop) (K : ℕ) : Prop :=
  ∀ σ, P σ → ∃ σ', Run B c σ σ' K ∧ Q σ σ'





/-! ### The structural rules -/











/-! ### The rules of the language -/







/-! The two tape operations. Both are stated the way `assign` and
`store` are — the caller names what the operation moves as a function of
the state it is in — and both are relational in the tape they touch,
since a phase says how the tape it was handed *changed*, never what it
is. -/











/-! ### The loop rules

`Run.while_potential` stays the primitive: its step obligation carries
an existential cost, which is exactly what an amortized loop needs and
what a `Spec`'s fixed `K` cannot express. What the rules here add is the
packaging — the loop's own cost, which depends on the state it starts
in, is discharged against `K` once, by the caller, at the top. -/





/-! ### Reading a comparison of two scalars

The loop condition of every scan in the repo is `x < m` on two scalars.
These say what its truth and its falsity mean, which `Spec.forRange`
needs and which every hand-written loop proof was re-deriving. -/









end Lax808846Proofs.Reasoning

end

-- Solutions.RAM_Lax109476Proofs_RamArithmetic
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- One Euclidean step uses only operations compiled to the registered RAM. -/
def gcdStep : Com :=
  .seq (.assign "gcd.t" (.sub (.var "gcd.a")
    (.mul (.div (.var "gcd.a") (.var "gcd.b")) (.var "gcd.b"))))
    (.seq (.assign "gcd.a" (.var "gcd.b")) (.assign "gcd.b" (.var "gcd.t")))



def gcdDoubleStep : Com :=
  .seq gcdStep (.ite (.lt (.lit 0) (.var "gcd.b")) gcdStep .skip)

def gcdLoop : Com := .while (.lt (.lit 0) (.var "gcd.b")) gcdDoubleStep











/-- Reduce an unsigned numerator and positive denominator in place. The sign
is held separately by the rational representation and is left untouched. -/
def normalizeFraction : Com :=
  .seq (.assign "gcd.a" (.var "rat.n"))
    (.seq (.assign "gcd.b" (.var "rat.d"))
      (.seq gcdLoop
        (.seq (.assign "rat.n" (.div (.var "rat.n") (.var "gcd.a")))
          (.assign "rat.d" (.div (.var "rat.d") (.var "gcd.a"))))))



end Lax109476Proofs.RamArithmetic

end

-- Solutions.RAM_Lax109476Proofs_RamRational
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic















def invertFraction : Com :=
  .ite (.eq (.var "left.n") (.lit 0))
    (.seq (.assign "rat.n" (.lit 0))
      (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
    (.seq (.assign "rat.n" (.var "left.d"))
      (.seq (.assign "rat.d" (.var "left.n"))
        (.seq (.assign "rat.s" (.var "left.s")) normalizeFraction)))





def multiplyFraction : Com :=
  .seq (.assign "rat.n" (.mul (.var "left.n") (.var "right.n")))
    (.seq (.assign "rat.d" (.mul (.var "left.d") (.var "right.d")))
      (.seq (.ite (.eq (.var "left.s") (.var "right.s"))
        (.assign "rat.s" (.lit 0)) (.assign "rat.s" (.lit 1))) normalizeFraction))









def addFraction : Com :=
  .seq (.assign "sum.u" (.mul (.var "left.n") (.var "right.d")))
    (.seq (.assign "sum.v" (.mul (.var "right.n") (.var "left.d")))
      (.seq (.assign "rat.d" (.mul (.var "left.d") (.var "right.d")))
        (.seq (.ite (.eq (.var "left.s") (.var "right.s"))
          (.seq (.assign "rat.n" (.add (.var "sum.u") (.var "sum.v")))
            (.assign "rat.s" (.var "left.s")))
          (.ite (.lt (.var "sum.u") (.var "sum.v"))
            (.seq (.assign "rat.n" (.sub (.var "sum.v") (.var "sum.u")))
              (.assign "rat.s" (.var "right.s")))
            (.seq (.assign "rat.n" (.sub (.var "sum.u") (.var "sum.v")))
              (.assign "rat.s" (.var "left.s"))))) normalizeFraction)))



end Lax109476Proofs.RamRational

end

-- Solutions.RAM_Lax109476Proofs_RamSquareRoot
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSquareRoot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def sqrtStep : Com :=
  .seq (.assign "sqrt.mid" (.div (.add (.var "sqrt.lo") (.var "sqrt.hi")) (.lit 2)))
    (.ite (.lt (.var "sqrt.n") (.mul (.var "sqrt.mid") (.var "sqrt.mid")))
      (.assign "sqrt.hi" (.var "sqrt.mid")) (.assign "sqrt.lo" (.var "sqrt.mid")))

def sqrtLoop : Com :=
  .while (.lt (.lit 1) (.sub (.var "sqrt.hi") (.var "sqrt.lo"))) sqrtStep

def squareRoot : Com :=
  .seq (.assign "sqrt.lo" (.lit 0))
    (.seq (.assign "sqrt.hi" (.add (.var "sqrt.n") (.lit 1))) sqrtLoop)









end Lax109476Proofs.RamSquareRoot

end

-- Solutions.RAM_Lax109476Proofs_RamRounding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRounding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic











def roundFraction : Com :=
  .seq (.assign "round.a" (.mul (.var "left.n") (.var "grid.D")))
    (.seq (.assign "round.q" (.div (.var "round.a") (.var "left.d")))
      (.seq (.assign "round.r" (.sub (.var "round.a")
        (.mul (.var "round.q") (.var "left.d"))))
        (.seq (.assign "rat.n" (.var "round.q"))
          (.seq (.ite (.eq (.var "left.s") (.lit 1))
            (.ite (.eq (.var "round.r") (.lit 0)) .skip
              (.assign "rat.n" (.add (.var "rat.n") (.lit 1)))) .skip)
            (.seq (.assign "rat.s" (.var "left.s"))
              (.seq (.assign "rat.d" (.var "grid.D")) normalizeFraction))))))









def upperRootFraction : Com :=
  .seq (.assign "round.a" (.mul (.mul (.var "left.n") (.var "grid.D")) (.var "grid.D")))
    (.seq (.assign "round.q" (.div (.var "round.a") (.var "left.d")))
      (.seq (.assign "round.r" (.sub (.var "round.a")
        (.mul (.var "round.q") (.var "left.d"))))
        (.seq (.assign "sqrt.n" (.var "round.q"))
          (.seq (.ite (.eq (.var "round.r") (.lit 0)) .skip
            (.assign "sqrt.n" (.add (.var "sqrt.n") (.lit 1))))
            (.seq (.ite (.eq (.var "left.s") (.lit 1)) (.assign "sqrt.n" (.lit 0)) .skip)
              (.seq RamSquareRoot.squareRoot
                (.seq (.assign "rat.n" (.add (.var "sqrt.lo") (.lit 1)))
                  (.seq (.assign "rat.s" (.lit 0))
                    (.seq (.assign "rat.d" (.var "grid.D")) normalizeFraction)))))))))



end Lax109476Proofs.RamRounding

end

-- Solutions.RAM_Lax109476Proofs_RamComparison
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational







def compareFraction : Com :=
  .seq (.assign "cmp.u" (.mul (.var "left.n") (.var "right.d")))
    (.seq (.assign "cmp.v" (.mul (.var "right.n") (.var "left.d")))
      (.ite (.eq (.var "left.s") (.var "right.s"))
        (.ite (.eq (.var "left.s") (.lit 1))
          (.ite (.lt (.var "cmp.u") (.var "cmp.v"))
            (.assign "cmp.le" (.lit 0)) (.assign "cmp.le" (.lit 1)))
          (.ite (.lt (.var "cmp.v") (.var "cmp.u"))
            (.assign "cmp.le" (.lit 0)) (.assign "cmp.le" (.lit 1))))
        (.ite (.eq (.var "left.s") (.lit 1)) (.assign "cmp.le" (.lit 1))
          (.ite (.eq (.var "left.n") (.lit 0))
            (.ite (.eq (.var "right.n") (.lit 0))
              (.assign "cmp.le" (.lit 1)) (.assign "cmp.le" (.lit 0)))
            (.assign "cmp.le" (.lit 0))))))





end Lax109476Proofs.RamComparison

end

-- Solutions.RAM_Lax109476Proofs_RamEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open Lax109476.RationalEncoding



/-- Emit the registered canonical triple, removing a possible internal
negative sign on zero. All three writes are part of the proved cost. -/
def writeReducedFraction : Com :=
  .seq (.ite (.eq (.var "rat.n") (.lit 0)) (.write (.lit 0)) (.write (.var "rat.s")))
    (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))



end Lax109476Proofs.RamEncoding

end

-- Solutions.RAM_Lax109476Proofs_RamRationalArrays
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalArrays

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def rationalSign (q : ℚ) : ℕ := if q.num < 0 then 1 else 0





/-- Three arrays hold reduced rational coordinates. Separating the three
fields avoids index multiplication when scanning a vector or matrix row. -/
def Represents (a : String) (qs : List ℚ) (σ : Env) : Prop :=
  σ.arrs (a ++ ".s") = qs.map rationalSign ∧
    σ.arrs (a ++ ".n") = qs.map (fun q => q.num.natAbs) ∧
    σ.arrs (a ++ ".d") = qs.map (fun q => q.den)

def loadLeft (a : String) : Com :=
  .seq (.assign "left.s" (.get (a ++ ".s") (.var "vec.i")))
    (.seq (.assign "left.n" (.get (a ++ ".n") (.var "vec.i")))
      (.assign "left.d" (.get (a ++ ".d") (.var "vec.i"))))









def loadRight (a : String) : Com :=
  .seq (.assign "right.s" (.get (a ++ ".s") (.var "vec.i")))
    (.seq (.assign "right.n" (.get (a ++ ".n") (.var "vec.i")))
      (.assign "right.d" (.get (a ++ ".d") (.var "vec.i"))))







def storeReduced (a : String) : Com :=
  .seq (.ite (.eq (.var "rat.n") (.lit 0))
    (.store (a ++ ".s") (.var "vec.i") (.lit 0))
    (.store (a ++ ".s") (.var "vec.i") (.var "rat.s")))
    (.seq (.store (a ++ ".n") (.var "vec.i") (.var "rat.n"))
      (.store (a ++ ".d") (.var "vec.i") (.var "rat.d")))



end Lax109476Proofs.RamRationalArrays

end

-- Solutions.RAM_Lax109476Proofs_RamFractionInterface
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFractionInterface

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRounding















def resultToLeft : Com :=
  .seq (.assign "left.s" (.var "rat.s"))
    (.seq (.assign "left.n" (.var "rat.n")) (.assign "left.d" (.var "rat.d")))

def resultToRight : Com :=
  .seq (.assign "right.s" (.var "rat.s"))
    (.seq (.assign "right.n" (.var "rat.n")) (.assign "right.d" (.var "rat.d")))













def negateRight : Com := .assign "right.s" (.sub (.lit 1) (.var "right.s"))



def subtractFraction : Com := .seq negateRight addFraction







end Lax109476Proofs.RamFractionInterface

end

-- Solutions.RAM_Lax109476Proofs_RamCenterCoordinate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCenterCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface

/-- One stored center coordinate is rounded after the exact rational update. -/
def centerCoordinate : Com :=
  .seq (.assign "vec.i" (.var "center.i"))
    (.seq (loadLeft "ell.u")
      (.seq (.assign "vec.i" (.lit 2))
        (.seq (loadRight "ell.coeff")
          (.seq multiplyFraction
            (.seq resultToRight
              (.seq (.assign "vec.i" (.var "center.i"))
                (.seq (loadLeft "ell.center")
                  (.seq subtractFraction
                    (.seq resultToLeft (.seq RamRounding.roundFraction (storeReduced "ell.nextcenter")))))))))))













end Lax109476Proofs.RamCenterCoordinate

end

-- Solutions.RAM_Lax808846Proofs_Lib_Fill
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
An array filled cell by cell by a counter: the array, a scalar counting
how much of it is done, and the promise that everything below the
counter already holds what it should.

This is what a *pass* over an array leaves behind, and the repo is full
of them — Lax11's read loop copying the tape into `off` and into `tgt`,
its `initLab` marking every vertex unvisited, every array a search
initialises. Each of them wrote out the same invariant by hand
("`i ≤ n`, and there is a `g` with `arrs a = arrOf n g` and `∀ j < i,
g j = F j`"), the same one-turn extension of it, and the same reading of
it at the exit. Here that is proved once.

The module is the counterpart of `Spec.forRangeZero`, not a competitor:
that rule owns the loop, this one owns what the loop's body does to the
array, and `loop_spec` at the end is the two of them put together — the
whole phase `x := 0; while x < m do (a[x] := e; x := x + 1)` as one
specification, at a cost of `(10 + e.size) · n + 6`.

### Two forms of the relation

`Fill a x n i g F σ` names the cell function `g` and the counter's value
`i`, as `Stack` names its height: what a *specification* changes has to
be a parameter, since it cannot be recovered from an intermediate state.
`Fill.Below a x n F σ` hides both — the counter is read off `σ` and the
cell function is existentially quantified — and that is the form a *loop
invariant* needs, since neither is fixed over a loop. The operations are
proved in the first form and exported in the second, which is the only
place the two meet.

What is deliberately absent is any statement about the cells at or above
the counter: a fill says nothing about where it has not been yet, so the
caller's precondition is only that the array has the right length.
-/

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v : ℕ} {a b x y m : String} {g F : ℕ → ℕ} {σ : Env}

/-! ### The relation -/





























/-! Everything from here on is this module's own — the loop-invariant
form of the relation, the operation, its specification and the phase
they add up to — so it lives in the module's namespace. -/

namespace Fill

/-! ### The loop-invariant form

A loop cannot hold the cell function or the counter fixed, so the form
an invariant is stated in has neither: the counter is whatever `σ` says
and the cell function is quantified away. Everything a caller needs of
it comes back out at the exit, when `Spec.forRangeZero` reports the
counter *at* the bound. -/















/-! ### The operation

One command, parameterized in the array, the counter and the expression
whose value is filled in. It is a store and a bump, which is what every
fill in the repo already writes; its cost is `6 + e.size`, the store's
`2 + e.size` and the bump's `4`. -/

/-- Put the value of `e` into the cell the counter `x` names, and move
the counter up. -/
def put (a x : String) (e : Expr) : Com :=
  .seq (.store a (.var x) e) (.assign x (.add (.var x) (.lit 1)))

/-! The frame conditions, as `simp` lemmas: a call site's array and
counter are bound variables, so `Spec.frame`'s obligations are
discharged there by `simp` and not by `decide`. -/









/-! ### The specification -/





/-! ### The phase

The loop and its body together: `Spec.forRangeZero` owns the counter and
the cost, `put_spec` owns the array, and what is left for the caller is
the one thing neither can know — what the cell it is filling in should
hold. -/



/-! ### The worked example

Fill a three-cell array with the counter's own value, then write the
three cells out. `demo` is the phase the specification is about;
`demoWatched` is the same phase with the reads appended, so that the
machine can be seen doing it. -/

namespace Demo















/-! And the arithmetic on the other side of the abstraction: three turns
of a fill with the identity. -/

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

-- Solutions.RAM_Lax109476Proofs_RamZeroArray
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamZeroArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

/-- Array extent is a ghost parameter of the verified RAM compiler; this
phase initializes every field that will subsequently represent a rational. -/
def fillConstant (a : String) (v : ℕ) : Com :=
  .seq (.assign "vec.i" (.lit 0))
    (.while (.lt (.var "vec.i") (.var "vec.n")) (Lib.Fill.put a "vec.i" (.lit v)))





def zeroRationalArray (a : String) : Com :=
  .seq (fillConstant (a ++ ".s") 0)
    (.seq (fillConstant (a ++ ".n") 0) (fillConstant (a ++ ".d") 1))



end Lax109476Proofs.RamZeroArray

end

-- Solutions.RAM_Lax109476Proofs_RamCenterUpdate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCenterUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface
open RamCenterCoordinate RamZeroArray













def centerStep : Com := .seq centerCoordinate (.assign "center.i" (.add (.var "center.i") (.lit 1)))



def centerLoop : Com :=
  .seq (.assign "center.i" (.lit 0)) (.while (.lt (.var "center.i") (.var "vec.n")) centerStep)

def updateCenter : Com := .seq (zeroRationalArray "ell.nextcenter") centerLoop













end Lax109476Proofs.RamCenterUpdate

end

-- Solutions.RAM_Lax109476Proofs_RamCopy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays








def leftToResult : Com :=
  .seq (.assign "rat.s" (.var "left.s"))
    (.seq (.assign "rat.n" (.var "left.n")) (.assign "rat.d" (.var "left.d")))



def copyCoordinate (a b : String) : Com :=
  .seq (.assign "vec.i" (.var "copy.i"))
    (.seq (loadLeft a) (.seq leftToResult (storeReduced b)))





def copyStep (a b : String) : Com :=
  .seq (copyCoordinate a b) (.assign "copy.i" (.add (.var "copy.i") (.lit 1)))



def copyLoop (a b : String) : Com :=
  .seq (.assign "copy.i" (.lit 0)) (.while (.lt (.var "copy.i") (.var "vec.n")) (copyStep a b))



def copyRationalArray (a b : String) : Com := .seq (RamZeroArray.zeroRationalArray b) (copyLoop a b)



end Lax109476Proofs.RamCopy

end

-- Solutions.RAM_Lax109476Proofs_RamRationalScalars
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalArrays



def readLeft (name : String) : Com := .seq (.assign "left.s" (.var (name ++ ".s")))
  (.seq (.assign "left.n" (.var (name ++ ".n"))) (.assign "left.d" (.var (name ++ ".d"))))

def readRight (name : String) : Com := .seq (.assign "right.s" (.var (name ++ ".s")))
  (.seq (.assign "right.n" (.var (name ++ ".n"))) (.assign "right.d" (.var (name ++ ".d"))))

def save (name : String) : Com := .seq (.assign (name ++ ".s") (.var "rat.s"))
  (.seq (.assign (name ++ ".n") (.var "rat.n")) (.assign (name ++ ".d") (.var "rat.d")))







end Lax109476Proofs.RamRationalScalars

end

-- Solutions.RAM_Lax109476Proofs_RamScalarCopy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamScalarCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def copy (a b : String) : Com := .seq (.assign (b ++ ".s") (.var (a ++ ".s")))
  (.seq (.assign (b ++ ".n") (.var (a ++ ".n"))) (.assign (b ++ ".d") (.var (a ++ ".d"))))



end Lax109476Proofs.RamScalarCopy

end

-- Solutions.RAM_Lax109476Proofs_RamArrayResult
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamArrayResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars

def load (a : String) : Com := .seq (loadLeft a) RamCopy.leftToResult





end Lax109476Proofs.RamArrayResult

end

-- Solutions.RAM_Lax109476Proofs_RamInput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The physical length prefix makes end-of-input checks available to the
structured RAM program without reading from an exhausted tape. -/
def safeRead (x : String) : Com := .ite (.lt (.lit 0) (.var "input.remaining"))
  (.seq (.read x) (.assign "input.remaining" (.sub (.var "input.remaining") (.lit 1))))
  (.seq (.assign "input.valid" (.lit 0)) (.assign x (.lit 0)))



def startInput : Com := .seq (.read "input.remaining") (.assign "input.valid" (.lit 1))



end Lax109476Proofs.RamInput

end

-- Solutions.RAM_Lax109476Proofs_RamReadFraction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamRational RamArithmetic

def validateFraction : Com := .ite (.lt (.var "rat.s") (.lit 2))
  (.ite (.lt (.lit 0) (.var "rat.d")) normalizeFraction (.assign "input.valid" (.lit 0)))
  (.assign "input.valid" (.lit 0))

def readRawFraction : Com := .seq (safeRead "rat.s") (.seq (safeRead "rat.n") (safeRead "rat.d"))

def readFraction : Com := .seq readRawFraction validateFraction



















def zeroResult : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))



def safeFraction : Com := .seq readFraction
  (.ite (.eq (.var "input.valid") (.lit 1)) .skip zeroResult)





end Lax109476Proofs.RamReadFraction

end

-- Solutions.RAM_Lax109476Proofs_RamReadArray
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadFraction RamRational RamRationalArrays RamCenterUpdate
open RamArithmetic











def readStep (a : String) : Com := .seq safeFraction
  (.seq (storeReduced a) (.assign "vec.i" (.add (.var "vec.i") (.lit 1))))



def readLoop (a : String) : Com := .seq (.assign "vec.i" (.lit 0))
  (.while (.lt (.var "vec.i") (.var "vec.n")) (readStep a))



def readArray (a : String) : Com := .seq (RamZeroArray.zeroRationalArray a) (readLoop a)



















end Lax109476Proofs.RamReadArray

end

-- Solutions.RAM_Lax109476Proofs_RamDotProduct
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamDotProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays













def multiplyAt (a b : String) : Com :=
  .seq (loadLeft a) (.seq (loadRight b) multiplyFraction)









def addToAccumulator : Com :=
  .seq (.assign "right.s" (.var "rat.s")) (.seq (.assign "right.n" (.var "rat.n")) (.seq (.assign "right.d" (.var "rat.d")) (.seq (.assign "left.s" (.var "dot.s")) (.seq (.assign "left.n" (.var "dot.n")) (.seq (.assign "left.d" (.var "dot.d")) (.seq (addFraction) (.seq (.assign "dot.s" (.var "rat.s")) (.seq (.assign "dot.n" (.var "rat.n")) (.seq (.assign "dot.d" (.var "rat.d")) (.assign "vec.i" (.add (.var "vec.i") (.lit 1))))))))))))



def dotStep (a b : String) : Com := .seq (multiplyAt a b) addToAccumulator





def dotProduct (a b : String) : Com :=
  .seq (.assign "dot.s" (.lit 0))
    (.seq (.assign "dot.n" (.lit 0))
      (.seq (.assign "dot.d" (.lit 1))
        (.seq (.assign "vec.i" (.lit 0))
          (.while (.lt (.var "vec.i") (.var "vec.n")) (dotStep a b)))))









end Lax109476Proofs.RamDotProduct

end

-- Solutions.RAM_Lax109476Proofs_RamMatrixRows
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamMatrixRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRational RamDotProduct





def loadRowLeft (a : String) : Com :=
  .seq (.assign "left.s" (.get (a ++ ".s") (.add (.var "row.base") (.var "vec.i"))))
    (.seq (.assign "left.n" (.get (a ++ ".n") (.add (.var "row.base") (.var "vec.i"))))
      (.assign "left.d" (.get (a ++ ".d") (.add (.var "row.base") (.var "vec.i")))))





def multiplyRowAt (a b : String) : Com :=
  .seq (loadRowLeft a) (.seq (loadRight b) multiplyFraction)







def rowDotStep (a b : String) : Com := .seq (multiplyRowAt a b) addToAccumulator





def rowDotProduct (a b : String) : Com :=
  .seq (.assign "dot.s" (.lit 0))
    (.seq (.assign "dot.n" (.lit 0))
      (.seq (.assign "dot.d" (.lit 1))
        (.seq (.assign "vec.i" (.lit 0))
          (.while (.lt (.var "vec.i") (.var "vec.n")) (rowDotStep a b)))))







def matrixRowDot (a b : String) : Com :=
  .seq (.assign "row.base" (.mul (.var "row.i") (.var "vec.n"))) (rowDotProduct a b)



end Lax109476Proofs.RamMatrixRows

end

-- Solutions.RAM_Lax109476Proofs_RamMatrixStorage
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamMatrixStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows

def flatten {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : List ℚ :=
  List.ofFn (fun k : Fin (m * n) => A k.divNat k.modNat)











end Lax109476Proofs.RamMatrixStorage

end

-- Solutions.RAM_Lax109476Proofs_RamReadBlock
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamRationalArrays







def readBlock (a field : String) : Com :=
  .seq (.assign "vec.n" (.var field)) (readArray a)




end Lax109476Proofs.RamReadBlock

end

-- Solutions.RAM_Lax109476Proofs_RamShapeCoordinate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamShapeCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface

def addDiagonal : Com :=
  .ite (.eq (.var "entry.i") (.var "entry.j"))
    (.seq resultToLeft (.seq (.assign "vec.i" (.lit 4))
      (.seq (loadRight "ell.coeff") addFraction))) .skip

def entryIndex : Com :=
  .seq (.assign "entry.i" (.div (.var "entry.k") (.var "vec.n")))
    (.assign "entry.j" (.sub (.var "entry.k") (.mul (.var "entry.i") (.var "vec.n"))))

def entryProduct : Com :=
  .seq entryIndex (.seq (.assign "vec.i" (.var "entry.i")) (.seq (loadLeft "ell.u") (.seq (.assign "vec.i" (.var "entry.j")) (.seq (loadRight "ell.u") (multiplyFraction)))))

def shapeDifference : Com :=
  .seq resultToRight (.seq (.assign "vec.i" (.lit 1)) (.seq (loadLeft "ell.coeff") (.seq multiplyFraction (.seq resultToRight (.seq (.assign "vec.i" (.var "entry.k")) (.seq (loadLeft "ell.shape") (subtractFraction)))))))

def roundedEntry : Com :=
  .seq resultToRight (.seq (.assign "vec.i" (.lit 0)) (.seq (loadLeft "ell.coeff") (.seq multiplyFraction (.seq resultToLeft (RamRounding.roundFraction)))))

def inflatedEntry : Com :=
  .seq addDiagonal (.seq resultToRight (.seq (.assign "vec.i" (.lit 3)) (.seq (loadLeft "ell.coeff") (.seq multiplyFraction (.seq (.assign "vec.i" (.var "entry.k")) ((storeReduced "ell.nextshape")))))))

/-- One rounded shape entry, using the stored vector and step coefficients. -/
def shapeCoordinate : Com :=
  .seq entryProduct (.seq shapeDifference (.seq roundedEntry inflatedEntry))































end Lax109476Proofs.RamShapeCoordinate

end

-- Solutions.RAM_Lax109476Proofs_RamShapeUpdate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamShapeUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface
open RamShapeCoordinate RamZeroArray RamMatrixStorage







def shapeStep : Com := .seq shapeCoordinate (.assign "entry.k" (.add (.var "entry.k") (.lit 1)))



def shapeLoop : Com :=
  .seq (.assign "entry.count" (.mul (.var "vec.n") (.var "vec.n")))
    (.seq (.assign "entry.k" (.lit 0)) (.while (.lt (.var "entry.k") (.var "entry.count")) shapeStep))





def initializeShape : Com :=
  .seq (.assign "shape.savedn" (.var "vec.n"))
    (.seq (.assign "vec.n" (.mul (.var "vec.n") (.var "vec.n")))
      (.seq (zeroRationalArray "ell.nextshape") (.assign "vec.n" (.var "shape.savedn"))))



def updateShape : Com := .seq initializeShape shapeLoop













end Lax109476Proofs.RamShapeUpdate

end

-- Solutions.RAM_Lax109476Proofs_RamMatrixVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamMatrixVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamDotProduct RamMatrixRows

def storeDotAtRow (a : String) : Com :=
  .seq (.assign "rat.s" (.var "dot.s"))
    (.seq (.assign "rat.n" (.var "dot.n"))
      (.seq (.assign "rat.d" (.var "dot.d"))
        (.seq (.assign "vec.i" (.var "row.i")) (storeReduced a))))













def matrixVectorStep : Com :=
  .seq (matrixRowDot "ell.shape" "ell.normal")
    (.seq (storeDotAtRow "ell.u") (.assign "row.i" (.add (.var "row.i") (.lit 1))))





def ellipsoidMulVec : Com :=
  .seq (.assign "row.m" (.var "vec.n"))
    (.seq (.assign "row.i" (.lit 0))
      (.while (.lt (.var "row.i") (.var "row.m")) matrixVectorStep))



def ellipsoidMulVecInitialized : Com := .seq (RamZeroArray.zeroRationalArray "ell.u") ellipsoidMulVec







end Lax109476Proofs.RamMatrixVector

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidForm
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamDotProduct RamMatrixRows RamMatrixVector




def saveForm : Com :=
  .seq (.assign "ell.form.s" (.var "dot.s"))
    (.seq (.assign "ell.form.n" (.var "dot.n")) (.assign "ell.form.d" (.var "dot.d")))









def ellipsoidForm : Com :=
  .seq ellipsoidMulVecInitialized (.seq (RamDotProduct.dotProduct "ell.normal" "ell.u") saveForm)





end Lax109476Proofs.RamEllipsoidForm

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidScalars
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEllipsoidScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamEllipsoidForm RationalSizeBounds
open RamRounding

def alphaFraction : Com :=
  .seq (.assign "rat.s" (.lit 0))
    (.seq (.assign "rat.n" (.mul (.var "vec.n") (.var "vec.n")))
      (.seq (.assign "rat.d" (.sub (.var "rat.n") (.lit 1))) normalizeFraction))





def epsilonDenominator : Com :=
  .assign "ell.epsden" (.shiftl (.lit 1) (.add (.mul (.lit 2) (.var "vec.n")) (.lit 4)))



def inflationFraction : Com :=
  .seq (.assign "infl.a" (.add (.var "ell.epsden") (.lit 1)))
    (.seq (.assign "rat.s" (.lit 0))
      (.seq (.assign "rat.n" (.mul (.var "infl.a") (.var "infl.a")))
        (.seq (.assign "rat.d" (.mul (.var "ell.epsden") (.var "ell.epsden"))) normalizeFraction)))





def precisionGrid : Com :=
  .assign "grid.D" (.shiftl (.lit 1)
    (.add (.add (.mul (.lit 2) (.var "iter.k")) (.mul (.lit 3) (.var "vec.n"))) (.lit 9)))







def betaFraction : Com :=
  .seq (.assign "rat.s" (.lit 0))
    (.seq (.assign "rat.n" (.mul (.lit 2) (.var "ell.form.d")))
      (.seq (.assign "beta.nplus" (.add (.var "vec.n") (.lit 1)))
        (.seq (.assign "rat.d" (.mul (.var "beta.nplus") (.var "ell.form.n"))) normalizeFraction)))





def scaledInverseFraction : Com :=
  .seq (.assign "gamma.rootn" (.var "rat.n"))
    (.seq (.assign "gamma.nplus" (.add (.var "vec.n") (.lit 1)))
      (.seq (.assign "rat.n" (.var "rat.d"))
        (.seq (.assign "rat.d" (.mul (.var "gamma.nplus") (.var "gamma.rootn")))
          (.seq (.assign "rat.s" (.lit 0)) normalizeFraction))))







def gammaFraction : Com :=
  .seq (.assign "left.s" (.var "ell.form.s"))
    (.seq (.assign "left.n" (.var "ell.form.n"))
      (.seq (.assign "left.d" (.var "ell.form.d"))
        (.seq upperRootFraction scaledInverseFraction)))





def diagonalFraction : Com :=
  .seq (.assign "rat.s" (.lit 0))
    (.seq (.assign "rat.n" (.var "vec.n")) (.seq (.assign "rat.d" (.var "grid.D")) normalizeFraction))



end Lax109476Proofs.RamEllipsoidScalars

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidCoefficients
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamEllipsoidScalars RamEllipsoidForm




def storeCoefficient (i : ℕ) : Com :=
  .seq (.assign "vec.i" (.lit i)) (storeReduced "ell.coeff")





def computeAndStore (c : Com) (i : ℕ) : Com := .seq c (storeCoefficient i)





def computeCoefficients : Com :=
  .seq (computeAndStore alphaFraction 0)
    (.seq (computeAndStore betaFraction 1)
      (.seq (computeAndStore gammaFraction 2)
        (.seq (computeAndStore inflationFraction 3) (computeAndStore diagonalFraction 4))))





















def initializeCoefficients : Com :=
  .seq (.assign "coeff.savedn" (.var "vec.n"))
    (.seq (.assign "vec.n" (.lit 5))
      (.seq (RamZeroArray.zeroRationalArray "ell.coeff") (.assign "vec.n" (.var "coeff.savedn"))))



def prepareCoefficients : Com := .seq initializeCoefficients computeCoefficients



end Lax109476Proofs.RamEllipsoidCoefficients

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidUpdate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays
open RamCenterCoordinate RamCenterUpdate RamShapeCoordinate RamShapeUpdate
open RamEllipsoidCoefficients RamMatrixStorage







def roundedUpdate : Com := .seq updateCenter updateShape











end Lax109476Proofs.RamEllipsoidUpdate

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidPrecision
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEllipsoidPrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEllipsoidScalars

def preparePrecision : Com := .seq epsilonDenominator precisionGrid





end Lax109476Proofs.RamEllipsoidPrecision

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidStep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamEllipsoidStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays
open RamEllipsoidUpdate RamEllipsoidPrecision RamEllipsoidCoefficients
open RamEllipsoidScalars RamEllipsoidForm RamMatrixVector RamMatrixRows RamDotProduct RamMatrixStorage

/-- Three equal extents for the sign, numerator, and denominator arrays. -/
def Extents (a : String) (n : ℕ) (σ : Env) : Prop :=
  ∀ s ∈ [".s", ".n", ".d"], (σ.arrs (a ++ s)).length = n

def Workspace (n : ℕ) (σ : Env) : Prop :=
  Extents "ell.u" n σ ∧ Extents "ell.coeff" 5 σ ∧
    Extents "ell.nextcenter" n σ ∧ Extents "ell.nextshape" (n * n) σ

















def ellipsoidStep : Com :=
  .seq ellipsoidForm (.seq preparePrecision (.seq prepareCoefficients roundedUpdate))














 

end Lax109476Proofs.RamEllipsoidStep

end

-- Solutions.RAM_Lax109476Proofs_RamCommitState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamCommitState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamCopy RamMatrixStorage RamEllipsoidStep

/-- Restore the logical dimension after copying the flattened shape. -/
def commitShape : Com :=
  .seq (.assign "state.savedn" (.var "vec.n"))
    (.seq (.assign "vec.n" (.mul (.var "vec.n") (.var "vec.n")))
      (.seq (copyRationalArray "ell.nextshape" "ell.shape") (.assign "vec.n" (.var "state.savedn"))))



def commitState : Com := .seq (copyRationalArray "ell.nextcenter" "ell.center") commitShape







end Lax109476Proofs.RamCommitState

end

-- Solutions.RAM_Lax109476Proofs_RamAdvanceState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators Matrix

namespace Lax109476Proofs.RamAdvanceState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCommitState
open RamEllipsoidCoefficients RamMatrixStorage









/-- A complete central cut, installation of the next state, and counter advance. -/
def advanceState : Com := .seq ellipsoidStep
  (.seq commitState (.assign "iter.k" (.add (.var "iter.k") (.lit 1))))




end Lax109476Proofs.RamAdvanceState

end

-- Solutions.RAM_Lax109476Proofs_RamReadBody
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadBody

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBlock RamRationalArrays RamEllipsoidStep RamAdvanceState

/-- Unconsumed words make the input malformed; a prior failure stays recorded. -/
def finishInput : Com := .ite (.eq (.var "input.remaining") (.lit 0)) .skip
  (.assign "input.valid" (.lit 0))



def readBody : Com := .seq (readBlock "lp.A" "decode.count")
  (.seq (readBlock "lp.b" "lp.m") (.seq (readBlock "lp.c" "lp.n") finishInput))


















end Lax109476Proofs.RamReadBody

end

-- Solutions.RAM_Lax109476Proofs_RamRationalHalf
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalHalf

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamArithmetic

def half : Com := .seq (.assign "rat.s" (.var "left.s"))
  (.seq (.assign "rat.n" (.var "left.n"))
    (.seq (.assign "rat.d" (.mul (.var "left.d") (.lit 2))) normalizeFraction))





end Lax109476Proofs.RamRationalHalf

end

-- Solutions.RAM_Lax109476Proofs_RamRationalMidpoint
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalMidpoint

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def midpoint : Com := .seq (readLeft "bisect.lo") (.seq (readRight "bisect.hi")
  (.seq addFraction (.seq resultToLeft (.seq RamRationalHalf.half (save "bisect.mid")))))



end Lax109476Proofs.RamRationalMidpoint

end

-- Solutions.RAM_Lax109476Proofs_RamBisectionCommit
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamBisectionCommit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def condition : Cond := .eq (.var "search.found") (.lit 1)

def commit : Com := .ite condition (RamScalarCopy.copy "bisect.mid" "bisect.hi")
  (RamScalarCopy.copy "bisect.mid" "bisect.lo")



end Lax109476Proofs.RamBisectionCommit

end

-- Solutions.RAM_Lax109476Proofs_RamBisectionLoop
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars
open RamBisectionCommit





def increment : Com := .assign "bisect.i" (.add (.var "bisect.i") (.lit 1))

def body (query : Com) : Com := .seq RamRationalMidpoint.midpoint (.seq query (.seq commit increment))





def loop (query : Com) : Com := .seq (.assign "bisect.i" (.lit 0))
  (.while (.lt (.var "bisect.i") (.var "bisect.limit")) (body query))



end Lax109476Proofs.RamBisectionLoop

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateSource
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateSource

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding




def Data {m n : ℕ} (P : Program ℤ m n) (σ : Env) : Prop :=
  Represents "source.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "source.b" (List.ofFn (rationalProgram P).b) σ ∧
    Represents "source.c" (List.ofFn (rationalProgram P).c) σ ∧
    σ.vars "source.m" = m ∧ σ.vars "source.n" = n







end Lax109476Proofs.RamCertificateSource

end

-- Solutions.RAM_Lax109476Proofs_RamBuildVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamBuildVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCenterUpdate RamEllipsoidStep

def coordinate (a : String) (selector : Com) : Com := .seq selector
  (.seq (.assign "vec.i" (.var "build.i")) (storeReduced a))

def step (a : String) (selector : Com) : Com := .seq (coordinate a selector)
  (.assign "build.i" (.add (.var "build.i") (.lit 1)))





def loop (a : String) (selector : Com) : Com := .seq (.assign "build.i" (.lit 0))
  (.while (.lt (.var "build.i") (.var "build.count")) (step a selector))



def build (a : String) (selector : Com) : Com := .seq (.assign "vec.n" (.var "build.count"))
  (.seq (RamZeroArray.zeroRationalArray a) (loop a selector))



end Lax109476Proofs.RamBuildVector

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays IntegerEncoding RamEllipsoidStep




def selectCoordinate (selector : Com) : Com := .seq
  (.assign "query.row" (.div (.var "build.i") (.var "system.n")))
  (.seq (.assign "query.col" (.sub (.var "build.i")
    (.mul (.var "query.row") (.var "system.n")))) selector)



def prepare : Com := .assign "build.count" (.mul (.var "system.m") (.var "system.n"))
def matrix (selector : Com) : Com := .seq prepare (RamBuildVector.build "system.A" (selectCoordinate selector))



end Lax109476Proofs.RamCertificateMatrix

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays IntegerEncoding RamEllipsoidStep


def selectCoordinate (selector : Com) : Com := .seq (.assign "query.row" (.var "build.i")) selector



def prepare : Com := .assign "build.count" (.var "system.m")
def buildBound (selector : Com) : Com := .seq prepare (RamBuildVector.build "system.b" (selectCoordinate selector))



end Lax109476Proofs.RamCertificateBound

end

-- Solutions.RAM_Lax109476Proofs_RamPadSelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage

def constantFraction (v : ℕ) : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit v)) (.assign "rat.d" (.lit 1)))



def selectEntry : Com := .ite (.lt (.var "pad.row") (.var "source.m"))
  (.ite (.lt (.var "pad.col") (.var "source.n"))
    (.seq (.assign "vec.i" (.add (.mul (.var "pad.row") (.var "source.n")) (.var "pad.col")))
      (.seq (loadLeft "query.A") RamCopy.leftToResult)) (constantFraction 0))
  (.ite (.lt (.var "pad.col") (.var "source.n")) (constantFraction 0)
    (.ite (.eq (.sub (.var "pad.row") (.var "source.m"))
      (.sub (.var "pad.col") (.var "source.n"))) (constantFraction 1) (constantFraction 0)))





end Lax109476Proofs.RamPadSelector

end

-- Solutions.RAM_Lax109476Proofs_RamRecoverySelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoverySelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage

def negativeOne : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 1)))



def selectEntry : Com := .ite (.lt (.var "query.row") (.var "point.m"))
  (.seq (.assign "vec.i" (.add (.mul (.var "query.row") (.var "point.n")) (.var "query.col")))
    (.seq (loadLeft "point.A") RamCopy.leftToResult))
  (.ite (.lt (.var "query.row") (.add (.var "point.m") (.var "point.n")))
    (.ite (.lt (.sub (.var "query.row") (.var "point.m")) (.var "point.k"))
      (.ite (.eq (.var "query.col") (.sub (.var "query.row") (.var "point.m")))
        (RamPadSelector.constantFraction 1) (RamPadSelector.constantFraction 0))
      (RamPadSelector.constantFraction 0))
    (.ite (.lt (.var "query.row") (.add (.add (.var "point.m") (.var "point.n")) (.var "point.n")))
      (.ite (.lt (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")) (.var "point.k"))
        (.ite (.eq (.var "query.col") (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")))
          negativeOne (RamPadSelector.constantFraction 0))
        (RamPadSelector.constantFraction 0))
      (.ite (.eq (.var "query.col") (.var "point.k"))
        (RamPadSelector.constantFraction 1) (RamPadSelector.constantFraction 0))))





end Lax109476Proofs.RamRecoverySelector

end

-- Solutions.RAM_Lax109476Proofs_RamResultNegation
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamResultNegation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface

def negateResult : Com := .assign "rat.s" (.sub (.lit 1) (.var "rat.s"))



end Lax109476Proofs.RamResultNegation

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryBoundSelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryBoundSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars

def selectBound : Com := .ite (.lt (.var "query.row") (.var "point.m"))
  (.seq (.assign "vec.i" (.var "query.row")) (RamArrayResult.load "point.b"))
  (.ite (.lt (.var "query.row") (.add (.var "point.m") (.var "point.n")))
    (.ite (.lt (.sub (.var "query.row") (.var "point.m")) (.var "point.k"))
      (.seq (.assign "vec.i" (.sub (.var "query.row") (.var "point.m"))) (RamArrayResult.load "point.x"))
      (RamPadSelector.constantFraction 0))
    (.ite (.lt (.var "query.row") (.add (.add (.var "point.m") (.var "point.n")) (.var "point.n")))
      (.ite (.lt (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")) (.var "point.k"))
        (.seq (.assign "vec.i" (.sub (.sub (.var "query.row") (.var "point.m")) (.var "point.n")))
          (.seq (RamArrayResult.load "point.x") RamResultNegation.negateResult))
        (RamPadSelector.constantFraction 0))
      (RamScalarCopy.copy "bisect.mid" "rat")))





end Lax109476Proofs.RamRecoveryBoundSelector

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage
open RamEllipsoidStep



def selectCoordinate : Com := .seq (.assign "query.row" (.div (.var "build.i") (.var "point.n")))
  (.seq (.assign "query.col" (.sub (.var "build.i") (.mul (.var "query.row") (.var "point.n"))))
    RamRecoverySelector.selectEntry)



def prepare : Com := .assign "build.count"
    (.mul (.add (.add (.var "point.m") (.add (.var "point.n") (.var "point.n"))) (.lit 1)) (.var "point.n"))

def matrix : Com := .seq prepare (RamBuildVector.build "lp.A" selectCoordinate)



end Lax109476Proofs.RamRecoveryMatrix

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays
open RamEllipsoidStep



def selectCoordinate : Com := .seq (.assign "query.row" (.var "build.i")) RamRecoveryBoundSelector.selectBound



def prepare : Com := .assign "build.count"
    (.add (.add (.var "point.m") (.add (.var "point.n") (.var "point.n"))) (.lit 1))

def buildBound : Com := .seq prepare (RamBuildVector.build "lp.b" selectCoordinate)



end Lax109476Proofs.RamRecoveryBound

end

-- Solutions.RAM_Lax109476Proofs_RamStoredProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamStoredProgram

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamReadBlock

def RepresentsProgram {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "lp.A" (RamMatrixStorage.flatten P.A) σ ∧
    Represents "lp.b" (List.ofFn P.b) σ ∧ Represents "lp.c" (List.ofFn P.c) σ ∧
    σ.vars "lp.m" = m ∧ σ.vars "lp.n" = n ∧ σ.vars "decode.count" = m * n



end Lax109476Proofs.RamStoredProgram

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryQuery
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamStoredProgram

def objective : Com := .seq (.assign "vec.n" (.var "point.n"))
  (RamZeroArray.zeroRationalArray "lp.c")

def metadata : Com := .seq
  (.assign "lp.m" (.add (.add (.var "point.m") (.add (.var "point.n") (.var "point.n"))) (.lit 1)))
  (.seq (.assign "lp.n" (.var "point.n"))
    (.assign "decode.count" (.mul (.var "lp.m") (.var "lp.n"))))

/-- Build one coordinate threshold query from the immutable point-recovery
system and its already recovered prefix. The command is independent of the
dimensions, prefix length, and rational threshold. -/
def buildQuery : Com := .seq RamRecoveryMatrix.matrix
  (.seq RamRecoveryBound.buildBound (.seq objective metadata))

def Extent (m n : ℕ) (σ : Env) : Prop :=
  Extents "lp.A" (((m + (n + n)) + 1) * n) σ ∧
    Extents "lp.b" ((m + (n + n)) + 1) σ ∧ Extents "lp.c" n σ









end Lax109476Proofs.RamRecoveryQuery

end

-- Solutions.RAM_Lax109476Proofs_RamCopyBlock
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCopyBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCopy RamRationalArrays RamEllipsoidStep

def copyBlock (a b field : String) : Com :=
  .seq (.assign "vec.n" (.var field)) (copyRationalArray a b)







end Lax109476Proofs.RamCopyBlock

end

-- Solutions.RAM_Lax109476Proofs_RamScaleCoordinate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamScaleCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RamCopy

def prepareFactor : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "scale.factor")) (.assign "right.d" (.lit 1)))





def scaleCoordinate (a b : String) : Com := .seq (.assign "vec.i" (.var "scale.i"))
  (.seq (loadLeft a) (.seq prepareFactor (.seq RamRational.multiplyFraction (storeReduced b))))



end Lax109476Proofs.RamScaleCoordinate

end

-- Solutions.RAM_Lax109476Proofs_RamNormalizedEntry
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalizedEntry

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface
open RamMatrixStorage IntegerEncoding RamScaleCoordinate







def negativeFactor : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.var "cap.R")) (.assign "rat.d" (.lit 1)))



def selectEntry : Com := .ite (.lt (.var "norm.row") (.var "query.m"))
  (.seq (.assign "vec.i" (.add (.mul (.var "norm.row") (.var "query.n")) (.var "norm.col")))
    (.seq (loadLeft "pad.A") (.seq (.assign "scale.factor" (.var "cap.R"))
      (.seq prepareFactor RamRational.multiplyFraction))))
  (.ite (.eq (.sub (.var "norm.row") (.var "query.m")) (.var "norm.col"))
    negativeFactor (RamPadSelector.constantFraction 0))





end Lax109476Proofs.RamNormalizedEntry

end

-- Solutions.RAM_Lax109476Proofs_RamNormalizedMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalizedMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage RamNormalizedEntry
open RamCenterUpdate RamEllipsoidStep IntegerEncoding







def normalizeCoordinate : Com := .seq
  (.assign "norm.row" (.div (.var "norm.k") (.var "query.n")))
  (.seq (.assign "norm.col" (.sub (.var "norm.k")
    (.mul (.var "norm.row") (.var "query.n"))))
    (.seq RamNormalizedEntry.selectEntry
      (.seq (.assign "vec.i" (.var "norm.k")) (storeReduced "search.rows"))))





def normalizeStep : Com := .seq normalizeCoordinate (.assign "norm.k" (.add (.var "norm.k") (.lit 1)))



def normalizeLoop : Com := .seq (.assign "norm.k" (.lit 0))
  (.while (.lt (.var "norm.k") (.var "norm.count")) normalizeStep)



def normalizeMatrix : Com := .seq
  (.assign "norm.count" (.mul (.add (.var "query.m") (.var "query.n")) (.var "query.n")))
  (.seq (.assign "vec.n" (.var "norm.count")) (.seq (RamZeroArray.zeroRationalArray "search.rows") normalizeLoop))



end Lax109476Proofs.RamNormalizedMatrix

end

-- Solutions.RAM_Lax109476Proofs_RamNormalizedBoundEntry
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalizedBoundEntry

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface
open IntegerEncoding









def prepareEpsilon : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.lit 1)) (.assign "right.d" (.var "cap.D")))



def epsilonResult : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.var "cap.D")))



def selectBound : Com := .ite (.lt (.var "norm.k") (.var "query.m"))
  (.seq (.assign "vec.i" (.var "norm.k"))
    (.seq (loadLeft "pad.b") (.seq prepareEpsilon RamRational.addFraction))) epsilonResult





end Lax109476Proofs.RamNormalizedBoundEntry

end

-- Solutions.RAM_Lax109476Proofs_RamNormalizedBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalizedBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage RamNormalizedBoundEntry
open RamCenterUpdate RamEllipsoidStep IntegerEncoding







def normalizeCoordinate : Com := .seq RamNormalizedBoundEntry.selectBound
  (.seq (.assign "vec.i" (.var "norm.k")) (storeReduced "search.rhs"))





def normalizeStep : Com := .seq normalizeCoordinate (.assign "norm.k" (.add (.var "norm.k") (.lit 1)))



def normalizeLoop : Com := .seq (.assign "norm.k" (.lit 0))
  (.while (.lt (.var "norm.k") (.var "norm.count")) normalizeStep)



def normalizeBound : Com := .seq
  (.assign "norm.count" (.add (.var "query.m") (.var "query.n")))
  (.seq (.assign "vec.n" (.var "norm.count")) (.seq (RamZeroArray.zeroRationalArray "search.rhs") normalizeLoop))



end Lax109476Proofs.RamNormalizedBound

end

-- Solutions.RAM_Lax109476Proofs_RamNonzero
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNonzero

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays









def scanStep (a : String) : Com :=
  .seq (.ite (.lt (.lit 0) (.get (a ++ ".n") (.var "nonzero.i")))
    (.assign "nonzero.flag" (.lit 1)) .skip)
    (.assign "nonzero.i" (.add (.var "nonzero.i") (.lit 1)))



def scanLoop (a : String) : Com := .seq (.assign "nonzero.i" (.lit 0))
  (.while (.lt (.var "nonzero.i") (.var "vec.n")) (scanStep a))

def scan (a : String) : Com := .seq (.assign "nonzero.flag" (.lit 0)) (scanLoop a)



end Lax109476Proofs.RamNonzero

end

-- Solutions.RAM_Lax109476Proofs_RamRowCopy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRowCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixRows
open RamCopy RamCenterUpdate RamZeroArray



def copyCoordinate (a b : String) : Com := .seq (.assign "vec.i" (.var "copy.i"))
  (.seq (loadRowLeft a) (.seq leftToResult (storeReduced b)))





def copyStep (a b : String) : Com := .seq (copyCoordinate a b)
  (.assign "copy.i" (.add (.var "copy.i") (.lit 1)))



def copyLoop (a b : String) : Com := .seq (.assign "copy.i" (.lit 0))
  (.while (.lt (.var "copy.i") (.var "vec.n")) (copyStep a b))



def copyRow (a b : String) : Com := .seq (zeroRationalArray b) (copyLoop a b)



end Lax109476Proofs.RamRowCopy

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidBitBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEllipsoidBitBounds

open RamDotProduct RamEllipsoidForm RamEllipsoidStep RamEllipsoidCoefficients
open RamShapeCoordinate RamShapeUpdate RationalSizeBounds

def formExponent (n h : ℕ) : ℕ := (2 * ((2 * h + 1) * (n + 1)) + 1) * (n + 1)

/-- A polynomial exponent bounds the full quadratic form and both precision denominators. -/
def magnitudeExponent (n h k : ℕ) : ℕ := formExponent n h + n * n + 2 * k + 5 * n + 13

def wordWidth (n h k : ℕ) : ℕ := 64 * magnitudeExponent n h k + 224













end Lax109476Proofs.RamEllipsoidBitBounds

end

-- Solutions.RAM_Lax109476Proofs_RamTrajectoryBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix BigOperators

namespace Lax109476Proofs.RamTrajectoryBounds

open Lax759944.BinaryWordEncoding Lax109476.RationalEncoding Lax109476.RationalCertificates
open EncodingSize
open RamEllipsoidBitBounds RamEllipsoidStep RamAdvanceState RamRationalArrays RamMatrixStorage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def stateBits (n K l : ℕ) : ℕ := 60 + 6 * K + 14 * n + l

def instructionBound (n K l : ℕ) : ℕ :=
  let h := stateBits n K l
  let e := magnitudeExponent n h K
  (144 * ((n + 1) * (2 * (h + 1) + 3) + 1) + 220) * n ^ 2 +
    (144 * ((n + 1) * (2 * ((n + 1) * (2 * (h + 1) + 3) + 1) + 3) + 1) + 292) * n +
    (2880 * (e + 1) + 7559) * n + (14976 * (e + 1) + 36767) * (n * n) +
    582 * (e + 1) + 1060 + 71 * n + 71 * (n * n)















end Lax109476Proofs.RamTrajectoryBounds

end

-- Solutions.RAM_Lax109476Proofs_RamNormalSelection
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalSelection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamZeroArray
open RamEllipsoidStep RamAdvanceState RamMatrixRows

def fallbackNormal : Com := .seq (zeroRationalArray "ell.normal")
  (.seq (.assign "vec.i" (.lit 0))
    (.seq (.assign "rat.s" (.lit 0)) (.seq (.assign "rat.n" (.lit 1))
      (.seq (.assign "rat.d" (.lit 1)) (storeReduced "ell.normal")))))





def copySelectedRow (a : String) : Com :=
  .seq (.assign "row.base" (.mul (.var "row.first") (.var "vec.n")))
    (RamRowCopy.copyRow a "ell.normal")



def ensureNormal : Com := .seq (RamNonzero.scan "ell.normal")
  (.ite (.eq (.var "nonzero.flag") (.lit 0)) fallbackNormal .skip)



def selectNormal (a : String) : Com :=
  .ite (.lt (.var "row.first") (.var "row.m"))
    (.seq (copySelectedRow a) ensureNormal) fallbackNormal




end Lax109476Proofs.RamNormalSelection

end

-- Solutions.RAM_Lax109476Proofs_RamSeparation
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamSeparation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamDotProduct RamMatrixRows RamComparison

/-- Compare the accumulated row value with the stored right-hand side. -/
def compareRowRhs (a : String) : Com :=
  .seq (.assign "left.s" (.var "dot.s"))
    (.seq (.assign "left.n" (.var "dot.n"))
      (.seq (.assign "left.d" (.var "dot.d"))
        (.seq (.assign "vec.i" (.var "row.i"))
          (.seq (loadRight a) (.seq compareFraction (.assign "vec.i" (.var "vec.n")))))))




def evaluateRow (a point rhs : String) : Com :=
  .seq (matrixRowDot a point) (compareRowRhs rhs)



















def recordViolation : Com :=
  .seq (.ite (.eq (.var "cmp.le") (.lit 0))
    (.ite (.eq (.var "row.first") (.var "row.m"))
      (.assign "row.first" (.var "row.i")) .skip) .skip)
    (.assign "row.i" (.add (.var "row.i") (.lit 1)))




def scanStep (a point rhs : String) : Com := .seq (evaluateRow a point rhs) recordViolation







def separateRows (a point rhs : String) : Com :=
  .seq (.assign "row.first" (.var "row.m"))
    (.seq (.assign "row.i" (.lit 0))
      (.while (.lt (.var "row.i") (.var "row.m")) (scanStep a point rhs)))









end Lax109476Proofs.RamSeparation

end

-- Solutions.RAM_Lax109476Proofs_RamSearchStep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows RamSeparation RamNormalSelection RamTrajectoryBounds
open RamEllipsoidStep RamEllipsoidBitBounds RamAdvanceState



def advanceKeepingRows : Com := .seq (.assign "search.savedm" (.var "row.m"))
  (.seq advanceState (.assign "row.m" (.var "search.savedm")))

def cutOrFinish : Com := .ite (.lt (.var "row.first") (.var "row.m"))
  (.seq (selectNormal "search.rows") advanceKeepingRows)
  (.seq (.assign "search.found" (.lit 1)) (.assign "search.limit" (.var "iter.k")))

def searchStep : Com := .seq (separateRows "search.rows" "ell.center" "search.rhs") cutOrFinish





-- The iteration-loop proof will use this fixed body and a variant
-- `search.limit - iter.k`; success lowers the limit to the current index.




end Lax109476Proofs.RamSearchStep

end

-- Solutions.RAM_Lax109476Proofs_RamInitialState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix

namespace Lax109476Proofs.RamInitialState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamZeroArray RamMatrixStorage RamCenterUpdate





def identityCoordinate : Com :=
  .seq (.assign "vec.i" (.var "init.k"))
    (.seq (.assign "init.row" (.div (.var "init.k") (.var "vec.n")))
      (.seq (.assign "init.col" (.sub (.var "init.k") (.mul (.var "init.row") (.var "vec.n"))))
        (.seq (.assign "rat.s" (.lit 0))
          (.seq (.assign "rat.d" (.lit 1))
            (.seq (.ite (.eq (.var "init.row") (.var "init.col"))
              (.assign "rat.n" (.lit 1)) (.assign "rat.n" (.lit 0))) (storeReduced "ell.shape"))))))





def identityStep : Com := .seq identityCoordinate (.assign "init.k" (.add (.var "init.k") (.lit 1)))



def identityLoop : Com := .seq (.assign "init.count" (.mul (.var "vec.n") (.var "vec.n")))
  (.seq (.assign "init.k" (.lit 0)) (.while (.lt (.var "init.k") (.var "init.count")) identityStep))





def initializeIdentity : Com := .seq (.assign "init.savedn" (.var "vec.n"))
  (.seq (.assign "vec.n" (.mul (.var "vec.n") (.var "vec.n")))
    (.seq (zeroRationalArray "ell.shape")
      (.seq (.assign "vec.n" (.var "init.savedn")) identityLoop)))



def initialState : Com := .seq (zeroRationalArray "ell.center")
  (.seq initializeIdentity (.assign "iter.k" (.lit 0)))



end Lax109476Proofs.RamInitialState

end

-- Solutions.RAM_Lax109476Proofs_RamSearchLoop
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSearchStep



def searchLoop : Com := .while (.lt (.var "iter.k") (.var "search.limit")) searchStep







def search : Com := .seq (.assign "search.limit" (.var "search.budget"))
  (.seq (.assign "search.found" (.lit 0)) (.seq RamInitialState.initialState searchLoop))




end Lax109476Proofs.RamSearchLoop

end

-- Solutions.RAM_Lax109476Proofs_RamSearchBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSearchBounds

open RamTrajectoryBounds RamEllipsoidBitBounds RamEllipsoidStep
open RamDotProduct RamEllipsoidForm

def wordWidth (m n N l : ℕ) : ℕ :=
  RamEllipsoidBitBounds.wordWidth n (stateBits n N l) N + m + n + m * n + N + 2



def rowBound (n N l : ℕ) : ℕ :=
  (144 * ((n + 1) * (2 * (stateBits n N l + 1) + 3) + 1) + 220) * n + 95

def stepBound (m n N l : ℕ) : ℕ := rowBound n N l * m + 126 * n + instructionBound n N l + 103

def instructionBound (m n N l : ℕ) : ℕ :=
  33 * n + 76 * (n * n) + (stepBound m n N l + 4) * N + 64





open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamMatrixRows RamRationalArrays RamEllipsoidStep





end Lax109476Proofs.RamSearchBounds

end

-- Solutions.RAM_Lax109476Proofs_RamNormalizeQuery
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalizeQuery

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding

def normalizeQuery : Com := .seq RamNormalizedMatrix.normalizeMatrix
  (.seq RamNormalizedBound.normalizeBound (.seq (.assign "vec.n" (.var "query.n"))
    (.assign "row.m" (.add (.var "query.m") (.var "query.n")))))





end Lax109476Proofs.RamNormalizeQuery

end

-- Solutions.RAM_Lax109476Proofs_RamBitLength
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamBitLength

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning



def bitLengthStep : Com :=
  .seq (.assign "bits.v" (.div (.var "bits.v") (.lit 2)))
    (.assign "bits.k" (.add (.var "bits.k") (.lit 1)))

def bitLengthLoop : Com := .while (.lt (.lit 0) (.var "bits.v")) bitLengthStep

def bitLength : Com :=
  .seq (.assign "bits.k" (.lit 0)) bitLengthLoop







end Lax109476Proofs.RamBitLength

end

-- Solutions.RAM_Lax109476Proofs_RamNaturalPower
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning



def powerStep : Com := .seq
  (.assign "power.value" (.mul (.var "power.value") (.var "power.base")))
  (.assign "power.i" (.add (.var "power.i") (.lit 1)))



def power : Com := .seq (.assign "power.value" (.lit 1))
  (.seq (.assign "power.i" (.lit 0))
    (.while (.lt (.var "power.i") (.var "power.exponent")) powerStep))





def factorialStep : Com := .seq
  (.assign "factorial.i" (.add (.var "factorial.i") (.lit 1)))
  (.assign "factorial.value" (.mul (.var "factorial.value") (.var "factorial.i")))



def factorial : Com := .seq (.assign "factorial.value" (.lit 1))
  (.seq (.assign "factorial.i" (.lit 0))
    (.while (.lt (.var "factorial.i") (.var "factorial.n")) factorialStep))



end Lax109476Proofs.RamNaturalPower

end

-- Solutions.RAM_Lax109476Proofs_RamCoordinateCap
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCoordinateCap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamNaturalPower



def prepareCap : Com := .seq
  (.assign "cap.k" (.add (.mul (.lit 2) (.add (.var "query.m") (.var "query.n"))) (.lit 2)))
  (.seq (.assign "factorial.n" (.var "cap.k"))
    (.seq factorial (.seq (.assign "cap.factorial" (.var "factorial.value"))
      (.seq (.assign "power.base" (.add (.mul (.mul (.var "cap.k") (.var "cap.H"))
        (.var "cap.H")) (.lit 1)))
        (.seq (.assign "power.exponent" (.var "cap.k"))
          (.seq power (.assign "cap.value" (.mul (.var "cap.factorial") (.var "power.value")))))))))



end Lax109476Proofs.RamCoordinateCap

end

-- Solutions.RAM_Lax109476Proofs_RamCoordinateCapBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCoordinateCapBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RationalSizeBounds RamCoordinateCap



def wordWidth (S : ℕ) : ℕ := 32 * (S + 1) ^ 2 + S + 16





end Lax109476Proofs.RamCoordinateCapBounds

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilityScales
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilityScales

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamBitLength



def prepareScales : Com := .seq
  (.assign "cap.G" (.add (.mul (.var "query.m") (.var "cap.value"))
    (.mul (.mul (.mul (.var "query.n") (.var "query.m")) (.var "cap.H")) (.var "cap.value"))))
  (.seq (.assign "cap.D" (.mul (.lit 2) (.add (.var "cap.G") (.lit 1))))
    (.seq (.assign "cap.R" (.mul (.mul (.lit 4) (.add (.var "query.n") (.lit 1)))
      (.add (.var "cap.value") (.lit 1))))
      (.seq (.assign "cap.ball" (.mul (.mul (.var "cap.D")
        (.add (.mul (.var "query.n") (.var "cap.H")) (.lit 1))) (.var "cap.R")))
        (.seq (.assign "bits.v" (.var "cap.ball"))
          (.seq bitLength (.seq (.assign "cap.E" (.var "bits.k"))
            (.assign "search.budget" (.add (.mul (.mul (.lit 4) (.add (.var "query.n") (.lit 1)))
              (.add (.mul (.var "cap.E") (.var "query.n")) (.lit 1))) (.lit 1)))))))))





end Lax109476Proofs.RamFeasibilityScales

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilityScaleBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilityScaleBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamFeasibilityScales



def wordWidth (S : ℕ) : ℕ := 4096 * (S + 1) ^ 4





end Lax109476Proofs.RamFeasibilityScaleBounds

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilityParameters
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilityParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCoordinateCap RamFeasibilityScales

def prepareParameters : Com := .seq
  (.assign "cap.H" (.shiftl (.lit 1) (.mul (.lit 2) (.var "query.bits"))))
  (.seq prepareCap prepareScales)

def instructionBound (S : ℕ) : ℕ := 1536 * (S + 1) ^ 2 + 48 * S + 158



end Lax109476Proofs.RamFeasibilityParameters

end

-- Solutions.RAM_Lax109476Proofs_RamNormalizedBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamNormalizedBounds

open Lax109476.LinearProgram




def coefficientBits (S : ℕ) : ℕ := 128 * (S + 1) ^ 2 + 2 * S + 2



end Lax109476Proofs.RamNormalizedBounds

end

-- Solutions.RAM_Lax109476Proofs_RamReadHeader
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReadHeader

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput

def rejectDimensions : Com := .seq (.assign "input.valid" (.lit 0))
  (.assign "decode.count" (.lit 0))

/-- Dimensions are tested against the actual payload length before any
matrix count is computed or array loop is entered. -/
def validateDimensions : Com := .seq
  (.assign "decode.bound" (.add (.var "input.remaining") (.lit 2)))
  (.ite (.lt (.var "lp.m") (.var "decode.bound"))
    (.ite (.lt (.var "lp.n") (.var "decode.bound"))
      (.assign "decode.count" (.mul (.var "lp.m") (.var "lp.n"))) rejectDimensions)
    rejectDimensions)



def readHeader : Com := .seq (safeRead "lp.m")
  (.seq (safeRead "lp.n") validateDimensions)


def ValidDimensions (xs : List ℕ) : Prop :=
  xs.headD 0 ≤ (xs.drop 2).length + 1 ∧ xs.tail.headD 0 ≤ (xs.drop 2).length + 1

instance (xs : List ℕ) : Decidable (ValidDimensions xs) := by unfold ValidDimensions; infer_instance



end Lax109476Proofs.RamReadHeader

end

-- Solutions.RAM_Lax109476Proofs_RamDecoder
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamDecoder

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamInput RamReadHeader RamReadBody RamRationalArrays RamEllipsoidStep RamAdvanceState

/-- One input-independent command reads the physical prefix and LP payload.
The matrix loops run only after the payload-length dimension checks. -/
def decode : Com := .seq startInput (.seq readHeader
  (.ite (.eq (.var "input.valid") (.lit 1)) readBody .skip))




def Input (B : ℕ) (xs : List ℕ) (σ : Env) : Prop :=
  σ.inp = xs.length :: xs ∧ σ.InpBounded B ∧
    Extents "lp.A" (if ValidDimensions xs then xs.headD 0 * xs.tail.headD 0 else 0) σ ∧
    Extents "lp.b" (if ValidDimensions xs then xs.headD 0 else 0) σ ∧
    Extents "lp.c" (if ValidDimensions xs then xs.tail.headD 0 else 0) σ



def instructionBound (S bits : ℕ) : ℕ := (36 * bits + 115) * (S ^ 2 + 4 * S + 3) + 127



def wordWidth (L : ℕ) : ℕ := 4 * (L + 2)







end Lax109476Proofs.RamDecoder

end

-- Solutions.RAM_Lax109476Proofs_RamEncodedSize
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEncodedSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RamBitLength RamRationalArrays EncodingSize

/-- Count the registered word encoding, including its separator. -/
def countWord (x : String) : Com := .seq (.assign "bits.v" (.var x))
  (.seq bitLength (.assign "size.total" (.add (.add (.var "size.total") (.var "bits.k")) (.lit 1))))



def countFraction : Com := .seq (countWord "left.s")
  (.seq (countWord "left.n") (countWord "left.d"))

















def countStep (a : String) : Com := .seq (.assign "vec.i" (.var "size.i"))
  (.seq (loadLeft a) (.seq countFraction (.assign "size.i" (.add (.var "size.i") (.lit 1)))))





def countArray (a : String) : Com := .seq (.assign "size.i" (.lit 0))
  (.while (.lt (.var "size.i") (.var "vec.n")) (countStep a))



end Lax109476Proofs.RamEncodedSize

end

-- Solutions.RAM_Lax109476Proofs_RamSizeBlock
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSizeBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEncodedSize RamRationalArrays
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding RamReadBlock



def countBlock (a field : String) : Com := .seq (.assign "vec.n" (.var field)) (countArray a)



end Lax109476Proofs.RamSizeBlock

end

-- Solutions.RAM_Lax109476Proofs_RamProgramSize
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamProgramSize

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEncodedSize RamSizeBlock RamRationalArrays RamStoredProgram RamReadBlock
open EncodingSize







def prepareSize : Com := .seq (.assign "size.total" (.lit 0))
  (.seq (countWord "lp.m") (.seq (countWord "lp.n")
    (.seq (countBlock "lp.A" "decode.count") (.seq (countBlock "lp.b" "lp.m")
      (.seq (countBlock "lp.c" "lp.n") (.assign "input.bits" (.var "size.total")))))))



end Lax109476Proofs.RamProgramSize

end

-- Solutions.RAM_Lax109476Proofs_RamDenominatorProduct
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamDenominatorProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays



















def productStep (a : String) : Com := .seq
  (.assign "den.value" (.mul (.var "den.value") (.get (a ++ ".d") (.var "den.i"))))
  (.assign "den.i" (.add (.var "den.i") (.lit 1)))



def productArray (a : String) : Com := .seq (.assign "den.i" (.lit 0))
  (.while (.lt (.var "den.i") (.var "vec.n")) (productStep a))



end Lax109476Proofs.RamDenominatorProduct

end

-- Solutions.RAM_Lax109476Proofs_RamDenominatorBlock
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamDenominatorBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamDenominatorProduct RamRationalArrays RamReadBlock



def productBlock (a field : String) : Com := .seq (.assign "vec.n" (.var field)) (productArray a)



end Lax109476Proofs.RamDenominatorBlock

end

-- Solutions.RAM_Lax109476Proofs_RamProgramDenominator
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamProgramDenominator

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamDenominatorProduct RamDenominatorBlock RamRationalArrays RamStoredProgram RamReadBlock
open IntegerEncoding RationalSizeBounds EncodingSize





def prepareDenominator : Com := .seq (.assign "den.value" (.lit 1))
  (.seq (productBlock "lp.A" "decode.count")
    (.seq (productBlock "lp.b" "lp.m") (productBlock "lp.c" "lp.n")))



end Lax109476Proofs.RamProgramDenominator

end

-- Solutions.RAM_Lax109476Proofs_RamSolverInitialization
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamSolverInitialization

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram EncodingSize IntegerEncoding

def initializeSolver : Com := .seq RamDecoder.decode
  (.ite (.eq (.var "input.valid") (.lit 1))
    (.seq RamProgramSize.prepareSize RamProgramDenominator.prepareDenominator) .skip)





def instructionBound (L : ℕ) : ℕ := RamDecoder.instructionBound L (L + 1) +
  (36 * (L + 1) + 61) * L + 37 * L + 86



end Lax109476Proofs.RamSolverInitialization

end

-- Solutions.RAM_Lax109476Proofs_RamScaleArray
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamScaleArray

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleCoordinate RamRationalArrays RamRational RamCenterUpdate RamCopy







def scaleStep (a b : String) : Com := .seq (scaleCoordinate a b)
  (.assign "scale.i" (.add (.var "scale.i") (.lit 1)))



def scaleLoop (a b : String) : Com := .seq (.assign "scale.i" (.lit 0))
  (.while (.lt (.var "scale.i") (.var "vec.n")) (scaleStep a b))



def scaleArray (a b : String) : Com := .seq (RamZeroArray.zeroRationalArray b) (scaleLoop a b)



end Lax109476Proofs.RamScaleArray

end

-- Solutions.RAM_Lax109476Proofs_RamScaleBlock
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamScaleBlock

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleArray RamRationalArrays RamReadBlock







def scaleBlock (a b field : String) : Com := .seq (.assign "vec.n" (.var field)) (scaleArray a b)



end Lax109476Proofs.RamScaleBlock

end

-- Solutions.RAM_Lax109476Proofs_RamClearProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamClearProgram

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamScaleArray RamScaleBlock RamRationalArrays RamStoredProgram
open IntegerEncoding RamEllipsoidStep

def IntegerRep {m n : ℕ} (P : Program ℚ m n) (σ : Env) : Prop :=
  Represents "int.A" (RamMatrixStorage.flatten (rationalProgram (integerProgram P)).A) σ ∧
    Represents "int.b" (List.ofFn (rationalProgram (integerProgram P)).b) σ ∧
    Represents "int.c" (List.ofFn (rationalProgram (integerProgram P)).c) σ

def clearProgram : Com := .seq (.assign "scale.factor" (.var "den.value"))
  (.seq (scaleBlock "lp.A" "int.A" "decode.count")
    (.seq (scaleBlock "lp.b" "int.b" "lp.m") (scaleBlock "lp.c" "int.c" "lp.n")))



end Lax109476Proofs.RamClearProgram

end

-- Solutions.RAM_Lax109476Proofs_RamSolverFrontEnd
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverFrontEnd

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep IntegerEncoding

def frontEnd : Com := .seq RamSolverInitialization.initializeSolver
  (.ite (.eq (.var "input.valid") (.lit 1)) clearProgram .skip)

def Input {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (σ : Env) : Prop :=
  RamDecoder.Input B (encodeProgram P) σ ∧ Extents "int.A" (m * n) σ ∧
    Extents "int.b" m σ ∧ Extents "int.c" n σ

def Output {m n : ℕ} (P : Program ℚ m n) (τ : Env) : Prop :=
  RepresentsProgram P τ ∧ IntegerRep P τ ∧ τ.vars "input.valid" = 1 ∧
    τ.vars "input.bits" = bitSize (encodeProgram P) ∧
    τ.vars "den.value" = programDenominator P ∧ τ.inp = []

def instructionBound (L : ℕ) : ℕ := RamSolverInitialization.instructionBound L +
  (72 * (L + 1) + 135) * L + 86





end Lax109476Proofs.RamSolverFrontEnd

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilitySetup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilitySetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding
open RamNormalizedBounds

def setup : Com := .seq RamFeasibilityParameters.prepareParameters RamNormalizeQuery.normalizeQuery

def wordWidth (S : ℕ) : ℕ := RamFeasibilityScaleBounds.wordWidth S +
  RamDecoder.wordWidth (coefficientBits S) + (S + 1) ^ 2 + S + 2

def instructionBound (S : ℕ) : ℕ := RamFeasibilityParameters.instructionBound S +
  (72 * (coefficientBits S + 1) + 181) * (S * S) +
  (72 * (coefficientBits S + 1) + 189) * S + 78





end Lax109476Proofs.RamFeasibilitySetup

end

-- Solutions.RAM_Lax109476Proofs_RamIntegerFeasibility
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamNormalizedBounds

def iterationBound (S : ℕ) : ℕ := 1024 * (S + 1) ^ 4 + 1

def wordWidth (S : ℕ) : ℕ := RamFeasibilitySetup.wordWidth S +
  RamSearchBounds.wordWidth S S (iterationBound S) (coefficientBits S)

def decideFeasible : Com := .seq RamFeasibilitySetup.setup RamSearchLoop.search







def uniformInstructionBound (S : ℕ) : ℕ := RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound S S (iterationBound S) (coefficientBits S)









end Lax109476Proofs.RamIntegerFeasibility

end

-- Solutions.RAM_Lax109476Proofs_RamPadMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPadMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamMatrixStorage
open RamCenterUpdate RamEllipsoidStep



def padCoordinate : Com := .seq
  (.assign "pad.row" (.div (.var "pad.k") (.add (.var "source.n") (.lit 2))))
  (.seq (.assign "pad.col" (.sub (.var "pad.k")
    (.mul (.var "pad.row") (.add (.var "source.n") (.lit 2)))))
    (.seq RamPadSelector.selectEntry
      (.seq (.assign "vec.i" (.var "pad.k")) (storeReduced "pad.A"))))





def padStep : Com := .seq padCoordinate (.assign "pad.k" (.add (.var "pad.k") (.lit 1)))



def padLoop : Com := .seq (.assign "pad.k" (.lit 0))
  (.while (.lt (.var "pad.k") (.var "pad.count")) padStep)



def padMatrix : Com := .seq
  (.assign "pad.count" (.mul (.add (.var "source.m") (.lit 2)) (.add (.var "source.n") (.lit 2))))
  (.seq (.assign "vec.n" (.var "pad.count")) (.seq (RamZeroArray.zeroRationalArray "pad.A") padLoop))



end Lax109476Proofs.RamPadMatrix

end

-- Solutions.RAM_Lax109476Proofs_RamPadBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPadBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCenterUpdate RamEllipsoidStep







def selectBound : Com := .ite (.lt (.var "pad.k") (.var "source.m"))
  (.seq (.assign "vec.i" (.var "pad.k")) (.seq (loadLeft "query.b") RamCopy.leftToResult))
  (RamPadSelector.constantFraction 0)



def padCoordinate : Com := .seq selectBound
  (.seq (.assign "vec.i" (.var "pad.k")) (storeReduced "pad.b"))





def padStep : Com := .seq padCoordinate (.assign "pad.k" (.add (.var "pad.k") (.lit 1)))



def padLoop : Com := .seq (.assign "pad.k" (.lit 0))
  (.while (.lt (.var "pad.k") (.var "pad.count")) padStep)



def padBound : Com := .seq (.assign "pad.count" (.add (.var "source.m") (.lit 2)))
  (.seq (.assign "vec.n" (.var "pad.count")) (.seq (RamZeroArray.zeroRationalArray "pad.b") padLoop))



end Lax109476Proofs.RamPadBound

end

-- Solutions.RAM_Lax109476Proofs_RamQueryPadding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamQueryPadding

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage

def padQuery : Com := .seq RamPadMatrix.padMatrix (.seq RamPadBound.padBound
  (.seq (.assign "query.m" (.add (.var "source.m") (.lit 2)))
    (.seq (.assign "query.n" (.add (.var "source.n") (.lit 2)))
      (.assign "query.bits" (.add (.var "source.bits") (.lit 4))))))







end Lax109476Proofs.RamQueryPadding

end

-- Solutions.RAM_Lax109476Proofs_RamPaddedFeasibility
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPaddedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding

 

def decideFeasible : Com := .seq RamQueryPadding.padQuery RamIntegerFeasibility.decideFeasible

def wordWidth (S : ℕ) : ℕ := RamIntegerFeasibility.wordWidth (S + 4) +
  RamDecoder.wordWidth (2 * S) + (S + 4) ^ 2 + S + 5

def instructionBound (S : ℕ) : ℕ := 111 * (S + 4) ^ 2 + 77 * (S + 4) + 78 +
  RamIntegerFeasibility.uniformInstructionBound (S + 4)





end Lax109476Proofs.RamPaddedFeasibility

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilityQuery
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilityQuery

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RamCopyBlock

def copyInput : Com := .seq (copyBlock "int.A" "query.A" "decode.count")
  (.seq (copyBlock "int.b" "query.b" "lp.m")
    (.seq (.assign "source.m" (.var "lp.m"))
      (.seq (.assign "source.n" (.var "lp.n")) (.assign "source.bits" (.var "input.bits")))))

def Workspace (m n : ℕ) (σ : Env) : Prop :=
  Extents "query.A" (m * n) σ ∧ Extents "query.b" m σ ∧
    Extents "pad.A" ((m + 2) * (n + 2)) σ ∧ Extents "pad.b" (m + 2) σ ∧
    Extents "search.rows" (((m + 2) + (n + 2)) * (n + 2)) σ ∧
    Extents "search.rhs" ((m + 2) + (n + 2)) σ ∧
    Extents "ell.center" (n + 2) σ ∧ Extents "ell.shape" ((n + 2) * (n + 2)) σ ∧
    RamEllipsoidStep.Workspace (n + 2) σ ∧ Extents "ell.normal" (n + 2) σ





end Lax109476Proofs.RamFeasibilityQuery

end

-- Solutions.RAM_Lax109476Proofs_RamRationalFeasibility
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

def decideFeasible : Com := .seq RamFeasibilityQuery.copyInput RamPaddedFeasibility.decideFeasible

def wordWidth (L : ℕ) : ℕ := RamPaddedFeasibility.wordWidth L + RamDecoder.wordWidth (2 * L)

def instructionBound (L : ℕ) : ℕ := 71 * L + 58 + RamPaddedFeasibility.instructionBound L





end Lax109476Proofs.RamRationalFeasibility

end

-- Solutions.RAM_Lax109476Proofs_RamStoredFeasibility
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamStoredFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep IntegerEncoding

def decideFeasible : Com := .seq RamProgramSize.prepareSize
  (.seq RamProgramDenominator.prepareDenominator
    (.seq clearProgram RamRationalFeasibility.decideFeasible))



def wordWidth (L : ℕ) : ℕ := RamDecoder.wordWidth L + RamRationalFeasibility.wordWidth L

def instructionBound (L : ℕ) : ℕ :=
  (36 * (L + 1) + 61) * L + 24 * L + 56 + 13 * L + 26 +
    (72 * (L + 1) + 135) * L + 80 + RamRationalFeasibility.instructionBound L





end Lax109476Proofs.RamStoredFeasibility

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryThreshold
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryThreshold

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars RamEllipsoidStep



def Workspace (m n : ℕ) (σ : Env) : Prop :=
  RamRecoveryQuery.Extent m n σ ∧
    Extents "int.A" (((m + (n + n)) + 1) * n) σ ∧
    Extents "int.b" ((m + (n + n)) + 1) σ ∧ Extents "int.c" n σ ∧
    RamFeasibilityQuery.Workspace ((m + (n + n)) + 1) n σ



def decideThreshold : Com := .seq RamRecoveryQuery.buildQuery RamStoredFeasibility.decideFeasible
















end Lax109476Proofs.RamRecoveryThreshold

end

-- Solutions.RAM_Lax109476Proofs_RamContinuedFractionStep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamContinuedFractionStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamArithmetic RamFractionInterface



def quotientRemainder : Com :=
  .seq (.assign "cf.a" (.div (.var "left.n") (.var "left.d")))
    (.seq (.assign "cf.r" (.sub (.var "left.n") (.mul (.var "cf.a") (.var "left.d"))))
      (.assign "rat.s" (.lit 0)))

def finish : Com := .ite (.eq (.var "cf.r") (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
  (.seq (.assign "rat.n" (.var "left.d"))
    (.seq (.assign "rat.d" (.var "cf.r")) normalizeFraction))

def step : Com := .seq quotientRemainder finish









end Lax109476Proofs.RamContinuedFractionStep

end

-- Solutions.RAM_Lax109476Proofs_RamContinuedFractionStack
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamContinuedFractionStack

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface
open RamContinuedFractionStep



def forwardStep : Com := .seq RamContinuedFractionStep.step
  (.seq (.store "cf.stack" (.var "cf.i") (.var "cf.a"))
    (.seq resultToLeft (.assign "cf.i" (.add (.var "cf.i") (.lit 1)))))





def forward : Com := .seq (.assign "cf.i" (.lit 0))
  (.while (.lt (.var "cf.i") (.var "cf.limit")) forwardStep)



end Lax109476Proofs.RamContinuedFractionStack

end

-- Solutions.RAM_Lax109476Proofs_RamContinuedFractionFoldStep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamContinuedFractionFoldStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface
open RamContinuedFractionStack

def restoreFloor : Com := .seq (.assign "left.s" (.lit 0))
  (.seq (.assign "left.n" (.get "cf.stack" (.var "cf.back"))) (.assign "left.d" (.lit 1)))

 

 def foldStep : Com := .seq
  (.assign "cf.back" (.sub (.sub (.var "cf.limit") (.var "cf.done")) (.lit 1)))
  (.seq resultToLeft (.seq invertFraction (.seq resultToRight
    (.seq restoreFloor (.seq addFraction (.assign "cf.done" (.add (.var "cf.done") (.lit 1))))))))

 



end Lax109476Proofs.RamContinuedFractionFoldStep

end

-- Solutions.RAM_Lax109476Proofs_RamContinuedFractionConvergent
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamContinuedFractionConvergent

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface
open RamContinuedFractionStack RamContinuedFractionFoldStep

def zeroResult : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))

def foldStack : Com := .seq zeroResult (.seq (.assign "cf.done" (.lit 0))
  (.while (.lt (.var "cf.done") (.var "cf.limit")) foldStep))





def convergent : Com := .seq (.assign "cf.limit" (.add (.var "cf.depth") (.lit 1)))
  (.seq RamContinuedFractionStack.forward foldStack)



end Lax109476Proofs.RamContinuedFractionConvergent

end

-- Solutions.RAM_Lax109476Proofs_RamConvergentBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamConvergentBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface

def exponent (S K : ℕ) : ℕ := (S + 1) * (K + 2)

def wordWidth (S K : ℕ) : ℕ := RamDecoder.wordWidth (exponent S K) + K + 2

def instructionBound (S K : ℕ) : ℕ :=
  ((36 * (S + 1) + 113) + (108 * (exponent S K + 1) + 208)) * (K + 1) + 22





end Lax109476Proofs.RamConvergentBounds

end

-- Solutions.RAM_Lax109476Proofs_RamReconstructionCandidate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReconstructionCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def finish : Com :=
  .ite (.lt (.var "recon.bound") (.var "rat.d")) (.assign "recon.accept" (.lit 0))
    (.ite (.eq (.var "recon.lower") (.lit 1))
      (.assign "recon.accept" (.var "cmp.le")) (.assign "recon.accept" (.lit 0)))



def check : Com := .seq (readLeft "recon.lo")
  (.seq resultToRight (.seq RamComparison.compareFraction
    (.seq (.assign "recon.lower" (.var "cmp.le"))
      (.seq resultToLeft (.seq (readRight "recon.hi")
        (.seq RamComparison.compareFraction finish))))))





end Lax109476Proofs.RamReconstructionCandidate

end

-- Solutions.RAM_Lax109476Proofs_RamConvergentCandidate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamConvergentCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def testCandidate : Com := .seq (readLeft "recon.hi")
  (.seq (.assign "cf.depth" (.var "recon.i"))
    (.seq RamContinuedFractionConvergent.convergent RamReconstructionCandidate.check))



end Lax109476Proofs.RamConvergentCandidate

end

-- Solutions.RAM_Lax109476Proofs_RamReconstructionRecord
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReconstructionRecord

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars



def record : Com := .seq (save "recon.result") (.assign "recon.found" (.lit 1))



def candidate : Com := .seq RamConvergentCandidate.testCandidate
  (.ite (.eq (.var "recon.accept") (.lit 1)) record .skip)



end Lax109476Proofs.RamReconstructionRecord

end

-- Solutions.RAM_Lax109476Proofs_RamReconstructionSearch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReconstructionSearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars
open RamReconstructionRecord

def searchStep : Com := .seq (.ite (.eq (.var "recon.found") (.lit 1)) .skip candidate)
  (.assign "recon.i" (.add (.var "recon.i") (.lit 1)))







def search : Com := .seq (.assign "recon.found" (.lit 0))
  (.seq (.assign "recon.i" (.lit 0))
    (.while (.lt (.var "recon.i") (.var "recon.limit")) searchStep))



end Lax109476Proofs.RamReconstructionSearch

end

-- Solutions.RAM_Lax109476Proofs_RamRationalReconstruction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalReconstruction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalScalars

def prepare : Com := .seq (.assign "bits.v" (.var "recon.hi.d"))
  (.seq RamBitLength.bitLength
    (.assign "recon.limit" (.add (.mul (.var "bits.k") (.lit 2)) (.lit 1))))

def depthBound (S : ℕ) : ℕ := 2 * (S + 1) + 1

def wordWidth (S : ℕ) : ℕ := RamConvergentBounds.wordWidth S (depthBound S)

def instructionBound (S : ℕ) : ℕ :=
  (RamConvergentBounds.instructionBound S (depthBound S) + 156) * depthBound S + 12 * (S + 1) + 22



def reconstruct : Com := .seq prepare RamReconstructionSearch.search



end Lax109476Proofs.RamRationalReconstruction

end

-- Solutions.RAM_Lax109476Proofs_RamBinaryMinimum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamBinaryMinimum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalScalars

def endpoints : Com := .seq (.assign "bisect.lo.s" (.lit 0))
  (.seq (.assign "bisect.lo.n" (.lit 0))
  (.seq (.assign "bisect.lo.d" (.lit 1))
  (.seq (.assign "bisect.hi.s" (.lit 0))
  (.seq (.assign "bisect.hi.n" (.var "minimum.bound"))
  (.seq (.assign "bisect.hi.d" (.lit 1))
    (.assign "bits.v" (.var "minimum.bound")))))))

def setLimit : Com := .assign "bisect.limit" (.add (.mul (.lit 3) (.var "bits.k")) (.lit 2))

def prepare : Com := .seq endpoints (.seq RamBitLength.bitLength setLimit)

def finish : Com := .seq (RamScalarCopy.copy "bisect.lo" "recon.lo")
  (.seq (RamScalarCopy.copy "bisect.hi" "recon.hi")
    (.seq (.assign "recon.bound" (.var "minimum.bound")) RamRationalReconstruction.reconstruct))

/-- A fixed RAM program computes a bounded rational minimum using threshold
queries, then continued-fraction reconstruction. -/
def minimum (query : Com) : Com := .seq prepare (.seq (RamBisectionLoop.loop query) finish)







end Lax109476Proofs.RamBinaryMinimum

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryMinimum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryMinimum

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalScalars RamRationalArrays RamRecoveryThreshold











def recoverCoordinate : Com := RamBinaryMinimum.minimum decideThreshold




end Lax109476Proofs.RamRecoveryMinimum

end

-- Solutions.RAM_Lax109476Proofs_RamPointRecoveryStep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPointRecoveryStep

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamRationalScalars RamRecoveryThreshold


def install : Com := .seq (RamScalarCopy.copy "recon.result" "rat")
  (.seq (.assign "vec.i" (.var "point.k"))
    (.seq (storeReduced "point.x") (.assign "point.k" (.add (.var "point.k") (.lit 1)))))

def step : Com := .seq RamRecoveryMinimum.recoverCoordinate install








end Lax109476Proofs.RamPointRecoveryStep

end

-- Solutions.RAM_Lax109476Proofs_RamPointRecovery
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRecoveryThreshold RamPointRecoveryStep





def recover : Com := .seq (.assign "point.k" (.lit 0))
  (.while (.lt (.var "point.k") (.var "point.n")) RamPointRecoveryStep.step)




end Lax109476Proofs.RamPointRecovery

end

-- Solutions.RAM_Lax109476Proofs_RamPointRecoveryBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPointRecoveryBounds

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamPointRecovery RamRecoveryThreshold

def querySize (m n S : ℕ) : ℕ :=
  ((m + (n + n)) + 1) + n + 2 +
    ((((m + (n + n)) + 1) * n) + ((m + (n + n)) + 1) + n) * (4 + 2 * (2 * S + 3))

def queryCost (m n S : ℕ) : ℕ :=
  142 * (((m + (n + n)) + 1) * n) + 138 * ((m + (n + n)) + 1) + 33 * n + 106 +
    RamStoredFeasibility.instructionBound (querySize m n S)

def wordWidth (m n S : ℕ) : ℕ := RamDecoder.wordWidth (S + 1) +
  RamRationalReconstruction.wordWidth S + RamStoredFeasibility.wordWidth (querySize m n S) +
    (((m + (n + n)) + 1) * n + m + (n + n) + 4) + S + 4

def instructionBound (m n S C : ℕ) : ℕ :=
  ((144 * (S + 1) + 342 + queryCost m n S) * (3 * C + 2) + 12 * C +
    RamRationalReconstruction.instructionBound S + 77) * n + 6








end Lax109476Proofs.RamPointRecoveryBounds

end

-- Solutions.RAM_Lax109476Proofs_RamPointInitialization
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPointInitialization

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRecoveryThreshold RamEllipsoidStep



def prepare : Com := .seq (.assign "vec.n" (.var "point.n"))
  (.seq (RamZeroArray.zeroRationalArray "point.x") (.assign "point.k" (.lit 0)))



def recover : Com := .seq prepare RamPointRecovery.recover




end Lax109476Proofs.RamPointInitialization

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateBuilder
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays IntegerEncoding RamEllipsoidStep


def buildSystem (matrixSelector boundSelector : Com) : Com :=
  .seq (RamCertificateMatrix.matrix matrixSelector) (RamCertificateBound.buildBound boundSelector)



end Lax109476Proofs.RamCertificateBuilder

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateMetadata
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateMetadata

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamCertificateSource

def optimal : Com := .seq
  (.assign "system.m" (.add (.var "source.m") (.add (.var "source.n") (.lit 2))))
  (.assign "system.n" (.add (.var "source.n") (.var "source.m")))

def infeasible : Com := .seq (.assign "system.m" (.add (.var "source.n") (.lit 1)))
  (.assign "system.n" (.var "source.m"))

def unbounded : Com := .seq
  (.assign "system.m" (.add (.var "source.m") (.add (.var "source.m") (.lit 1))))
  (.assign "system.n" (.add (.var "source.n") (.var "source.n")))







end Lax109476Proofs.RamCertificateMetadata

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateLoad
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateLoad

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCertificateSource IntegerEncoding

def matrix : Com := .seq (.assign "vec.i"
  (.add (.mul (.var "query.a.row") (.var "source.n")) (.var "query.a.col"))) (RamArrayResult.load "source.A")





def vector (a : String) : Com := .seq (.assign "vec.i" (.var "query.a.row")) (RamArrayResult.load a)









end Lax109476Proofs.RamCertificateLoad

end

-- Solutions.RAM_Lax109476Proofs_RamPairSelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPairSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCertificateSource IntegerEncoding

def primalEntry : Com := .ite (.lt (.var "query.col") (.var "source.n"))
  (.seq (.assign "query.a.row" (.var "query.row"))
    (.seq (.assign "query.a.col" (.var "query.col")) RamCertificateLoad.matrix))
  (RamPadSelector.constantFraction 0)

def dualEntry : Com := .ite (.lt (.var "query.col") (.var "source.n"))
  (RamPadSelector.constantFraction 0)
  (.seq (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n")))
    (.seq (.assign "query.a.col" (.sub (.var "query.row") (.var "source.m")))
      (.seq RamCertificateLoad.matrix RamResultNegation.negateResult)))

def gapEntry : Com := .ite (.lt (.var "query.col") (.var "source.n"))
  (.seq (.assign "query.a.row" (.var "query.col")) (RamCertificateLoad.vector "source.c"))
  (.seq (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n")))
    (.seq (RamCertificateLoad.vector "source.b") RamResultNegation.negateResult))

def selectEntry : Com := .ite (.lt (.var "query.row") (.var "source.m")) primalEntry
  (.ite (.lt (.var "query.row") (.add (.var "source.m") (.var "source.n"))) dualEntry
    (.ite (.eq (.var "query.row") (.add (.var "source.m") (.var "source.n"))) gapEntry
      (.seq gapEntry RamResultNegation.negateResult)))



def selectBound : Com := .ite (.lt (.var "query.row") (.var "source.m"))
  (.seq (.assign "query.a.row" (.var "query.row")) (RamCertificateLoad.vector "source.b"))
  (.ite (.lt (.var "query.row") (.add (.var "source.m") (.var "source.n")))
    (.seq (.assign "query.a.row" (.sub (.var "query.row") (.var "source.m")))
      (.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult))
    (RamPadSelector.constantFraction 0))



end Lax109476Proofs.RamPairSelector

end

-- Solutions.RAM_Lax109476Proofs_RamFarkasSelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFarkasSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCertificateSource IntegerEncoding

def selectEntry : Com := .ite (.lt (.var "query.row") (.var "source.n"))
  (.seq (.assign "query.a.row" (.var "query.col"))
    (.seq (.assign "query.a.col" (.var "query.row"))
      (.seq RamCertificateLoad.matrix RamResultNegation.negateResult)))
  (.seq (.assign "query.a.row" (.var "query.col")) (RamCertificateLoad.vector "source.b"))



def selectBound : Com := .ite (.lt (.var "query.row") (.var "source.n"))
  (RamPadSelector.constantFraction 0)
  (.seq (RamPadSelector.constantFraction 1) RamResultNegation.negateResult)



end Lax109476Proofs.RamFarkasSelector

end

-- Solutions.RAM_Lax109476Proofs_RamRaySelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRaySelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamCertificateSource IntegerEncoding

def selectEntry : Com := .ite (.lt (.var "query.row") (.var "source.m"))
  (.ite (.lt (.var "query.col") (.var "source.n"))
    (.seq (.assign "query.a.row" (.var "query.row"))
      (.seq (.assign "query.a.col" (.var "query.col")) RamCertificateLoad.matrix))
    (RamPadSelector.constantFraction 0))
  (.ite (.lt (.var "query.row") (.add (.var "source.m") (.var "source.m")))
    (.ite (.lt (.var "query.col") (.var "source.n")) (RamPadSelector.constantFraction 0)
      (.seq (.assign "query.a.row" (.sub (.var "query.row") (.var "source.m")))
        (.seq (.assign "query.a.col" (.sub (.var "query.col") (.var "source.n"))) RamCertificateLoad.matrix)))
    (.ite (.lt (.var "query.col") (.var "source.n")) (RamPadSelector.constantFraction 0)
      (.seq (.assign "query.a.row" (.sub (.var "query.col") (.var "source.n")))
        (.seq (RamCertificateLoad.vector "source.c") RamResultNegation.negateResult))))



def selectBound : Com := .ite (.lt (.var "query.row") (.var "source.m"))
  (.seq (.assign "query.a.row" (.var "query.row")) (RamCertificateLoad.vector "source.b"))
  (.ite (.lt (.var "query.row") (.add (.var "source.m") (.var "source.m")))
    (RamPadSelector.constantFraction 0)
    (.seq (RamPadSelector.constantFraction 1) RamResultNegation.negateResult))



end Lax109476Proofs.RamRaySelector

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateFamilies
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateFamilies

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateSource

def withMetadata (metadata matrixSelector boundSelector : Com) : Com :=
  .seq metadata (RamCertificateBuilder.buildSystem matrixSelector boundSelector)

def optimal : Com := withMetadata RamCertificateMetadata.optimal RamPairSelector.selectEntry RamPairSelector.selectBound
def infeasible : Com := withMetadata RamCertificateMetadata.infeasible RamFarkasSelector.selectEntry RamFarkasSelector.selectBound
def unbounded : Com := withMetadata RamCertificateMetadata.unbounded RamRaySelector.selectEntry RamRaySelector.selectBound











end Lax109476Proofs.RamCertificateFamilies

end

-- Solutions.RAM_Lax109476Proofs_RamFamilyQueryCopy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFamilyQueryCopy

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCopy

def metadata : Com := .seq (.assign "lp.m" (.var "system.m")) (.assign "lp.n" (.var "system.n"))
def count : Com := .assign "decode.count" (.mul (.var "system.m") (.var "system.n"))
def zeroObjective (a : String) : Com := .seq (.assign "vec.n" (.var "system.n")) (RamZeroArray.zeroRationalArray a)

def copy (sourceA sourceB targetA targetB targetC : String) : Com := .seq count
  (.seq (RamCopyBlock.copyBlock sourceA targetA "decode.count")
  (.seq (RamCopyBlock.copyBlock sourceB targetB "system.m")
  (.seq (zeroObjective targetC) metadata)))















end Lax109476Proofs.RamFamilyQueryCopy

end

-- Solutions.RAM_Lax109476Proofs_RamArrayRelabel
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def expression (f : String → String) : Expr → Expr
  | .lit v => .lit v
  | .var x => .var x
  | .get a i => .get (f a) (expression f i)
  | .bin op e g => .bin op (expression f e) (expression f g)

def condition (f : String → String) : Cond → Cond
  | .eq e g => .eq (expression f e) (expression f g)
  | .lt e g => .lt (expression f e) (expression f g)

def command (f : String → String) : Com → Com
  | .skip => .skip
  | .assign x e => .assign x (expression f e)
  | .store a i e => .store (f a) (expression f i) (expression f e)
  | .seq c d => .seq (command f c) (command f d)
  | .ite b c d => .ite (condition f b) (command f c) (command f d)
  | .while b c => .while (condition f b) (command f c)
  | .read x => .read x
  | .write e => .write (expression f e)

def view (f : String → String) (σ : Env) : Env := {σ with arrs := fun a => σ.arrs (f a)}

















def prefixed (name : String) (c : Com) : Com := command (fun a => name ++ a) c





end Lax109476Proofs.RamArrayRelabel

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateArrayRelabel
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateArrayRelabel

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def sourceNames : List String := ["source.A.s", "source.A.n", "source.A.d",
  "source.b.s", "source.b.n", "source.b.d", "source.c.s", "source.c.n", "source.c.d"]

def relabel (name a : String) : String := if a ∈ sourceNames then a else name ++ a



def isolated (name : String) (c : Com) : Com := RamArrayRelabel.command (relabel name) c

















end Lax109476Proofs.RamCertificateArrayRelabel

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateDecision
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateDecision

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

def prefixedView (name : String) (σ : Env) : Env := RamArrayRelabel.view (fun a => name ++ a) σ

def prepare (source target : String) : Com := RamFamilyQueryCopy.copy
  (source ++ "system.A") (source ++ "system.b") (target ++ "lp.A") (target ++ "lp.b") (target ++ "lp.c")

def decideFeasible (source target : String) : Com := .seq (prepare source target)
  (RamArrayRelabel.prefixed target RamStoredFeasibility.decideFeasible)

def sizeBound (r s S : ℕ) : ℕ := r + s + 2 + (r * s + r + s) * (4 + 2 * (2 * S + 1))
def instructionBound (r s S : ℕ) : ℕ := 71 * (r * s + r) + 33 * s + 80 +
  RamStoredFeasibility.instructionBound (sizeBound r s S)














end Lax109476Proofs.RamCertificateDecision

end

-- Solutions.RAM_Lax109476Proofs_RamEquationSelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEquationSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays IntegerEncoding

def selectSlack : Com := .ite (.lt (.var "query.col") (.var "system.n"))
  (.seq (.assign "vec.i" (.add (.mul (.var "query.baseRow") (.var "system.n")) (.var "query.col")))
    (RamArrayResult.load "system.A"))
  (.ite (.eq (.sub (.var "query.col") (.var "system.n")) (.var "query.baseRow"))
    (RamPadSelector.constantFraction 1) (RamPadSelector.constantFraction 0))





def prepareRow : Com := .ite (.lt (.var "query.row") (.var "system.m"))
  (.assign "query.baseRow" (.var "query.row"))
  (.assign "query.baseRow" (.sub (.var "query.row") (.var "system.m")))

def applyRowSign : Com := .ite (.lt (.var "query.row") (.var "system.m")) .skip RamResultNegation.negateResult

def selectEntry : Com := .seq prepareRow (.seq selectSlack applyRowSign)





end Lax109476Proofs.RamEquationSelector

end

-- Solutions.RAM_Lax109476Proofs_RamEquationMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEquationMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamEllipsoidStep



def selectCoordinate : Com := .seq
  (.assign "query.row" (.div (.var "build.i") (.add (.var "system.n") (.var "system.m"))))
  (.seq (.assign "query.col" (.sub (.var "build.i")
    (.mul (.var "query.row") (.add (.var "system.n") (.var "system.m"))))) RamEquationSelector.selectEntry)



def prepare : Com := .assign "build.count"
  (.mul (.add (.var "system.m") (.var "system.m")) (.add (.var "system.n") (.var "system.m")))

def matrix : Com := .seq prepare (RamBuildVector.build "point.A" selectCoordinate)



end Lax109476Proofs.RamEquationMatrix

end

-- Solutions.RAM_Lax109476Proofs_RamEquationBoundSelector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEquationBoundSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays IntegerEncoding

def selectBound : Com := .seq RamEquationSelector.prepareRow
  (.seq (.assign "vec.i" (.var "query.baseRow"))
    (.seq (RamArrayResult.load "system.b") RamEquationSelector.applyRowSign))



end Lax109476Proofs.RamEquationBoundSelector

end

-- Solutions.RAM_Lax109476Proofs_RamEquationBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEquationBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamEllipsoidStep

def selectCoordinate : Com := .seq (.assign "query.row" (.var "build.i")) RamEquationBoundSelector.selectBound



def prepare : Com := .assign "build.count" (.add (.var "system.m") (.var "system.m"))
def buildBound : Com := .seq prepare (RamBuildVector.build "point.b" selectCoordinate)



end Lax109476Proofs.RamEquationBound

end

-- Solutions.RAM_Lax109476Proofs_RamEquationBuilder
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEquationBuilder

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep

def metadata : Com := .seq (.assign "point.m" (.add (.var "system.m") (.var "system.m")))
  (.assign "point.n" (.add (.var "system.n") (.var "system.m")))

/-- Add slack coordinates and the negated inequalities that express each
equation. The stored integer system remains immutable during point recovery. -/
def buildSystem : Com := .seq RamEquationMatrix.matrix (.seq RamEquationBound.buildBound metadata)





end Lax109476Proofs.RamEquationBuilder

end

-- Solutions.RAM_Lax109476Proofs_RamRecoverFeasibleSystem
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoverFeasibleSystem

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep
open IntegerEncoding

def capBits (S : ℕ) : ℕ := 32 * (S + 1) ^ 2
def recoveryBits (S : ℕ) : ℕ := 4 * capBits S + 2 * S + 2

def wordWidth (m n S : ℕ) : ℕ :=
  RamPointRecoveryBounds.wordWidth (m + m) (n + m) (recoveryBits S) +
    RamCoordinateCapBounds.wordWidth S + (m + m) * (n + m) + m + m + n + 4 + S + 8

def instructionBound (m n S : ℕ) : ℕ :=
  118 * ((m + m) * (n + m)) + 91 * (m + m) + 33 * (n + m) + 48 * S + 192 +
    RamPointRecoveryBounds.instructionBound (m + m) (n + m) (recoveryBits S) (capBits S)

def prepareCap : Com := .seq (.assign "query.m" (.var "system.m"))
  (.seq (.assign "query.n" (.var "system.n")) (.assign "cap.H" (.var "system.H")))

def recover : Com := .seq RamEquationBuilder.buildSystem (.seq prepareCap
  (.seq RamCoordinateCap.prepareCap
    (.seq (.assign "minimum.bound" (.var "cap.value")) RamPointInitialization.recover)))








end Lax109476Proofs.RamRecoverFeasibleSystem

end

-- Solutions.RAM_Lax109476Proofs_RamWriteVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamWriteVector

open Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays

def increment : Com := .assign "output.i" (.add (.var "output.i") (.lit 1))
def step (a : String) : Com := .seq (.assign "vec.i" (.var "output.i"))
  (.seq (RamArrayResult.load a) (.seq RamEncoding.writeReducedFraction increment))





/-- Emit a prefix of a stored rational vector in the registered canonical
encoding. Slack coordinates beyond the prefix remain internal. -/
def writePrefix (a : String) : Com := .seq (.assign "output.i" (.lit 0))
  (.while (.lt (.var "output.i") (.var "output.count")) (step a))





end Lax109476Proofs.RamWriteVector

end

-- Solutions.RAM_Lax109476Proofs_RamWriteCertificate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamWriteCertificate

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays

/-- A literal outcome tag and the nonslack prefix of the recovered point.
The coordinate count is read from the runtime certificate-system metadata. -/
def emit (tag : ℕ) : Com := .seq (.write (.lit tag))
  (.seq (.assign "output.count" (.var "system.n")) (RamWriteVector.writePrefix "point.x"))























end Lax109476Proofs.RamWriteCertificate

end

-- Solutions.RAM_Lax109476Proofs_RamRecoverCertificate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoverCertificate

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

def recover (tag : ℕ) : Com := .seq RamRecoverFeasibleSystem.recover (RamWriteCertificate.emit tag)

















end Lax109476Proofs.RamRecoverCertificate

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateSetup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateSetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

def parameter (L : ℕ) : ℕ := 2 * (L + 4)

def Saved (m n L : ℕ) (σ : Env) : Prop :=
  σ.vars "certificate.m" = m ∧ σ.vars "certificate.n" = n ∧
    σ.vars "certificate.bits" = L ∧ σ.vars "certificate.parameter" = parameter L

def metadata : Com := .seq (.assign "certificate.m" (.var "lp.m"))
  (.seq (.assign "certificate.n" (.var "lp.n"))
  (.seq (.assign "certificate.bits" (.var "input.bits"))
  (.seq (.assign "certificate.parameter" (.mul (.lit 2) (.add (.var "input.bits") (.lit 4))))
  (.seq (.assign "system.H" (.shiftl (.lit 1) (.mul (.lit 2) (.var "certificate.parameter"))))
  (.seq (.assign "source.m" (.var "lp.m")) (.assign "source.n" (.var "lp.n")))))))



def copyCoefficients : Com := .seq (RamCopyBlock.copyBlock "int.A" "source.A" "decode.count")
  (.seq (RamCopyBlock.copyBlock "int.b" "source.b" "lp.m") (RamCopyBlock.copyBlock "int.c" "source.c" "lp.n"))



def save : Com := .seq copyCoefficients metadata



/-- The feasibility routines use `source.m` and `source.n` as scratch fields.
Restore them from the saved input dimensions before building another family. -/
def restore : Com := .seq (.assign "source.m" (.var "certificate.m"))
  (.assign "source.n" (.var "certificate.n"))



end Lax109476Proofs.RamCertificateSetup

end

-- Solutions.RAM_Lax109476Proofs_RamExactSolverProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamExactSolverProgram

open Lax808846Proofs.Imp
open RamCertificateArrayRelabel

def optimalSystem : Com := isolated "optimal.recovery." RamCertificateFamilies.optimal
def infeasibleSystem : Com := isolated "infeasible.recovery." RamCertificateFamilies.infeasible
def unboundedSystem : Com := isolated "unbounded.recovery." RamCertificateFamilies.unbounded

def optimalDecision : Com := RamCertificateDecision.decideFeasible "optimal.recovery." "optimal.decision."
def infeasibleDecision : Com := RamCertificateDecision.decideFeasible "infeasible.recovery." "infeasible.decision."

def optimalRecovery : Com := isolated "optimal.recovery." (RamRecoverCertificate.recover 0)
def infeasibleRecovery : Com := isolated "infeasible.recovery." (RamRecoverCertificate.recover 1)
def unboundedRecovery : Com := isolated "unbounded.recovery." (RamRecoverCertificate.recover 2)

/-- The failed optimal and infeasibility queries leave the unbounded family
as the feasible certificate system, by the proved certificate alternative. -/
def afterInfeasible : Com := .ite RamBisectionCommit.condition infeasibleRecovery
  (.seq RamCertificateSetup.restore (.seq unboundedSystem unboundedRecovery))

def afterOptimal : Com := .ite RamBisectionCommit.condition optimalRecovery
  (.seq RamCertificateSetup.restore (.seq infeasibleSystem (.seq infeasibleDecision afterInfeasible)))

def chooseCertificate : Com := .seq optimalSystem (.seq optimalDecision afterOptimal)

/-- One fixed command decodes and clears denominators, saves the original LP,
selects a feasible certificate system, recovers its exact point, and emits the
canonical output certificate. All loops use runtime dimensions and data. -/
def solve : Com := .seq RamSolverFrontEnd.frontEnd
  (.ite (.eq (.var "input.valid") (.lit 1)) (.seq RamCertificateSetup.save chooseCertificate) .skip)













end Lax109476Proofs.RamExactSolverProgram

end

-- Solutions.RAM_Lax109476Proofs_RamSolverWorkspace
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverWorkspace

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamCertificateArrayRelabel

def recoveryView (name : String) (σ : Env) : Env := RamArrayRelabel.view (relabel name) σ

def Recovery (name : String) (r s N : ℕ) (σ : Env) : Prop :=
  Extents "system.A" (r * s) (recoveryView name σ) ∧
  Extents "system.b" r (recoveryView name σ) ∧
  Extents "point.A" ((r + r) * (s + r)) (recoveryView name σ) ∧
  Extents "point.b" (r + r) (recoveryView name σ) ∧
  Extents "point.x" (s + r) (recoveryView name σ) ∧
  RamRecoveryThreshold.Workspace (r + r) (s + r) (recoveryView name σ) ∧
  ((recoveryView name σ).arrs "cf.stack").length = N

def Decision (name : String) (r s : ℕ) (σ : Env) : Prop :=
  Extents "lp.A" (r * s) (RamCertificateDecision.prefixedView name σ) ∧
  Extents "lp.b" r (RamCertificateDecision.prefixedView name σ) ∧
  Extents "lp.c" s (RamCertificateDecision.prefixedView name σ) ∧
  Extents "int.A" (r * s) (RamCertificateDecision.prefixedView name σ) ∧
  Extents "int.b" r (RamCertificateDecision.prefixedView name σ) ∧
  Extents "int.c" s (RamCertificateDecision.prefixedView name σ) ∧
  RamFeasibilityQuery.Workspace r s (RamCertificateDecision.prefixedView name σ)

def All (m n N : ℕ) (σ : Env) : Prop :=
  Recovery "optimal.recovery." (m + (n + 2)) (n + m) N σ ∧
  Decision "optimal.decision." (m + (n + 2)) (n + m) σ ∧
  Recovery "infeasible.recovery." (n + 1) m N σ ∧
  Decision "infeasible.decision." (n + 1) m σ ∧
  Recovery "unbounded.recovery." (m + (m + 1)) (n + n) N σ













end Lax109476Proofs.RamSolverWorkspace

end

-- Solutions.RAM_Lax109476Proofs_RamSolverOriginalContext
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverOriginalContext

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding

def Coefficients {m n : ℕ} (P : Program ℤ m n) (σ : Env) : Prop :=
  Represents "source.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
  Represents "source.b" (List.ofFn (rationalProgram P).b) σ ∧
  Represents "source.c" (List.ofFn (rationalProgram P).c) σ

def Context {m n : ℕ} (P : Program ℤ m n) (L : ℕ) (σ : Env) : Prop :=
  Coefficients P σ ∧ RamCertificateSetup.Saved m n L σ ∧
  σ.vars "system.H" = 2 ^ (2 * RamCertificateSetup.parameter L)







end Lax109476Proofs.RamSolverOriginalContext

end

-- Solutions.RAM_Lax109476Proofs_RamSolverBranchComposition
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverBranchComposition

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open IntegerEncoding RamExactSolverProgram

def Result {m n : ℕ} (P : Program ℤ m n) (σ τ : Env) : Prop :=
  ∃ certificate : Certificate m n,
    τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate (rationalProgram P) certificate






end Lax109476Proofs.RamSolverBranchComposition

end

-- Solutions.RAM_Lax109476Proofs_RamSolverBranchSpecs
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverBranchSpecs

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamCertificateArrayRelabel RamSolverWorkspace RamSolverOriginalContext

def State {m n : ℕ} (P : Program ℤ m n) (L N : ℕ) (σ : Env) : Prop :=
  Context P L σ ∧ All m n N σ











end Lax109476Proofs.RamSolverBranchSpecs

end

-- Solutions.RAM_Lax109476Proofs_RamDecodedProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamDecodedProgram

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamReadArray RamReadBody RamRationalArrays













def canonicalBound (L : ℕ) : ℕ := 2 * L + 4 + ((L + 1) ^ 2 + 2 * L + 2) * (4 + 2 * (L + 1))









end Lax109476Proofs.RamDecodedProgram

end

-- Solutions.RAM_Lax109476Proofs_RamSolverBranchBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverBranchBounds

def wordWidth (S : ℕ) : ℕ := RamRecoverFeasibleSystem.wordWidth S S S +
  RamStoredFeasibility.wordWidth (RamCertificateDecision.sizeBound S S S)

def recoveryCost (S : ℕ) : ℕ := RamRecoverFeasibleSystem.instructionBound S S S + 35 * S + 10
def buildCost (S : ℕ) : ℕ := 142 * (S * S) + 98 * S + 74
def decisionCost (S : ℕ) : ℕ := RamCertificateDecision.instructionBound S S S
def instructionBound (S : ℕ) : ℕ := 3 * buildCost S + 2 * decisionCost S + recoveryCost S + 32





















end Lax109476Proofs.RamSolverBranchBounds

end

-- Solutions.RAM_Lax109476Proofs_RamInitializationTotal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamInitializationTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram IntegerEncoding RamDecodedProgram

def wordWidth (L : ℕ) : ℕ := RamDecoder.wordWidth (canonicalBound L)








end Lax109476Proofs.RamInitializationTotal

end

-- Solutions.RAM_Lax109476Proofs_RamFrontEndTotal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFrontEndTotal

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RamClearProgram RamEllipsoidStep IntegerEncoding RamDecodedProgram





def wordWidth (L : ℕ) : ℕ := RamInitializationTotal.wordWidth L
def instructionBound (L : ℕ) : ℕ := RamSolverFrontEnd.instructionBound (canonicalBound L)



end Lax109476Proofs.RamFrontEndTotal

end

-- Solutions.RAM_Lax109476Proofs_RamUniformSolverBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamUniformSolverBounds



def canonicalSize (L : ℕ) : ℕ := RamDecodedProgram.canonicalBound L
def parameter (L : ℕ) : ℕ := RamCertificateSetup.parameter (canonicalSize L)
def stackLength (L : ℕ) : ℕ := RamRationalReconstruction.depthBound
  (RamRecoverFeasibleSystem.recoveryBits (parameter L)) + 1
def wordWidth (L : ℕ) : ℕ := RamFrontEndTotal.wordWidth L +
  RamSolverBranchBounds.wordWidth (parameter L) + 32 * (parameter L + 1) ^ 2 + 32
def instructionBound (L : ℕ) : ℕ := RamFrontEndTotal.instructionBound L +
  71 * canonicalSize L + 100 + RamSolverBranchBounds.instructionBound (parameter L) + 16
































end Lax109476Proofs.RamUniformSolverBounds

end

-- Solutions.RAM_Lax109476Proofs_RamSolverFinish
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverFinish

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding RamSolverWorkspace EncodingSize

def Input {m n : ℕ} (P : Program ℚ m n) (N : ℕ) (σ : Env) : Prop :=
  RamSolverFrontEnd.Output P σ ∧ Extents "source.A" (m * n) σ ∧
  Extents "source.b" m σ ∧ Extents "source.c" n σ ∧ All m n N σ

def Result {m n : ℕ} (P : Program ℚ m n) (σ τ : Env) : Prop :=
  ∃ certificate : Certificate m n,
    τ.out = σ.out ++ encodeCertificate certificate ∧ IsValidCertificate P certificate

def instructionBound (L : ℕ) : ℕ := 71 * L + 100 +
  RamSolverBranchBounds.instructionBound (RamCertificateSetup.parameter L)






end Lax109476Proofs.RamSolverFinish

end

-- Solutions.RAM_Lax109476Proofs_RamSolverCanonicalExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamSolverCanonicalExecution

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamEllipsoidStep RamSolverWorkspace RamUniformSolverBounds

def Input {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (σ : Env) : Prop :=
  RamSolverFrontEnd.Input B P σ ∧ Extents "source.A" (m * n) σ ∧
  Extents "source.b" m σ ∧ Extents "source.c" n σ ∧
  All m n (stackLength (bitSize (encodeProgram P))) σ





end Lax109476Proofs.RamSolverCanonicalExecution

end

-- Solutions.RAM_Lax263307_RegisteredLP
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Decoding rational LP certificates
type: definition
---
Decode the tagged certificate produced by the registered rational LP
solver: an optimal primal-dual pair, an infeasibility certificate, or an
unboundedness certificate.

# Formalization notes

The parser reads canonical sign-numerator-denominator triples and returns
the unconsumed suffix. `certificate` applies a supplied solver and returns
the decoded certificate, using a fixed fallback when parsing fails.
Correctness of the chosen solver and the fact that its output parses are
proved in the proof package.
-/

namespace Lax263307.RegisteredLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

def value (sign num den : ℕ) : ℚ :=
  if sign = 1 then -(num : ℚ) / den else (num : ℚ) / den

def rational : List ℕ → Option (ℚ × List ℕ)
  | sign :: num :: den :: rest => some (value sign num den, rest)
  | _ => none

def vector : ℕ → List ℕ → Option (List ℚ × List ℕ)
  | 0, input => some ([], input)
  | n + 1, input => (rational input).bind fun qr =>
      (vector n qr.2).map fun tail => (qr.1 :: tail.1, tail.2)

def vectorFunction (n : ℕ) (input : List ℕ) : Option ((Fin n → ℚ) × List ℕ) :=
  (vector n input).map fun result => (fun i => result.1.getD i.val 0, result.2)

def parse (m n : ℕ) : List ℕ → Option (Certificate m n × List ℕ)
  | 0 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction m zr.2).map fun yr => (.optimal zr.1 yr.1, yr.2)
  | 1 :: rest => (vectorFunction m rest).map fun yr => (.infeasible yr.1, yr.2)
  | 2 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction n zr.2).map fun dr => (.unbounded zr.1 dr.1, dr.2)
  | _ => none

def certificate {m n : ℕ} (solve : List ℕ → List ℕ) (P : Program ℚ m n) : Certificate m n :=
  ((parse m n (solve (encodeProgram P))).map Prod.fst).getD (.infeasible 0)

end Lax263307.RegisteredLP

end

-- Solutions.RAM_Lax455465Proofs_RamArithmetic
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/

namespace Lax455465Proofs.RamArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- One Euclidean step uses only operations compiled to the registered RAM. -/
def gcdStep : Com :=
  .seq (.assign "gcd.t" (.sub (.var "gcd.a")
    (.mul (.div (.var "gcd.a") (.var "gcd.b")) (.var "gcd.b"))))
    (.seq (.assign "gcd.a" (.var "gcd.b")) (.assign "gcd.b" (.var "gcd.t")))



def gcdDoubleStep : Com :=
  .seq gcdStep (.ite (.lt (.lit 0) (.var "gcd.b")) gcdStep .skip)

def gcdLoop : Com := .while (.lt (.lit 0) (.var "gcd.b")) gcdDoubleStep











/-- Reduce an unsigned numerator and positive denominator in place. The sign
is held separately by the rational representation and is left untouched. -/
def normalizeFraction : Com :=
  .seq (.assign "gcd.a" (.var "rat.n"))
    (.seq (.assign "gcd.b" (.var "rat.d"))
      (.seq gcdLoop
        (.seq (.assign "rat.n" (.div (.var "rat.n") (.var "gcd.a")))
          (.assign "rat.d" (.div (.var "rat.d") (.var "gcd.a"))))))



end Lax455465Proofs.RamArithmetic

end

-- Solutions.RAM_Lax455465Proofs_RamRational
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic















def invertFraction : Com :=
  .ite (.eq (.var "left.n") (.lit 0))
    (.seq (.assign "rat.n" (.lit 0))
      (.seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))))
    (.seq (.assign "rat.n" (.var "left.d"))
      (.seq (.assign "rat.d" (.var "left.n"))
        (.seq (.assign "rat.s" (.var "left.s")) normalizeFraction)))





def multiplyFraction : Com :=
  .seq (.assign "rat.n" (.mul (.var "left.n") (.var "right.n")))
    (.seq (.assign "rat.d" (.mul (.var "left.d") (.var "right.d")))
      (.seq (.ite (.eq (.var "left.s") (.var "right.s"))
        (.assign "rat.s" (.lit 0)) (.assign "rat.s" (.lit 1))) normalizeFraction))









def addFraction : Com :=
  .seq (.assign "sum.u" (.mul (.var "left.n") (.var "right.d")))
    (.seq (.assign "sum.v" (.mul (.var "right.n") (.var "left.d")))
      (.seq (.assign "rat.d" (.mul (.var "left.d") (.var "right.d")))
        (.seq (.ite (.eq (.var "left.s") (.var "right.s"))
          (.seq (.assign "rat.n" (.add (.var "sum.u") (.var "sum.v")))
            (.assign "rat.s" (.var "left.s")))
          (.ite (.lt (.var "sum.u") (.var "sum.v"))
            (.seq (.assign "rat.n" (.sub (.var "sum.v") (.var "sum.u")))
              (.assign "rat.s" (.var "right.s")))
            (.seq (.assign "rat.n" (.sub (.var "sum.u") (.var "sum.v")))
              (.assign "rat.s" (.var "left.s"))))) normalizeFraction)))



end Lax455465Proofs.RamRational

end

-- Solutions.RAM_Lax455465Proofs_RamComparison
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/

namespace Lax455465Proofs.RamComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational







def compareFraction : Com :=
  .seq (.assign "cmp.u" (.mul (.var "left.n") (.var "right.d")))
    (.seq (.assign "cmp.v" (.mul (.var "right.n") (.var "left.d")))
      (.ite (.eq (.var "left.s") (.var "right.s"))
        (.ite (.eq (.var "left.s") (.lit 1))
          (.ite (.lt (.var "cmp.u") (.var "cmp.v"))
            (.assign "cmp.le" (.lit 0)) (.assign "cmp.le" (.lit 1)))
          (.ite (.lt (.var "cmp.v") (.var "cmp.u"))
            (.assign "cmp.le" (.lit 0)) (.assign "cmp.le" (.lit 1))))
        (.ite (.eq (.var "left.s") (.lit 1)) (.assign "cmp.le" (.lit 1))
          (.ite (.eq (.var "left.n") (.lit 0))
            (.ite (.eq (.var "right.n") (.lit 0))
              (.assign "cmp.le" (.lit 1)) (.assign "cmp.le" (.lit 0)))
            (.assign "cmp.le" (.lit 0))))))





end Lax455465Proofs.RamComparison

end

-- Solutions.RAM_Lax263307Proofs_NativeSignedArithmetic
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational



def save (name : String) : Com := .seq (.assign (name++".s") (.var "rat.s"))
  (.seq (.assign (name++".n") (.var "rat.n")) (.assign (name++".d") (.var "rat.d")))

def load (name : String) : Com := .seq (.assign "rat.s" (.var (name++".s")))
  (.seq (.assign "rat.n" (.var (name++".n"))) (.assign "rat.d" (.var (name++".d"))))







def Bounded (M : ℕ) (q : ℚ) : Prop := q.num.natAbs≤ M ∧ q.den≤ M







end Lax263307Proofs.NativeSignedArithmetic

end

-- Solutions.RAM_Lax263307Proofs_NativeEncodedLP
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

namespace Lax263307Proofs.NativeEncodedLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.RegisteredLP

/-- A canonical solver contract retaining the exact byte-level witness,
so native certificate readers and functional parsing use the same result. -/
def Encoded (solve : List ℕ → List ℕ) : Prop := ∀ (m n : ℕ) (P : Program ℚ m n),
  solve (encodeProgram P)=encodeCertificate (certificate solve P) ∧
    IsValidCertificate P (certificate solve P)







end Lax263307Proofs.NativeEncodedLP

end

-- Solutions.RAM_Lax263307_ExhaustiveTargets
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.ExhaustiveTargets


def candidates (n k : ℕ) : List (Finset (Fin n)) :=
  ((List.finRange n).sublistsLen k).map List.toFinset


def findIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) : Option (Finset (Fin n)) :=
  (candidates n k).find? fun I => decide (G.IsIndepSet (I : Set (Fin n)))


end Lax263307.ExhaustiveTargets

end

-- Solutions.RAM_Lax263307_TargetSearch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.TargetSearch


def search {n : ℕ} (attempt : ℕ → Option (Finset (Fin n))) :
    ℕ → Finset (Fin n) × ℕ
  | 0 => (∅, 0)
  | k + 1 => match attempt (k + 1) with
    | some I => (I, k + 1)
    | none => search attempt k


end Lax263307.TargetSearch

end

-- Solutions.RAM_Lax263307_RepeatedCutAccounting
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RepeatedCutAccounting

noncomputable def cost {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, x v

end Lax263307.RepeatedCutAccounting

end

-- Solutions.RAM_Lax263307_ComputedSeparators
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.ComputedSeparators

open EdgeSublinearSeparators (IsBalancedSeparator)
open Lax759944.RamPolytime (RamPolytime)
open SeparatorComponents (Partition)
open scoped NNRat
open VertexSplitting Lax455465.RationalEncoding

def decodeCut (n : ℕ) (words : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => words.getD v.val 0 = 1

def label {n : ℕ} (R : Finset (Fin n)) : Fin R.card ↪o Fin n :=
  R.orderEmbOfFin rfl

def restriction {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) :
    SimpleGraph (Fin R.card) := G.comap (label R)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Finset (Fin n)) :
    DecidableRel (restriction G R).Adj := inferInstanceAs (DecidableRel (G.comap (label R)).Adj)

def ratio (B n : ℕ) : ℚ := B * ((Nat.log2 (2 * n) : ℚ) + 1)
def scale (n ℓ k : ℕ) : ℚ := (ℓ : ℚ) * n ^ 2 / (3 * k)

def largeCapacity (B n r ℓ k : ℕ) : ℚ≥0 :=
  (Nat.ceil (ratio B n * (2 * r : ℕ) ^ 2 / scale n ℓ k) + 1 : ℕ)

def orient {n : ℕ} (A B : Finset (Fin n)) : Finset (Fin n) × Finset (Fin n) :=
  if B.card ≤ A.card then (A, B) else (B, A)

def step {n : ℕ} (solve : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (B ℓ k : ℕ) (R : Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  let I := splitInstance (restriction G R) (fun v => x (label R v))
    (largeCapacity B n R.card ℓ k)
  let U := decodeCut (2 * R.card) (solve (encodeInput .directed I))
  let shores := orient (leftShore U) (rightShore U)
  (shores.1.image (label R), shores.2.image (label R))

def cuts {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n)) :
    ℕ → Finset (Fin n) → List (Finset (Fin n) × Finset (Fin n))
  | 0, _ => []
  | fuel + 1, R =>
    if 3 * R.card ≤ 2 * n then []
    else let s := cut R
      s :: cuts cut fuel (s.1 \ s.2)

def separator {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  cs.foldr (fun s S => (s.1 ∩ s.2) ∪ S) ∅

def remaining {n : ℕ} (start : Finset (Fin n))
    (cs : List (Finset (Fin n) × Finset (Fin n))) : Finset (Fin n) :=
  if h : cs.length = 0 then start else
    let s := cs.get ⟨cs.length - 1, Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.zero_lt_one⟩
    s.1 \ s.2

def pieces {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) :
    Option (Fin cs.length) → Finset (Fin n)
  | none => remaining Finset.univ cs
  | some i => (cs.get i).2 \ (cs.get i).1

open GraphClasses
open Entropy RepeatedCutAccounting

end Lax263307.ComputedSeparators

end

-- Solutions.RAM_Lax263307_ComponentCutEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.ComponentCutEncoding

open LinearRelaxation


def coefficient {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ)
    (B : Coordinate n r) : ℤ :=
  (∑ v ∈ C, if insert v A = B.val then 1 else 0) -
    if A = B.val then (u : ℤ) else 0


noncomputable def evaluate {n r : ℕ} (a : Coordinate n r → ℤ)
    (z : MomentVector n r) : ℝ := ∑ B, (a B : ℝ) * z B


end Lax263307.ComponentCutEncoding

end

-- Solutions.RAM_Lax263307_ComputedRounding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.ComputedRounding

open SeparatorComponents (combine)

def target (δ cost : ℚ) : ℕ := ⌊(1 - δ) * cost⌋₊ + 1

def answer {n : ℕ} {ι : Type} (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n))) (i : ι) : Option (Finset (Fin n)) :=
  if δ * k / (4 * n) < cost i then query i (target δ (cost i)) else some ∅

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (vertices : Finset (Fin n)) (bound : ℕ)

def collect {n : ℕ} {ι : Type} [Fintype ι] (order : List ι) (parts : ι → Finset (Fin n))
    (δ : ℚ) (k : ℕ) (cost : ι → ℚ) (query : ι → ℕ → Option (Finset (Fin n))) : Result n :=
  match order.find? (fun i => (answer δ k cost query i).isNone) with
  | some i => .cut (parts i) (target δ (cost i) - 1)
  | none => .found (combine (fun i => (answer δ k cost query i).getD ∅))

open LinearRelaxation SeparatorComponents
open ComponentCutEncoding

end Lax263307.ComputedRounding

end

-- Solutions.RAM_Lax263307_HeavyRationalConditioning
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.HeavyRationalConditioning

open LinearRelaxation Entropy RationalConditioning

def rationalFloor (n p : ℕ) : ℚ := 1 / (2 * (n : ℚ) * p * ((Nat.log2 n : ℚ) + 1))

def HeavyPasses {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Prop :=
  Passes G k p y A ∧ rationalFloor n p ^ r ≤ rationalValue y A

instance {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) : Decidable (HeavyPasses G k p y A) :=
  inferInstanceAs (Decidable (Passes G k p y A ∧ rationalFloor n p ^ r ≤ rationalValue y A))

def findHeavyConditioning {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) : Option (Finset (Fin n)) :=
  (candidates n r).find? fun A => decide (HeavyPasses G k p y A)

end Lax263307.HeavyRationalConditioning

end

-- Solutions.RAM_Lax263307_MomentLP
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.MomentLP


open LinearRelaxation CoordinateCatalog
open Lax109476.LinearProgram Lax109476.RationalCertificates

abbrev dimension (n r : ℕ) : ℕ := (catalog n r).length
abbrev Index (n r : ℕ) := Fin (dimension n r)


abbrev rowCount (n r : ℕ) : ℕ :=
  let N := dimension n r
  2 + (N + (N + (N * n + (N + N))))

def decode {K : Type} {n r : ℕ} (x : Index n r → K) : Coordinate n r → K :=
  fun A => x ((indexing n r).symm A)

def encode {K : Type} {n r : ℕ} (y : Coordinate n r → K) : Index n r → K :=
  fun j => y (indexing n r j)

def singleRow {n r : ℕ} (A : Finset (Fin n)) (j : Index n r) : ℚ :=
  if A = (indexing n r j).val then 1 else 0

def monotoneRow {n r : ℕ} (A : Finset (Fin n)) (v : Fin n) (j : Index n r) : ℚ :=
  singleRow (insert v A) j - singleRow A j

def massRow {n r : ℕ} (A : Finset (Fin n)) (k : ℕ) (j : Index n r) : ℚ :=
  (∑ v, singleRow (insert v A) j) - (k : ℚ) * singleRow A j

def program {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    Program ℚ (rowCount n r) (dimension n r) where
  A := Fin.addCases
    (fun i : Fin 2 => fun j => if i = 0 then singleRow ∅ j else -singleRow ∅ j)
    (Fin.addCases
      (fun i : Index n r => singleRow (indexing n r i).val)
      (Fin.addCases
        (fun i : Index n r => fun j =>
          if G.IsIndepSet ((indexing n r i).val : Set (Fin n)) then 0 else singleRow (indexing n r i).val j)
        (Fin.addCases
          (fun i : Fin (dimension n r * n) =>
            let uv := finProdFinEquiv.symm i
            if (indexing n r uv.1).val.card ≤ r + 1 then
              monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0)
          (Fin.addCases
            (fun i : Index n r =>
              if (indexing n r i).val.card ≤ r + 1 then massRow (indexing n r i).val k else fun _ => 0)
            (fun i : Index n r => fun j =>
              if (indexing n r i).val.card ≤ r + 1 then -massRow (indexing n r i).val k j else 0)))))
  b := Fin.addCases (fun i : Fin 2 => if i = 0 then 1 else -1)
    (Fin.addCases (fun _ : Index n r => 1) (fun _ => 0))
  c := fun _ => 0

end Lax263307.MomentLP

end

-- Solutions.RAM_Lax263307_BufferedEllipsoid
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.BufferedEllipsoid

open Matrix

def scale {K : Type} [Field K] {n : ℕ} (z : Fin n → K) : Fin n → K := fun i => z i / (4 * (n : K))

end Lax263307.BufferedEllipsoid

end

-- Solutions.RAM_Lax263307_RoundedOracleSearch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RoundedOracleSearch

open BufferedEllipsoid (scale)
open Lax109476.RationalEncoding (encodeRational)
open Lax759944.BinaryWordEncoding (bitSize)
open Matrix

abbrev State (n : ℕ) := Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)

inductive Reply (n : ℕ) (Result : Type)
  | found (answer : Result)
  | reject
  | cut (normal : Fin n → ℤ)

def rationalNormal {n : ℕ} (a : Fin n → ℤ) : Fin n → ℚ := fun i => a i

def roundDown (q : ℚ) (D : ℕ) : ℚ := (Int.floor (q * D) : ℚ) / D

def sqrtUpper (q : ℚ) (D : ℕ) : ℚ :=
  ((Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) + 1 : ℕ) : ℚ) / D

def cutShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) •
    (A - (2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

def grid (n k : ℕ) : ℕ := 2 ^ ((2 * k + 2) + (2 * n + 4) + n + 3)

def cached {n : ℕ} (state : State n) : State n :=
  let rows : Vector (Vector ℚ n) n := Vector.ofFn (fun i => Vector.ofFn (state.1 i))
  let center : Vector ℚ n := Vector.ofFn state.2
  ((fun i j => (rows.get i).get j), fun i => center.get i)

def update {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) : State n :=
  let a := rationalNormal a
  let D := grid n k
  let η : ℚ := 1 / (2 : ℚ) ^ (2 * n + 4)
  let shape := ((1 + η) ^ 2) •
    ((Matrix.of fun i j => roundDown (cutShape state.1 a i j) D) + ((n : ℚ) / D) • 1)
  let center := fun i => roundDown
    (state.2 i - (1 / (((n : ℚ) + 1) * sqrtUpper (a ⬝ᵥ (state.1 *ᵥ a)) D)) *
      (state.1 *ᵥ a) i) D
  cached (shape, center)

def fallback {n : ℕ} : Fin n → ℤ := fun i => if i.val = 0 then 1 else 0

def selectedNormal {n : ℕ} {Result : Type} : Reply n Result → Fin n → ℤ
  | .cut a => a
  | _ => fallback

def trajectory {n : ℕ} {Result : Type} (oracle : ℕ → (Fin n → ℚ) → Reply n Result) :
    ℕ → State n
  | 0 => (1, 0)
  | k + 1 =>
    let old := trajectory oracle k
    update k old (selectedNormal (oracle k old.2))



def scan {n : ℕ} {Result : Type} (oracle : ℕ → (Fin n → ℚ) → Reply n Result) :
    ℕ → ℕ → State n → Option Result
  | _, 0, _ => none
  | k, count + 1, state =>
    match oracle k state.2 with
    | .found answer => some answer
    | .reject => none
    | .cut a => scan oracle (k + 1) count (update k state a)

def steps (n B : ℕ) : ℕ := 4 * (n + 1) * (B * n + 1)

def search {n : ℕ} {Result : Type} (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (B : ℕ) : Option Result := scan oracle 0 (steps n B) (1, 0)

end Lax263307.RoundedOracleSearch

end

-- Solutions.RAM_Lax263307_AlgorithmParameters
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.AlgorithmParameters


open MomentLP (dimension)
open RoundedOracleSearch (steps)
def logarithm (n : ℕ) : ℕ := Nat.log2 (2 * n) + 1
def load (B n D : ℕ) : ℕ := 12 * B * D * logarithm n
def targetThreshold (a K B n D : ℕ) : ℕ := K * (load B n D + 1) ^ (4 * a + 2)
def sparsity (a K B n D : ℕ) : ℕ := 2 * targetThreshold a K B n D
def level (a K B n D : ℕ) : ℕ := sparsity a K B n D * (Nat.log2 n + 1)
def cutoff (a K B n D : ℕ) : ℕ := max (targetThreshold a K B n D) (level a K B n D)
def floorDenominator (a K B n D : ℕ) : ℕ :=
  2 * n * sparsity a K B n D * (Nat.log2 n + 1)
def momentFloor (a K B n D : ℕ) : ℚ :=
  1 / (floorDenominator a K B n D : ℚ) ^ level a K B n D
def radiusDenominator (a K B n D : ℕ) : ℕ :=
  256 * dimension n (level a K B n D) * n ^ 2 * D ^ 2 *
    floorDenominator a K B n D ^ level a K B n D
def precision (a K B n D : ℕ) : ℕ := radiusDenominator a K B n D + 2
def iterations (a K B n D : ℕ) : ℕ :=
  steps (dimension n (level a K B n D)) (precision a K B n D)

end Lax263307.AlgorithmParameters

end

-- Solutions.RAM_Lax263307_NearOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The recursive oracle near the moment relaxation
type: definition
---
The oracle searches for a heavy conditioning set, computes separators,
and queries the resulting parts. Its possible outputs are an independent
set, a component cut, or rejection.

The correctness predicate requires an approximation guarantee for a found
set and a valid inequality with a quantitative gap for a returned cut.
It rules out rejection under the oracle's hypotheses.

# Formalization notes

`ChildCorrect` specifies the recursive answers on balanced parts.
`Correct` specifies the corresponding answer or cut at the current level.
The function itself is computable for the supplied flow solver and child
queries.
-/

namespace Lax263307.NearOracle

open AlgorithmParameters (level load sparsity)
open ComponentCutEncoding (coefficient evaluate)
open ComputedRounding (collect)
open ComputedSeparators (cuts pieces step)
open HeavyRationalConditioning (findHeavyConditioning)
open scoped NNRat
open LinearRelaxation RationalConditioning

def costs {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n) : ℚ≥0 :=
  ⟨max 0 (rationalValue y (insert v A) / rationalValue y A), le_max_left _ _⟩

def order (q : ℕ) : List (Option (Fin q)) := none :: (List.finRange q).map some

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (conditioning vertices : Finset (Fin n)) (bound : ℕ)
  | reject

def run {n : ℕ} (flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (y : RationalVector n (level a K B n D))
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Result n :=
  let p := sparsity a K B n D
  match findHeavyConditioning G k p y with
  | none => .reject
  | some A =>
    let x := costs y A
    let cs := cuts
      (step flow G x B (load B n D) k) n Finset.univ
    let parts := pieces cs
    let c : Option (Fin cs.length) → ℚ := fun i => ∑ v ∈ parts i, (x v : ℚ)
    match collect (order cs.length) parts (1 / D) k c
      (fun i t => child (parts i) t) with
    | .found I => .found I
    | .cut C u => .cut A C u

def ChildCorrect {n : ℕ} (G : SimpleGraph (Fin n)) (D h : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Prop :=
  ∀ C : Finset (Fin n), 3 * C.card ≤ 2 * n → ∀ t : ℕ,
    match child C t with
    | some I => I ⊆ C ∧ G.IsIndepSet (I : Set (Fin n)) ∧
        (1 - 4 * (1 / (D : ℝ))) ^ h * (t : ℝ) ≤ I.card
    | none => IsIndependenceBound G C (t - 1)



end Lax263307.NearOracle

end

-- Solutions.RAM_Lax263307_DistanceProjection
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.DistanceProjection

open Lax109476.LinearProgram


def distanceProgram {K : Type} [Ring K] {m n : ℕ} (P : Program K m n) (center : Fin n → K) :
    Program K (m + (n + n)) (n + 1) where
  A := Fin.addCases
    (fun i => Fin.addCases (P.A i) (fun _ => 0))
    (Fin.addCases
      (fun i => Fin.addCases (fun j => if i = j then 1 else 0) (fun _ => -1))
      (fun i => Fin.addCases (fun j => if i = j then -1 else 0) (fun _ => -1)))
  b := Fin.addCases P.b (Fin.addCases center (fun i => -center i))
  c := Fin.addCases (fun _ => 0) (fun _ => -1)

def point {K : Type} {n : ℕ} (z : Fin (n + 1) → K) (j : Fin n) : K := z (Fin.castAdd 1 j)
def distance {K : Type} {n : ℕ} (z : Fin (n + 1) → K) : K := z (Fin.natAdd n (0 : Fin 1))

def oldMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin m) : K :=
  dual (Fin.castAdd (n + n) i)
def plusMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  dual (Fin.natAdd m (Fin.castAdd n i))
def minusMultipliers {K : Type} {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  dual (Fin.natAdd m (Fin.natAdd n i))
def normal {K : Type} [Sub K] {m n : ℕ} (dual : Fin (m + (n + n)) → K) (i : Fin n) : K :=
  minusMultipliers dual i - plusMultipliers dual i

end Lax263307.DistanceProjection

end

-- Solutions.RAM_Lax263307_RationalProjection
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open DistanceProjection

inductive Outcome (n : ℕ)
  | near (point : Fin n → ℚ)
  | far (normal : Fin n → ℚ) (bound : ℚ)
  | reject


def classify {m n : ℕ} (P : Program ℚ m n) (ρ : ℚ) :
    Certificate (m + (n + n)) (n + 1) → Outcome n
  | .optimal z dual =>
    if distance z ≤ ρ then .near (point z)
    else .far (normal dual) (dualValue P (oldMultipliers dual))
  | .infeasible _ => .reject
  | .unbounded _ _ => .reject



end Lax263307.RationalProjection

end

-- Solutions.RAM_Lax263307_RationalCutBuffer
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.RationalCutBuffer

open BufferedEllipsoid (scale)
open Matrix

def denominator {n : ℕ} (a : Fin n → ℚ) : ℕ := ∏ i, (a i).den

def integerNormal {n : ℕ} (a : Fin n → ℚ) (i : Fin n) : ℤ :=
  (a i).num * (denominator a / (a i).den : ℕ)

end Lax263307.RationalCutBuffer

end

-- Solutions.RAM_Lax263307_ProjectedOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The projected round-or-cut search
type: definition
---
The oracle decodes an LP certificate and either rejects the relaxation,
returns a separating projection cut, or invokes the near-relaxation oracle.
A bounded rounded-ellipsoid search repeats this step.

The correctness predicates describe the approximation guarantee and the
protected region that every returned cut must preserve. A failed search
certifies that the independence number is below the requested target.

# Formalization notes

The definitions take the LP solver, flow solver, and recursive child queries
as arguments. Precision and iteration limits are explicit functions of the
class constants, graph order, and accuracy denominator.
-/

namespace Lax263307.ProjectedOracle

open BufferedEllipsoid (scale)
open ComponentCutEncoding (coefficient)
open DistanceProjection (distanceProgram)
open MomentLP (Index decode dimension encode program)
open RationalCutBuffer (integerNormal)
open RationalProjection (classify)
open RegisteredLP (certificate)
open RoundedOracleSearch (Reply rationalNormal)
open LinearRelaxation AlgorithmParameters

def tolerance (a K B n D : ℕ) : ℚ := momentFloor a K B n D / (32 * (n : ℚ)^2 * (D : ℚ)^2)

def raw {N : ℕ} (center : Fin N → ℚ) : Fin N → ℚ := fun i => 4 * (N : ℚ) * center i

def run {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n)))
    (center : Index n (level a K B n D) → ℚ) :
    Reply (dimension n (level a K B n D)) (Finset (Fin n)) :=
  let P := program G k (level a K B n D)
  match classify P (tolerance a K B n D)
    (certificate lp (distanceProgram P (raw center))) with
  | .reject => .reject
  | .far normal _ => .cut (integerNormal normal)
  | .near y =>
    match NearOracle.run flow a K B D G k (decode y) child with
    | .reject => .reject
    | .found I => .found I
    | .cut A C u => .cut (integerNormal
        (rationalNormal (encode (coefficient A C u))))

def Good {n : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧ (1 - 4 * (1 / (D : ℝ))) ^ (h+1) * (k : ℝ) ≤ I.card

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) (k h a K B D : ℕ)
    (center : Index n (level a K B n D) → ℚ) :
    Reply (dimension n (level a K B n D)) (Finset (Fin n)) → Prop
  | .found I => Good G k h D I
  | .reject => independentSetHull G k (level a K B n D) = ∅
  | .cut normal => (∃ i, normal i ≠ 0) ∧
    ∀ z ∈ independentSetHull G k (level a K B n D),
    ∀ e : Index n (level a K B n D) → ℝ,
    (∀ i, |e i| ≤ ((2 : ℝ) ^ precision a K B n D)⁻¹) →
      (fun i => (normal i : ℝ)) ⬝ᵥ
        (scale (encode z) + e - (fun i => (center i : ℝ))) ≤ 0

def search {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Option (Finset (Fin n)) :=
  RoundedOracleSearch.search (fun _ center => run lp flow a K B D G k child center)
    (precision a K B n D)



end Lax263307.ProjectedOracle

end

-- Solutions.RAM_Lax263307_RecursiveAlgorithm
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The recursive unweighted approximation algorithm
type: definition
---
The algorithm uses exhaustive search for small targets and projected
round-or-cut search for larger targets. Recursive calls work on canonically
labeled balanced parts. A descending target search selects the final set.

# Formalization notes

The fuel parameter bounds recursion depth. `Correct` records the size
guarantee for a returned independent set and the upper bound certified by
failure. The accuracy denominator is
$4(\operatorname{depth}(n)+1)\lceil1/\varepsilon\rceil$.
-/

namespace Lax263307.RecursiveAlgorithm

open ExhaustiveTargets (findIndependentSet)
open RecursionDepth (depth)
open ComputedSeparators AlgorithmParameters

def attempt (lp flow : List ℕ → List ℕ) (a K B D : ℕ) (fuel : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Option (Finset (Fin n)) :=
  if k ≤ cutoff a K B n D ∨ n ≤ 1 then findIndependentSet G k
  else if n < k then none
  else match fuel with
    | 0 => none
    | fuel + 1 => ProjectedOracle.search lp flow a K B D G k
        (fun C t => (attempt lp flow a K B D fuel (restriction G C) t).map
          (fun I => I.image (label C)))
termination_by fuel

def solve {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) × ℕ :=
  TargetSearch.search (attempt lp flow a K B D (depth n) G) n



def accuracyDenominator (n : ℕ) (ε : ℚ) : ℕ :=
  4 * (depth n + 1) * ⌈ε⁻¹⌉₊

def independentSet {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ε : ℚ) : Finset (Fin n) :=
  (solve lp flow a K B (accuracyDenominator n ε) G).1

end Lax263307.RecursiveAlgorithm

end

-- Solutions.RAM_Lax455465Proofs_RamSparseMemory
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamSparseMemory

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

















def scanStep : Com :=
  .seq (.ite (.eq (.get "vm.addresses" (.var "lookup.i")) (.var "lookup.address"))
    (.assign "lookup.result" (.get "vm.values" (.var "lookup.i"))) .skip)
    (.assign "lookup.i" (.add (.var "lookup.i") (.lit 1)))





def lookup : Com := .seq (.assign "lookup.result" (.lit 0))
  (.seq (.assign "lookup.i" (.lit 0))
    (.while (.lt (.var "lookup.i") (.var "vm.count")) scanStep))





def put : Com := .seq
  (.store "vm.addresses" (.var "vm.count") (.var "put.address"))
  (.seq (.store "vm.values" (.var "vm.count") (.var "put.value"))
    (.assign "vm.count" (.add (.var "vm.count") (.lit 1))))



end Lax455465Proofs.RamSparseMemory

end

-- Solutions.RAM_Lax455465Proofs_RamWordOps
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamWordOps

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Virtual arithmetic wraps at the chosen virtual modulus, independently
of the larger word size used to run the host program. -/
def reduce : Com := .assign "vm.result" (.sub (.var "vm.result")
  (.mul (.div (.var "vm.result") (.var "vm.modulus")) (.var "vm.modulus")))



def binary (op : Bop) : Com :=
  .seq (.assign "vm.result" (.bin op (.var "vm.left") (.var "vm.right"))) reduce



/-- Shifts by at least the virtual word length return zero. The host never
constructs the otherwise exponentially large intermediate. -/
def shift : Com := .ite (.lt (.var "vm.right") (.var "vm.width"))
  (binary .shiftl) (.assign "vm.result" (.lit 0))



/-- Bitwise complement is computed using the virtual mask. -/
def complement : Com := .assign "vm.result"
  (.sub (.sub (.var "vm.modulus") (.lit 1)) (.var "vm.left"))





def modulus : Com := .assign "vm.modulus" (.shiftl (.lit 1) (.var "vm.width"))



end Lax455465Proofs.RamWordOps

end

-- Solutions.RAM_Lax455465Proofs_RamSparseRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamSparseRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamSparseMemory



def read (target : String) (address : Expr) : Com :=
  .seq (.assign "lookup.address" address)
    (.seq lookup (.assign target (.var "lookup.result")))





def write : Com := .seq (.assign "put.address" (.var "vm.target"))
  (.seq (.assign "put.value" (.var "vm.result")) put)





end Lax455465Proofs.RamSparseRead

end

-- Solutions.RAM_Lax455465Proofs_RamVirtualProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVirtualProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Reduction to the chosen virtual word width uses native division and
truncated subtraction, rather than the host's implicit word modulus. -/
def remainder (e : Expr) : Expr := .sub e
  (.mul (.div e (.var "vm.modulus")) (.var "vm.modulus"))



def increment : Com := .assign "vm.pc" (.add (.var "vm.pc") (.lit 1))

def writeBack (target value : Expr) : Com := .seq
  (.assign "vm.target" (remainder target))
  (.seq (.assign "vm.result" (remainder value))
    (.seq RamSparseRead.write increment))

def operands (left right : ℕ) (body : Com) : Com := .seq
  (RamSparseRead.read "vm.left" (remainder (.lit left)))
  (.seq (RamSparseRead.read "vm.right" (remainder (.lit right))) body)

def binary (op : Bop) (target left right : ℕ) : Com := operands left right
  (.seq (RamWordOps.binary op) (writeBack (.lit target) (.var "vm.result")))

def stop : Com := .assign "vm.running" (.lit 0)

/-- A fixed native command for each virtual instruction. Virtual input and
output occupy separate host buffers; their tape operations do not consume
the host input or prematurely emit an LP certificate as the LR output. -/
def instruction : Lax808846.Ram.Instr → Com
  | .set a value => writeBack (.lit a) (.lit value)
  | .load a b => .seq (RamSparseRead.read "vm.left" (remainder (.lit b)))
      (.seq (RamSparseRead.read "vm.result" (remainder (.var "vm.left")))
        (writeBack (.lit a) (.var "vm.result")))
  | .store a b => .seq (RamSparseRead.read "vm.target" (remainder (.lit a)))
      (.seq (RamSparseRead.read "vm.result" (remainder (.lit b)))
        (writeBack (.var "vm.target") (.var "vm.result")))
  | .add a b c => binary .add a b c
  | .sub a b c => binary .sub a b c
  | .mul a b c => binary .mul a b c
  | .div a b c => binary .div a b c
  | .and a b c => binary .and a b c
  | .shiftl a b c => operands b c
      (.seq RamWordOps.shift (writeBack (.lit a) (.var "vm.result")))
  | .not a b => .seq (RamSparseRead.read "vm.left" (remainder (.lit b)))
      (.seq RamWordOps.complement (writeBack (.lit a) (.var "vm.result")))
  | .jump label => .assign "vm.pc" (.lit label)
  | .jzero a label => .seq (RamSparseRead.read "vm.left" (remainder (.lit a)))
      (.ite (.eq (.var "vm.left") (.lit 0)) (.assign "vm.pc" (.lit label)) increment)
  | .jeof label => .ite (.eq (.var "vm.cursor") (.var "vm.inputLength"))
      (.assign "vm.pc" (.lit label)) increment
  | .inputLength a => writeBack (.lit a) (.var "vm.inputLength")
  | .inputLoad a b => .seq (RamSparseRead.read "vm.left" (remainder (.lit b)))
      (.seq (.ite (.lt (.var "vm.left") (.var "vm.inputLength"))
        (.assign "vm.result" (.get "vm.input" (.var "vm.left")))
        (.assign "vm.result" (.lit 0)))
        (writeBack (.lit a) (.var "vm.result")))
  | .halt => stop
  | .read a => .ite (.lt (.var "vm.cursor") (.var "vm.inputLength"))
      (.seq (.seq (.assign "vm.result" (.get "vm.input" (.var "vm.cursor")))
        (.assign "vm.cursor" (.add (.var "vm.cursor") (.lit 1))))
        (writeBack (.lit a) (.var "vm.result"))) stop
  | .write a => .seq (RamSparseRead.read "vm.left" (remainder (.lit a)))
      (.seq (.store "vm.output" (.var "vm.outputLength") (remainder (.var "vm.left")))
        (.seq (.assign "vm.outputLength" (.add (.var "vm.outputLength") (.lit 1))) increment))

/-- Program instructions are fixed at elaboration, and only the virtual
program counter is runtime data. Falling outside the source program halts. -/
def dispatch : List Lax808846.Ram.Instr → ℕ → Com
  | [], _ => stop
  | i :: rest, offset => .ite (.eq (.var "vm.pc") (.lit offset))
      (instruction i) (dispatch rest (offset + 1))

def initCommand : Com := .seq (.assign "vm.pc" (.lit 0))
  (.seq (.assign "vm.count" (.lit 0))
    (.seq (.assign "vm.cursor" (.lit 0))
      (.seq (.assign "vm.outputLength" (.lit 0)) (.assign "vm.running" (.lit 1)))))

/-- The one fixed native host command for a black-box registered RAM
program. It executes through separate virtual-memory and tape buffers. -/
def execute (p : Lax808846.Ram.Program) : Com :=
  .seq RamWordOps.modulus (.seq initCommand
    (.while (.lt (.lit 0) (.var "vm.running")) (dispatch p 0)))

end Lax455465Proofs.RamVirtualProgram

end

-- Solutions.RAM_Lax455465Proofs_RamVirtualState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVirtualState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualProgram

/-- Reserved arrays are represented by their initialized prefix, so stale
entries beyond the logical length cannot affect virtual execution. -/
def Prefix (words : List ℕ) (array : String) (σ : Env) : Prop :=
  ∀ i (hi : i < words.length), (σ.arrs array)[i]? = some words[i]













end Lax455465Proofs.RamVirtualState

end

-- Solutions.RAM_Lax455465Proofs_RamUnsignedBuffer
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamUnsignedBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def encode (qs : List ℚ≥0) : List ℕ := qs.flatMap encodeRational







def read (array index : String) : Com :=
  .seq (.assign "rat.n" (.get array (.mul (.lit 2) (.var index))))
    (.seq (.assign "rat.d" (.get array (.add (.mul (.lit 2) (.var index)) (.lit 1))))
      (.assign "rat.s" (.lit 0)))



end Lax455465Proofs.RamUnsignedBuffer

end

-- Solutions.RAM_Lax455465Proofs_DirectedFlowLP
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! The polynomial-size edge formulation used by the deterministic solver.
There is one concurrent-value variable and n⁴ commodity/arc variables.
Capacity rows and paired conservation rows give n² + 2n³ inequalities.
No enumeration of simple paths is used in this LP. -/

open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowLP

open Lax455465.RationalEncoding Lax109476.LinearProgram

abbrev Edge (n : ℕ) := Fin n × Fin n
abbrev CommodityArc (n : ℕ) := Edge n × Edge n
abbrev Balance (n : ℕ) := Edge n × Fin n
abbrev Variable (n : ℕ) := Fin 1 ⊕ CommodityArc n
abbrev Row (n : ℕ) := Edge n ⊕ (Fin 2 × Balance n)

def edgeIndex (n : ℕ) : Edge n ≃ Fin (n * n) := finProdFinEquiv

def arcIndex (n : ℕ) : CommodityArc n ≃ Fin ((n * n) * (n * n)) :=
  ((edgeIndex n).prodCongr (edgeIndex n)).trans finProdFinEquiv

def balanceIndex (n : ℕ) : Balance n ≃ Fin ((n * n) * n) :=
  ((edgeIndex n).prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

def variableIndex (n : ℕ) : Variable n ≃ Fin (1 + (n * n) * (n * n)) :=
  ((Equiv.refl (Fin 1)).sumCongr (arcIndex n)).trans finSumFinEquiv

def rowIndex (n : ℕ) : Row n ≃ Fin (n * n + 2 * ((n * n) * n)) :=
  ((edgeIndex n).sumCongr
    (((Equiv.refl (Fin 2)).prodCongr (balanceIndex n)).trans finProdFinEquiv)).trans
      finSumFinEquiv

/-- The signed demand divergence at one vertex. Equal endpoints have zero demand. -/
def divergence {n : ℕ} (I : RationalInstance n) (s t u : Fin n) : ℚ :=
  if s = t then 0 else
    (if u = s then (I.weight s : ℚ) * I.weight t else 0) -
    (if u = t then (I.weight s : ℚ) * I.weight t else 0)

/-- One conservation equation, written as a linear expression equal to zero. -/
def balanceCoefficient {n : ℕ} (I : RationalInstance n)
    (b : Balance n) : Variable n → ℚ
  | .inl _ => - divergence I b.1.1 b.1.2 b.2
  | .inr a => if a.1 = b.1 then
      (if a.2.1 = b.2 then 1 else 0) - (if a.2.2 = b.2 then 1 else 0)
    else 0

/-- Capacity rows followed by both signs of every conservation equation. -/
def coefficient {n : ℕ} (I : RationalInstance n) : Row n → Variable n → ℚ
  | .inl _, .inl _ => 0
  | .inl e, .inr a => if a.2 = e then 1 else 0
  | .inr (sign, b), v =>
      if sign = 0 then balanceCoefficient I b v else -balanceCoefficient I b v

def rowBound {n : ℕ} (I : RationalInstance n) : Row n → ℚ
  | .inl e => I.capacity e.1 e.2
  | .inr _ => 0

def objective {n : ℕ} : Variable n → ℚ
  | .inl _ => 1
  | .inr _ => 0

/-- Dense rational LP with a polynomial number of rows and variables. -/
def program {n : ℕ} (I : RationalInstance n) :
    Program ℚ (n * n + 2 * ((n * n) * n)) (1 + (n * n) * (n * n)) where
  A i j := coefficient I ((rowIndex n).symm i) ((variableIndex n).symm j)
  b i := rowBound I ((rowIndex n).symm i)
  c j := objective ((variableIndex n).symm j)





















end Lax455465Proofs.DirectedFlowLP

end

-- Solutions.RAM_Lax455465Proofs_RamFractionPrimitives
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFractionPrimitives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational

def zero : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 0)) (.assign "rat.d" (.lit 1)))
def one : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 1)))
def negativeOne : Com := .seq (.assign "rat.s" (.lit 1))
  (.seq (.assign "rat.n" (.lit 1)) (.assign "rat.d" (.lit 1)))
def negate : Com := .assign "rat.s" (.sub (.lit 1) (.var "rat.s"))









end Lax455465Proofs.RamFractionPrimitives

end

-- Solutions.RAM_Lax455465Proofs_RamWordBuffer
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamWordBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

/-- Append to the initialized prefix of a reserved native array. -/
def append (array cursor : String) (value : Expr) : Com :=
  .seq (.store array (.var cursor) value)
    (.assign cursor (.add (.var cursor) (.lit 1)))





end Lax455465Proofs.RamWordBuffer

end

-- Solutions.RAM_Lax455465Proofs_RamFractionEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFractionEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState



def sign : Com := .ite (.eq (.var "rat.n") (.lit 0))
  (.assign "emit.s" (.lit 0)) (.assign "emit.s" (.var "rat.s"))



def emit : Com := .seq sign (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "emit.s"))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "rat.n"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "rat.d"))))



end Lax455465Proofs.RamFractionEncoding

end

-- Solutions.RAM_Lax455465Proofs_RamVectorEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVectorEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding





def step (index : String) (body : Com) : Com := .seq body
  (.seq RamFractionEncoding.emit (.assign index (.add (.var index) (.lit 1))))

def command (index limit : String) (body : Com) : Com :=
  .seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index body))





end Lax455465Proofs.RamVectorEncoding

end

-- Solutions.RAM_Lax455465Proofs_LpInputSize
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.LpInputSize

open Lax455465.RationalEncoding Lax455465.ProductNetwork
open Lax759944.BinaryWordEncoding DirectedFlowLP
open scoped NNRat

def Height (M : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ M ∧ q.den ≤ M











































end Lax455465Proofs.LpInputSize

end

-- Solutions.RAM_Lax455465Proofs_RamVirtualConstants
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVirtualConstants

open Lax808846.Ram

/-- Fixed literal allowance is part of the fixed program, never a
runtime input or an initialized-memory assumption. -/
def literalBound : Instr → ℕ
  | .set a v => max a v + 2
  | .load a b | .store a b | .not a b | .inputLoad a b => max a b + 2
  | .add a b c | .sub a b c | .mul a b c | .div a b c | .and a b c | .shiftl a b c =>
      max a (max b c) + 2
  | .jzero a l => max a l + 2
  | .jump l | .jeof l => l + 2
  | .inputLength a | .read a | .write a => a + 2
  | .halt => 2



def allowance (p : Program) : ℕ := p.length + 2 + (p.map literalBound).sum





end Lax455465Proofs.RamVirtualConstants

end

-- Solutions.RAM_Lax455465Proofs_RamBitSize
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBitSize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def wordStep : Com := .seq (.assign "size.value" (.div (.var "size.value") (.lit 2)))
  (.assign "size.count" (.add (.var "size.count") (.lit 1)))

def wordLoop : Com := .while (.lt (.lit 0) (.var "size.value")) wordStep

def word : Com := .seq (.assign "size.count" (.lit 0)) wordLoop







open RamVirtualState Lax759944.BinaryWordEncoding



def arrayStep (data : String) : Com := .seq (.assign "size.value" (.get data (.var "size.i")))
  (.seq word (.seq (.assign "size.total" (.add (.add (.var "size.total") (.var "size.count")) (.lit 1)))
    (.assign "size.i" (.add (.var "size.i") (.lit 1)))))



def array (data lengthVar : String) : Com := .seq (.assign "size.total" (.lit 0))
  (.seq (.assign "size.i" (.lit 0)) (.while (.lt (.var "size.i") (.var lengthVar)) (arrayStep data)))



end Lax455465Proofs.RamBitSize

end

-- Solutions.RAM_Lax455465Proofs_RamPolynomial
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The list is fixed program data, with coefficients in increasing degree. -/
def value : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: rest, x => a + x * value rest x

/-- Horner evaluation is compiled entirely into native integer operations. -/
def command : List ℕ → Com
  | [] => .assign "poly.value" (.lit 0)
  | a :: rest => .seq (command rest)
      (.assign "poly.value" (.add (.lit a) (.mul (.var "poly.argument") (.var "poly.value"))))















end Lax455465Proofs.RamPolynomial

end

-- Solutions.RAM_Lax455465Proofs_RamLpInputFrame
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamLpInputFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def step : Com := .seq
  (RamWordBuffer.append "vm.input" "vm.inputLength" (.get "lp.word" (.var "frame.i")))
  (.assign "frame.i" (.add (.var "frame.i") (.lit 1)))






/-- The virtual solver receives exactly the physical length-prefixed LP
word, copied from the constructed LP buffer without consuming host input. -/
def command : Com := .seq (.assign "vm.inputLength" (.lit 0))
  (.seq (RamWordBuffer.append "vm.input" "vm.inputLength" (.var "lp.position"))
    (.seq (.assign "frame.i" (.lit 0)) (.while (.lt (.var "frame.i") (.var "lp.position")) step)))



end Lax455465Proofs.RamLpInputFrame

end

-- Solutions.RAM_Lax455465Proofs_RamLpPrepare
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamLpPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax759944.BinaryWordEncoding

/-- The virtual width is computed from the LP word's actual binary size.
The host's word width is never queried or used as the virtual width. -/
def command (coefficients : List ℕ) : Com := .seq (RamBitSize.array "lp.word" "lp.position")
  (.seq (.assign "poly.argument" (.var "size.total"))
    (.seq (RamPolynomial.command coefficients)
      (.seq (.assign "vm.width" (.var "poly.value")) RamLpInputFrame.command)))



end Lax455465Proofs.RamLpPrepare

end

-- Solutions.RAM_Lax455465Proofs_RamGraphHeader
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamGraphHeader

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork

def tag (kind : EdgeKind) : ℕ := match kind with | .undirected => 0 | .directed => 1





end Lax455465Proofs.RamGraphHeader

end

-- Solutions.RAM_Lax455465Proofs_RamUnsignedEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamUnsignedEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def command (array cursor : String) : Com := .seq (RamWordBuffer.append array cursor (.var "rat.n"))
  (RamWordBuffer.append array cursor (.var "rat.d"))



end Lax455465Proofs.RamUnsignedEncoding

end

-- Solutions.RAM_Lax455465Proofs_RamInputCopy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamInputCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def copyStep : Com := .seq (.read "input.word")
  (.seq (.store "input.data" (.var "input.i") (.var "input.word"))
    (.assign "input.i" (.add (.var "input.i") (.lit 1))))













end Lax455465Proofs.RamInputCopy

end

-- Solutions.RAM_Lax455465Proofs_RamOptimalDecode
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamOptimalDecode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax109476.RationalEncoding Lax109476.RationalCertificates
open scoped NNRat

def vector {k : ℕ} (x : Fin k → ℚ) (hx : ∀ i, 0 ≤ x i) : List ℚ≥0 :=
  List.ofFn fun i => (⟨x i,hx i⟩ : ℚ≥0)











end Lax455465Proofs.RamOptimalDecode

end

-- Solutions.RAM_Lax455465Proofs_RamUnsignedVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamUnsignedVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat

def step (index array cursor : String) (body : Com) : Com := .seq body
  (.seq (RamUnsignedEncoding.command array cursor) (.assign index (.add (.var index) (.lit 1))))

def command (index limit array cursor : String) (body : Com) : Com :=
  .seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index array cursor body))





end Lax455465Proofs.RamUnsignedVector

end

-- Solutions.RAM_Lax455465Proofs_DirectedFlowDual
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators NNRat

namespace Lax455465Proofs.DirectedFlowDual

open Lax455465.RationalEncoding Lax455465Proofs.DirectedFlowLP Lax109476.LinearProgram

/-- The multiplier on one arc capacity constraint is its dual length. -/
def length {n : ℕ} (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ)
    (u v : Fin n) : ℚ := y (rowIndex n (.inl (u, v)))











end Lax455465Proofs.DirectedFlowDual

end

-- Solutions.RAM_Lax455465Proofs_RationalDistances
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! Exact min-plus shortest distances. The algorithm has n pivots, each
updating n² rational coordinates, and does not enumerate paths. -/

open scoped BigOperators

namespace Lax455465Proofs.RationalDistances

abbrev Distance (n : ℕ) := Fin n → Fin n → ℚ





/-- One exact Floyd–Warshall pivot. -/
def step {n : ℕ} (d : Distance n) (p : Fin n) : Distance n :=
  fun u v => min (d u v) (d u p + d p v)

/-- Process a fixed list of pivots in order. -/
def iterate {n : ℕ} (d : Distance n) : List (Fin n) → Distance n
  | [] => d
  | p :: rest => iterate (step d p) rest

def solve {n : ℕ} (d : Distance n) : Distance n := iterate d (List.finRange n)

























/-- Diagonal arc multipliers carry no geometric information. -/
def zeroDiagonal {n : ℕ} (d : Distance n) : Distance n :=
  fun u v => if u = v then 0 else d u v







/-- Exact directed distances derived from a feasible flow-LP dual. -/
def dualDistance {n : ℕ}
    (y : Fin (n * n + 2 * ((n * n) * n)) → ℚ) : Distance n :=
  solve (zeroDiagonal (Lax455465Proofs.DirectedFlowDual.length y))





end Lax455465Proofs.RationalDistances

end

-- Solutions.RAM_Lax455465Proofs_MetricMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat

abbrev Matrix (n : ℕ) := Fin n → Fin n → ℚ≥0

def values {n : ℕ} (d : Matrix n) : List ℚ≥0 :=
  List.ofFn fun e : Fin (n*n) => d ((edgeIndex n).symm e).1 ((edgeIndex n).symm e).2







def rational {n : ℕ} (d : Matrix n) : RationalDistances.Distance n := fun u v => (d u v : ℚ)















end Lax455465Proofs.MetricMatrix


end

-- Solutions.RAM_Lax455465Proofs_RamDualDistancesInit
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat





def indices : Com := .seq (.assign "metric.u" (.div (.var "metric.entry") (.var "metric.n")))
  (.assign "metric.v" (.sub (.var "metric.entry") (.mul (.var "metric.u") (.var "metric.n"))))



















end Lax455465Proofs.RamDualDistancesInit

end

-- Solutions.RAM_Lax455465Proofs_RamUnsignedArithmetic
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamUnsignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def copy (side : String) : Com := .seq (.assign (side ++ ".s") (.lit 0))
  (.seq (.assign (side ++ ".n") (.var "rat.n")) (.assign (side ++ ".d") (.var "rat.d")))







end Lax455465Proofs.RamUnsignedArithmetic

end

-- Solutions.RAM_Lax455465Proofs_RamMinimum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMinimum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def left : Com := .seq (.assign "rat.s" (.var "left.s"))
  (.seq (.assign "rat.n" (.var "left.n")) (.assign "rat.d" (.var "left.d")))
def right : Com := .seq (.assign "rat.s" (.var "right.s"))
  (.seq (.assign "rat.n" (.var "right.n")) (.assign "rat.d" (.var "right.d")))

def command : Com := .seq RamComparison.compareFraction
  (.ite (.eq (.var "cmp.le") (.lit 1)) left right)







end Lax455465Proofs.RamMinimum

end

-- Solutions.RAM_Lax455465Proofs_RamArrayCopy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamArrayCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def step (source target : String) : Com :=
  .seq (.store target (.var "copy.i") (.get source (.var "copy.i")))
    (.assign "copy.i" (.add (.var "copy.i") (.lit 1)))

def command (source target count : String) : Com := .seq (.assign "copy.i" (.lit 0))
  (.while (.lt (.var "copy.i") (.var count)) (step source target))







end Lax455465Proofs.RamArrayCopy

end

-- Solutions.RAM_Lax455465Proofs_RamArrayProduct
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamArrayProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def command (leftArray rightArray : String) : Com := .seq (RamUnsignedBuffer.read leftArray "sum.i")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read rightArray "sum.i")
    (.seq (RamUnsignedArithmetic.copy "right") multiplyFraction)))



end Lax455465Proofs.RamArrayProduct

end

-- Solutions.RAM_Lax455465Proofs_RamUnsignedSum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamUnsignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

def load : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "fold.n")) (.assign "right.d" (.var "fold.d")))
def save : Com := .seq (.assign "fold.n" (.var "rat.n")) (.assign "fold.d" (.var "rat.d"))
def finish : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var "fold.n")) (.assign "rat.d" (.var "fold.d")))
def combine : Com := .seq (RamUnsignedArithmetic.copy "left") (.seq load (.seq addFraction save))
def init : Com := .seq (.assign "fold.n" (.lit 0)) (.assign "fold.d" (.lit 1))
def step (index : String) (body : Com) : Com := .seq body
  (.seq combine (.assign index (.add (.var index) (.lit 1))))
def command (index limit : String) (body : Com) : Com := .seq init
  (.seq (.seq (.assign index (.lit 0)) (.while (.lt (.var index) (.var limit)) (step index body))) finish)















end Lax455465Proofs.RamUnsignedSum

end

-- Solutions.RAM_Lax455465Proofs_RamProductSum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamProductSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def products (xs ys : List ℚ≥0) : List ℚ≥0 :=
  List.ofFn fun i : Fin xs.length => xs[i.val] * ys.getD i.val 0



def command (leftArray rightArray : String) : Com :=
  RamUnsignedSum.command "sum.i" "sum.count" (RamArrayProduct.command leftArray rightArray)





end Lax455465Proofs.RamProductSum

end

-- Solutions.RAM_Lax455465Proofs_RegionBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RegionBudget

/-- Number of rational grid cells needed by the deterministic search. Only
integer bit length is used by the algorithm. -/
def steps (p : ℕ) : ℕ := 2 * Nat.log2 p + 4







end Lax455465Proofs.RegionBudget

end

-- Solutions.RAM_Lax455465Proofs_RegionSelection
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionSelection











def support {n : ℕ} (weights : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < weights v













end Lax455465Proofs.RegionSelection

end

-- Solutions.RAM_Lax455465Proofs_MetricCostData
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.MetricCostData

open Lax455465.RationalEncoding DirectedFlowLP MetricMatrix
open scoped BigOperators NNRat

def cost {n : ℕ} (I : RationalInstance n) (d : Matrix n) : ℚ≥0 :=
  (RamProductSum.products (values I.capacity) (values d)).sum





end Lax455465Proofs.MetricCostData

end

-- Solutions.RAM_Lax455465Proofs_RamUnsignedScalar
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamUnsignedScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat

/-- Canonical unsigned rational saved in a named pair of native registers. -/
def Stored (name : String) (q : ℚ≥0) (σ : Env) : Prop :=
  σ.vars (name ++ ".n") = q.num ∧ σ.vars (name ++ ".d") = q.den

def load (name : String) : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var (name ++ ".n"))) (.assign "rat.d" (.var (name ++ ".d"))))
def save (name : String) : Com := .seq (.assign (name ++ ".n") (.var "rat.n"))
  (.assign (name ++ ".d") (.var "rat.d"))





end Lax455465Proofs.RamUnsignedScalar

end

-- Solutions.RAM_Lax455465Proofs_RamMetricCostResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMetricCostResources

open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding

noncomputable def heightBound (metricWord : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X+metricWord+Polynomial.C 1)*(Polynomial.X^2+Polynomial.C 1)











end Lax455465Proofs.RamMetricCostResources

end

-- Solutions.RAM_Lax455465Proofs_RamBooleanArithmetic
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBooleanArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat





def command (mode : Option Bool) : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (match mode with
    | none => .mul (.var "left.n") (.var "right.n")
    | some true => .mul (.var "left.n") (.sub (.lit 1) (.var "right.n"))
    | some false => .mul (.sub (.lit 1) (.var "left.n")) (.var "right.n")))
    (.assign "rat.d" (.lit 1)))



end Lax455465Proofs.RamBooleanArithmetic

end

-- Solutions.RAM_Lax455465Proofs_RamArraySum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamArraySum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat



def command (array : String) : Com :=
  RamUnsignedSum.command "sum.i" "sum.count" (RamUnsignedBuffer.read array "sum.i")



end Lax455465Proofs.RamArraySum

end

-- Solutions.RAM_Lax455465Proofs_RamMaskedSum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMaskedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat





def entry (source mask : String) : Com := .seq (RamUnsignedBuffer.read mask "sum.i")
  (.ite (.eq (.var "rat.n") (.lit 1)) (RamUnsignedBuffer.read source "sum.i") RamFractionPrimitives.zero)

def command (source mask : String) : Com := RamUnsignedSum.command "sum.i" "sum.count" (entry source mask)









end Lax455465Proofs.RamMaskedSum

end

-- Solutions.RAM_Lax455465Proofs_RamArcMask
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamArcMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat







def coefficient (mode : Option Bool) (source : String) : Com :=
  .seq RamDualDistancesInit.indices
    (.seq (RamUnsignedBuffer.read source "metric.u")
      (.seq (RamUnsignedArithmetic.copy "left")
        (.seq (RamUnsignedBuffer.read source "metric.v")
          (.seq (RamUnsignedArithmetic.copy "right") (RamBooleanArithmetic.command mode)))))



def command (mode : Option Bool) (source target : String) : Com :=
  .seq (.assign "mask.position" (.lit 0))
    (RamUnsignedVector.command "metric.entry" "metric.n2" target "mask.position" (coefficient mode source))



end Lax455465Proofs.RamArcMask

end

-- Solutions.RAM_Lax455465Proofs_RamBallMask
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBallMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat





def entry (array : String) : Com := .seq (load "region.radius")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read array "ball.i")
    (.seq (RamUnsignedArithmetic.copy "right") (.seq RamComparison.compareFraction
      (.ite (.eq (.var "cmp.le") (.lit 1)) RamFractionPrimitives.zero RamFractionPrimitives.one)))))



def command (source target : String) : Com := .seq (.assign "ball.pos" (.lit 0))
  (RamUnsignedVector.command "ball.i" "ball.count" target "ball.pos" (entry source))



end Lax455465Proofs.RamBallMask

end

-- Solutions.RAM_Lax455465Proofs_RamTruncatedSubtract
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamTruncatedSubtract

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational
open scoped NNRat



def difference : Com := .seq (.assign "right.s" (.lit 1)) addFraction

def command : Com := .seq RamComparison.compareFraction
  (.ite (.eq (.var "cmp.le") (.lit 1)) RamFractionPrimitives.zero difference)



end Lax455465Proofs.RamTruncatedSubtract

end

-- Solutions.RAM_Lax455465Proofs_RamScalarInverse
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamScalarInverse
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (name : String) : Com := .seq (load name)
  (.seq (RamUnsignedArithmetic.copy "left") invertFraction)



end Lax455465Proofs.RamScalarInverse

end

-- Solutions.RAM_Lax455465Proofs_RamScalarBinary
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamScalarBinary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName : String) (operation : Com) : Com :=
  .seq (load leftName) (.seq (RamUnsignedArithmetic.copy "left")
    (.seq (load rightName) (.seq (RamUnsignedArithmetic.copy "right") operation)))



end Lax455465Proofs.RamScalarBinary

end

-- Solutions.RAM_Lax455465Proofs_RamEdgePortion
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamEdgePortion

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat





def difference : Com := RamScalarBinary.command "portion.radius" "portion.base" RamTruncatedSubtract.command
def minimum : Com := RamScalarBinary.command "portion.length" "portion.diff" RamMinimum.command

def command : Com := .seq difference (.seq (save "portion.diff") minimum)



end Lax455465Proofs.RamEdgePortion

end

-- Solutions.RAM_Lax455465Proofs_RamArrayScalar
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamArrayScalar

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat

def command (array index name : String) : Com := .seq (RamUnsignedBuffer.read array index) (save name)



end Lax455465Proofs.RamArrayScalar

end

-- Solutions.RAM_Lax455465Proofs_RamRootDistances
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRootDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix DirectedFlowLP
open scoped NNRat





def array (outward : Bool) : String := if outward then "region.out" else "region.in"





def entry (outward : Bool) : Com := .seq
  (.assign "region.address" (if outward then .add (.mul (.var "region.root") (.var "metric.n")) (.var "region.i")
    else .add (.mul (.var "region.i") (.var "metric.n")) (.var "region.root")))
  (RamUnsignedBuffer.read "metric.old" "region.address")



def command (outward : Bool) : Com := .seq (.assign "region.pos" (.lit 0))
  (RamUnsignedVector.command "region.i" "metric.n" (array outward) "region.pos" (entry outward))



end Lax455465Proofs.RamRootDistances

end

-- Solutions.RAM_Lax455465Proofs_RamVolumeCoefficient
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVolumeCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix DirectedFlowLP
open scoped NNRat





def baseIndex (outward : Bool) : String := if outward then "metric.u" else "metric.v"

def command (outward : Bool) : Com := .seq (.assign "metric.entry" (.var "sum.i"))
  (.seq RamDualDistancesInit.indices
    (.seq (RamArrayScalar.command "metric.old" "sum.i" "portion.length")
      (.seq (RamArrayScalar.command (RamRootDistances.array outward) (baseIndex outward) "portion.base")
        (.seq RamEdgePortion.command
          (.seq (RamUnsignedArithmetic.copy "left")
            (.seq (RamUnsignedBuffer.read "region.capacities" "sum.i")
              (.seq (RamUnsignedArithmetic.copy "right") multiplyFraction)))))))



end Lax455465Proofs.RamVolumeCoefficient

end

-- Solutions.RAM_Lax455465Proofs_RamVolume
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamVolume

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix
open scoped NNRat





def setup : Com := .seq (load "region.radius") (.seq (save "portion.radius") (.assign "sum.count" (.var "metric.n2")))
def sum (outward : Bool) : Com := RamUnsignedSum.command "sum.i" "sum.count" (RamVolumeCoefficient.command outward)
def addition : Com := RamScalarBinary.command "round.seed" "volume.sum" addFraction

def command (outward : Bool) : Com := .seq setup (.seq (sum outward)
  (.seq (save "volume.sum") (.seq addition (save "region.volume"))))



end Lax455465Proofs.RamVolume

end

-- Solutions.RAM_Lax455465Proofs_RamBallMass
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBallMass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar
open scoped NNRat

def maskArray (outward : Bool) : String := if outward then "region.outMask" else "region.inMask"
def massName (outward : Bool) : String := if outward then "region.outMass" else "region.inMass"



def command (outward : Bool) : Com := .seq (.assign "ball.count" (.var "metric.n"))
  (.seq (RamBallMask.command (RamRootDistances.array outward) (maskArray outward))
    (.seq (.assign "sum.count" (.var "ball.count"))
      (.seq (RamMaskedSum.command "region.weights" (maskArray outward)) (save (massName outward)))))



end Lax455465Proofs.RamBallMass

end

-- Solutions.RAM_Lax455465Proofs_RamBoundary
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBoundary

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamUnsignedScalar MetricMatrix
open scoped NNRat



def command (outward : Bool) : Com :=
  .seq (RamArcMask.command (some outward) (RamBallMass.maskArray outward) "region.crossing")
    (.seq (.assign "sum.count" (.var "metric.n2"))
      (.seq (RamMaskedSum.command "region.capacities" "region.crossing") (save "region.boundary")))



end Lax455465Proofs.RamBoundary

end

-- Solutions.RAM_Lax455465Proofs_RamScalarReciprocal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamScalarReciprocal
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (source target : String) : Com := .seq (RamScalarInverse.command source) (save target)



end Lax455465Proofs.RamScalarReciprocal

end

-- Solutions.RAM_Lax455465Proofs_RamScalarProduct
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamScalarProduct
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName target : String) : Com :=
  .seq (RamScalarBinary.command leftName rightName multiplyFraction) (save target)



end Lax455465Proofs.RamScalarProduct

end

-- Solutions.RAM_Lax455465Proofs_RamNatScalar
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamNatScalar
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

def command (source target : String) : Com := .seq (.assign (target++".n") (.var source))
  (.assign (target++".d") (.lit 1))



end Lax455465Proofs.RamNatScalar

end

-- Solutions.RAM_Lax455465Proofs_RamRoundingConstants
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRoundingConstants
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat











def stage1 : Com := RamNatScalar.command "round.support" "round.supportRat"
def stage2 : Com := RamScalarReciprocal.command "round.supportRat" "round.inverseSupport"
def stage3 : Com := RamScalarProduct.command "round.cost" "round.inverseSupport" "round.seed"
def stage4 : Com := RamScalarProduct.command "round.total" "round.total" "round.square"
def stage5 : Com := Com.seq (.assign "round.four.n" (.lit 4)) (.assign "round.four.d" (.lit 1))
def stage6 : Com := RamScalarProduct.command "round.four" "round.square" "round.denominator"
def stage7 : Com := RamScalarReciprocal.command "round.denominator" "round.delta"
def stage8 : Com := RamNatScalar.command "round.steps" "round.stepsRat"
def stage9 : Com := RamScalarReciprocal.command "round.delta" "round.inverseDelta"
def stage10 : Com := RamScalarProduct.command "round.stepsRat" "round.inverseDelta" "round.slope"
def stage11 : Com := RamScalarReciprocal.command "round.stepsRat" "round.inverseSteps"
def stage12 : Com := RamScalarProduct.command "round.delta" "round.inverseSteps" "round.gridStep"

def command : Com := .seq stage1 (.seq stage2 (.seq stage3 (.seq stage4 (.seq stage5 (.seq stage6 (.seq stage7 (.seq stage8 (.seq stage9 (.seq stage10 (.seq stage11 (.seq stage12 (.skip))))))))))))



end Lax455465Proofs.RamRoundingConstants

end

-- Solutions.RAM_Lax455465Proofs_RamGridRadius
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamGridRadius

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational
open scoped NNRat

def indexOperand : Com := .seq (.assign "right.s" (.lit 0))
  (.seq (.assign "right.n" (.var "radius.i")) (.assign "right.d" (.lit 1)))

def command : Com := .seq (load "round.gridStep") (.seq (RamUnsignedArithmetic.copy "left")
  (.seq indexOperand multiplyFraction))



end Lax455465Proofs.RamGridRadius

end

-- Solutions.RAM_Lax455465Proofs_RamEventRadius
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamEventRadius

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational RamVirtualState
open scoped NNRat

def command (outward : Bool) : Com := .seq (load "round.delta")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read (RamRootDistances.array outward) "radius.v")
    (.seq (RamUnsignedArithmetic.copy "right") RamMinimum.command)))



end Lax455465Proofs.RamEventRadius

end

-- Solutions.RAM_Lax455465Proofs_RamRadiusCoefficient
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRadiusCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRational RamVirtualState
open scoped NNRat










def vertex : Com := .seq (.assign "radius.v" (.sub (.var "radius.i") (.var "radius.gridCount")))
  (.ite (.lt (.var "radius.v") (.var "metric.n")) (RamEventRadius.command true)
    (.seq (.assign "radius.v" (.sub (.var "radius.v") (.var "metric.n"))) (RamEventRadius.command false)))

def command : Com := .ite (.lt (.var "radius.i") (.var "radius.gridCount")) RamGridRadius.command vertex



end Lax455465Proofs.RamRadiusCoefficient

end

-- Solutions.RAM_Lax455465Proofs_RamRadiusCandidates
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRadiusCandidates

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState RamRational RamRadiusCoefficient
open scoped NNRat

def setup : Com := .seq (.assign "radius.gridCount" (.add (.var "round.steps") (.lit 1)))
  (.seq (.assign "radius.count" (.add (.var "radius.gridCount") (.mul (.lit 2) (.var "metric.n"))))
    (.assign "radius.position" (.lit 0)))

def command : Com := .seq setup (RamUnsignedVector.command "radius.i" "radius.count" "region.radii" "radius.position" RamRadiusCoefficient.command)



end Lax455465Proofs.RamRadiusCandidates

end

-- Solutions.RAM_Lax455465Proofs_RamFind
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning





def record : Com := .seq (.assign "find.found" (.lit 1)) (.assign "find.result" (.var "find.i"))
def process (body : Com) : Com := .ite (.eq (.var "find.found") (.lit 0))
  (.seq body (.ite (.eq (.var "find.ok") (.lit 1)) record .skip)) .skip

def step (body : Com) : Com := .seq (process body) (.assign "find.i" (.add (.var "find.i") (.lit 1)))
def init : Com := .seq (.assign "find.found" (.lit 0)) (.assign "find.result" (.lit 0))
def command (body : Com) : Com := .seq init (.seq (.assign "find.i" (.lit 0))
  (.while (.lt (.var "find.i") (.var "find.count")) (step body)))











end Lax455465Proofs.RamFind

end

-- Solutions.RAM_Lax455465Proofs_RamScalarComparison
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamScalarComparison

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName : String) : Com := .seq (load leftName)
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (load rightName)
    (.seq (RamUnsignedArithmetic.copy "right") RamComparison.compareFraction)))



end Lax455465Proofs.RamScalarComparison

end

-- Solutions.RAM_Lax455465Proofs_RamRegionDirection
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionDirection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

def command : Com := .seq (RamScalarComparison.command "region.outMass" "region.inMass")
  (.assign "region.outward" (.var "cmp.le"))



end Lax455465Proofs.RamRegionDirection

end

-- Solutions.RAM_Lax455465Proofs_RamRegionMasses
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionMasses

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamUnsignedScalar RamVirtualState
open scoped NNRat

def command : Com := .seq (RamBallMass.command true)
  (.seq (RamBallMass.command false) RamRegionDirection.command)



end Lax455465Proofs.RamRegionMasses

end

-- Solutions.RAM_Lax455465Proofs_RamRegionMeasures
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionMeasures

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def oriented (outward : Bool) : Com := .seq (RamBoundary.command outward) (RamVolume.command outward)
def command : Com := .ite (.eq (.var "region.outward") (.lit 1)) (oriented true) (oriented false)





end Lax455465Proofs.RamRegionMeasures

end

-- Solutions.RAM_Lax455465Proofs_RamRegionAcceptance
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionAcceptance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState RamRational
open scoped NNRat

def product : Com := RamScalarBinary.command "round.slope" "region.volume" multiplyFraction
def compare : Com := RamScalarComparison.command "region.boundary" "query.bound"
def record : Com := .ite (.eq (.var "region.radius.n") (.lit 0)) (.assign "find.ok" (.lit 0))
  (.assign "find.ok" (.var "cmp.le"))
def command : Com := .seq product (.seq (save "query.bound") (.seq compare record))



end Lax455465Proofs.RamRegionAcceptance

end

-- Solutions.RAM_Lax455465Proofs_RamRegionQuery
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096

namespace Lax455465Proofs.RamRegionQuery

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat

def command : Com := .seq RamRegionMasses.command (.seq RamRegionMeasures.command RamRegionAcceptance.command)



end Lax455465Proofs.RamRegionQuery

end

-- Solutions.RAM_Lax455465Proofs_RamRadiusSearch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRadiusSearch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat












def test : Com := .seq (RamArrayScalar.command "region.radii" "find.i" "region.radius") RamRegionQuery.command







def command : Com := RamFind.command test



end Lax455465Proofs.RamRadiusSearch

end

-- Solutions.RAM_Lax455465Proofs_RamSelectedRegion
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamSelectedRegion
open RamRadiusSearch Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open scoped NNRat

def restore : Com := .seq (.assign "find.i" (.var "find.result")) RamRadiusSearch.test

def command : Com := .seq RamRadiusSearch.command
  (.ite (.eq (.var "find.found") (.lit 1)) restore .skip)





end Lax455465Proofs.RamSelectedRegion

end

-- Solutions.RAM_Lax455465Proofs_RamRegionSetup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionSetup
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat














def setup : Com := .seq (.assign "find.count" (.var "radius.count"))
  (.seq (.assign "region.radius.n" (.lit 0)) (.assign "region.radius.d" (.lit 1)))
def command : Com := .seq (RamRootDistances.command true) (.seq (RamRootDistances.command false)
  (.seq RamRadiusCandidates.command (.seq setup RamSelectedRegion.command)))





end Lax455465Proofs.RamRegionSetup

end

-- Solutions.RAM_Lax455465Proofs_RamBooleanVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBooleanVector
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamBooleanArithmetic
open scoped NNRat



def entry (mode : Option Bool) (leftArray rightArray : String) : Com := .seq (RamUnsignedBuffer.read leftArray "mask.i")
  (.seq (RamUnsignedArithmetic.copy "left") (.seq (RamUnsignedBuffer.read rightArray "mask.i")
    (.seq (RamUnsignedArithmetic.copy "right") (RamBooleanArithmetic.command mode))))

def command (mode : Option Bool) (leftArray rightArray target : String) : Com := .seq (.assign "mask.pos" (.lit 0))
  (RamUnsignedVector.command "mask.i" "metric.n" target "mask.pos" (entry mode leftArray rightArray))





end Lax455465Proofs.RamBooleanVector

end

-- Solutions.RAM_Lax455465Proofs_RamActiveRemove
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamActiveRemove
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open scoped NNRat





def select : Com := .ite (.eq (.var "region.outward") (.lit 1))
  (RamBooleanVector.command (some true) "region.active" "region.outMask" "region.nextActive")
  (RamBooleanVector.command (some true) "region.active" "region.inMask" "region.nextActive")

def command : Com := .seq select (.seq (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
  (RamArrayCopy.command "region.nextActive" "region.active" "copy.count"))





end Lax455465Proofs.RamActiveRemove

end

-- Solutions.RAM_Lax455465Proofs_RamRegionRecord
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionRecord
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat










def command : Com := .seq (RamWordBuffer.append "region.history" "history.pos" (.var "region.root"))
  (.seq (RamWordBuffer.append "region.history" "history.pos" (.var "region.radius.n"))
    (.seq (RamWordBuffer.append "region.history" "history.pos" (.var "region.radius.d"))
      (RamWordBuffer.append "region.history" "history.pos" (.var "region.outward"))))



end Lax455465Proofs.RamRegionRecord

end

-- Solutions.RAM_Lax455465Proofs_RamSmallRegion
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamSmallRegion
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionRecord
open scoped NNRat










def command : Com := .seq RamRegionRecord.command RamActiveRemove.command



end Lax455465Proofs.RamSmallRegion

end

-- Solutions.RAM_Lax455465Proofs_RamRegionLarge
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionLarge
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat

def command : Com := .seq (RamScalarComparison.command "round.largeThreshold" "region.outMass")
  (.seq (.assign "large.out" (.var "cmp.le"))
    (.seq (RamScalarComparison.command "round.largeThreshold" "region.inMass")
      (.assign "region.large" (.mul (.var "large.out") (.var "cmp.le")))))





end Lax455465Proofs.RamRegionLarge

end

-- Solutions.RAM_Lax455465Proofs_RamRegionBranch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionBranch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RamRegionRecord
open scoped NNRat




def branch : Com := .ite (.eq (.var "region.large") (.lit 1))
  (.assign "region.phase" (.lit 1)) RamSmallRegion.command

def command : Com := .seq RamRegionLarge.command branch







end Lax455465Proofs.RamRegionBranch

end

-- Solutions.RAM_Lax455465Proofs_RamProductVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamProductVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat



def command (leftArray rightArray target : String) : Com := .seq (.assign "product.pos" (.lit 0))
  (RamUnsignedVector.command "sum.i" "product.count" target "product.pos" (RamArrayProduct.command leftArray rightArray))



end Lax455465Proofs.RamProductVector

end

-- Solutions.RAM_Lax455465Proofs_RamResidual
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamResidual

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix
open Lax455465.RationalEncoding
open scoped NNRat



def command : Com := .seq (RamArcMask.command none "region.active" "region.arcActive")
  (.seq (.assign "product.count" (.var "metric.n2"))
    (.seq (RamProductVector.command "flow.capacities" "region.arcActive" "region.capacities")
      (.seq (.assign "product.count" (.var "metric.n"))
        (RamProductVector.command "flow.weights" "region.active" "region.weights"))))



end Lax455465Proofs.RamResidual

end

-- Solutions.RAM_Lax455465Proofs_RamRegionInvariant
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat















def extents (n p : ℕ) : List (String×ℕ) := [
  ("region.arcActive",2*n*n),("region.capacities",2*n*n),("region.weights",2*n),
  ("region.out",2*n),("region.in",2*n),("region.radii",2*(RegionBudget.steps p+1+2*n)),
  ("region.outMask",2*n),("region.inMask",2*n),("region.crossing",2*n*n),
  ("region.active",2*n),("region.nextActive",2*n),("region.history",4*p+4)]

def Room (n p : ℕ) (σ : Env) : Prop := ∀ a count, (a,count)∈extents n p → count<(σ.arrs a).length



end Lax455465Proofs.RamRegionInvariant

end

-- Solutions.RAM_Lax455465Proofs_RamRoot
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRoot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def test : Com := .seq (RamUnsignedBuffer.read "region.weights" "find.i")
  (.ite (.eq (.var "rat.n") (.lit 0)) (.assign "find.ok" (.lit 0)) (.assign "find.ok" (.lit 1)))





def command : Com := .seq (.assign "find.count" (.var "metric.n")) (RamFind.command test)



end Lax455465Proofs.RamRoot

end

-- Solutions.RAM_Lax455465Proofs_RamLargeThreshold
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamLargeThreshold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar
open scoped NNRat


def factor : Com := .seq (.assign "round.largeFactor.n" (.lit 2)) (.assign "round.largeFactor.d" (.lit 3))
def command : Com := .seq factor (RamScalarProduct.command "round.total" "round.largeFactor" "round.largeThreshold")





end Lax455465Proofs.RamLargeThreshold

end

-- Solutions.RAM_Lax455465Proofs_RamActiveInit
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamActiveInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def command : Com := .seq (.assign "active.position" (.lit 0))
  (RamUnsignedVector.command "active.i" "metric.n" "region.active" "active.position" RamFractionPrimitives.one)



end Lax455465Proofs.RamActiveInit

end

-- Solutions.RAM_Lax455465Proofs_RamRegionLoop
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Save the runtime root before the candidate-radius finder reuses its
index registers. No root, radius or decision is supplied as extra input. -/
def foundRoot : Com := .seq (.assign "region.root" (.var "find.result"))
  (.seq RamRegionSetup.command (.ite (.eq (.var "find.found") (.lit 1))
    RamRegionBranch.command (.assign "region.phase" (.lit 3))))

def iteration : Com := .seq (.seq RamResidual.command RamRoot.command)
  (.ite (.eq (.var "find.found") (.lit 1)) foundRoot (.assign "region.phase" (.lit 2)))

/-- Phase zero grows another region, phase one freezes a large-ball witness,
phase two records exhaustion, and phase three records an unsuccessful search.
The latter is excluded on the mathematical algorithm's valid inputs. -/
def step : Com := .seq (.ite (.eq (.var "region.phase") (.lit 0)) iteration .skip)
  (.assign "loop.i" (.add (.var "loop.i") (.lit 1)))

/-- A fixed native loop takes at most the original positive-support budget
of active iterations, with one final exhaustion check. It recomputes every
residual array from the original input rather than multiplying old rationals. -/
def command : Com := .seq RamLargeThreshold.command (.seq RamActiveInit.command
  (.seq (.assign "history.pos" (.lit 0)) (.seq (.assign "region.phase" (.lit 0))
    (.seq (.assign "loop.limit" (.add (.var "round.support") (.lit 1)))
      (.seq (.assign "loop.i" (.lit 0))
        (.while (.lt (.var "loop.i") (.var "loop.limit")) step))))))

end Lax455465Proofs.RamRegionLoop

end

-- Solutions.RAM_Lax455465Proofs_RamSupport
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamSupport
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

def inspect : Com := .seq (RamUnsignedBuffer.read "flow.weights" "support.i")
  (.ite (.eq (.var "rat.n") (.lit 0)) .skip
    (.assign "round.support" (.add (.var "round.support") (.lit 1))))
def step : Com := .seq inspect (.assign "support.i" (.add (.var "support.i") (.lit 1)))
def command : Com := .seq (.assign "round.support" (.lit 0))
  (.seq (.assign "support.i" (.lit 0)) (.while (.lt (.var "support.i") (.var "metric.n")) step))







end Lax455465Proofs.RamSupport

end

-- Solutions.RAM_Lax455465Proofs_RamGridBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamGridBudget
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def finish : Com := .assign "round.steps" (.add (.mul (.lit 2) (.var "size.count")) (.lit 2))
def command : Com := .seq (.assign "size.value" (.var "round.support")) (.seq RamBitSize.word finish)



end Lax455465Proofs.RamGridBudget

end

-- Solutions.RAM_Lax455465Proofs_RamRoundingInit
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRoundingInit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamVirtualState
open scoped NNRat


def support {n : ℕ} (weights : Fin n → ℚ≥0) : ℕ := (RegionSelection.support (fun v => (weights v : ℚ))).card



def command : Com := .seq (.assign "sum.count" (.var "metric.n"))
  (.seq (RamArraySum.command "flow.weights") (.seq (save "round.total")
    (.seq RamSupport.command (.seq RamGridBudget.command RamRoundingConstants.command))))



end Lax455465Proofs.RamRoundingInit

end

-- Solutions.RAM_Lax455465Proofs_RamBestUpdate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBestUpdate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat





def update : Com := .seq (.assign "best.index" (.var "cut.candidate"))
  (.seq (.assign "best.value.n" (.var "cut.ratio.n"))
    (.seq (.assign "best.value.d" (.var "cut.ratio.d")) (.assign "best.found" (.lit 1))))
def compare : Com := .seq (RamScalarComparison.command "best.value" "cut.ratio")
  (.ite (.eq (.var "cmp.le") (.lit 0)) update .skip)
def choose : Com := .ite (.eq (.var "best.found") (.lit 0)) update compare

def command : Com := .ite (.eq (.var "cut.valid") (.lit 1)) choose .skip





end Lax455465Proofs.RamBestUpdate

end

-- Solutions.RAM_Lax455465Proofs_RamBestFold
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamBestFold
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamBestUpdate
open scoped NNRat





def step (producer : Com) : Com := .seq producer (.seq RamBestUpdate.command
  (.assign "cut.candidate" (.add (.var "cut.candidate") (.lit 1))))
def scan (producer : Com) : Com := .seq (.assign "cut.candidate" (.lit 0))
  (.while (.lt (.var "cut.candidate") (.var "cut.count")) (step producer))
def command (producer : Com) : Com := .seq (.assign "best.found" (.lit 0))
  (.seq (.assign "best.index" (.lit 0)) (scan producer))





end Lax455465Proofs.RamBestFold

end

-- Solutions.RAM_Lax455465Proofs_RamMaskedMinimum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMaskedMinimum
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open scoped NNRat










def entry (source mask : String) : Com := .seq (RamArrayScalar.command source "cut.candidate" "cut.ratio")
  (.seq (RamUnsignedBuffer.read mask "cut.candidate") (.assign "cut.valid" (.var "rat.n")))
def command (source mask : String) : Com :=
  .seq (RamBestFold.command (entry source mask)) (load "best.value")





end Lax455465Proofs.RamMaskedMinimum

end

-- Solutions.RAM_Lax455465Proofs_RamThresholdMask
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamThresholdMask
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRational RamBooleanArithmetic
open scoped NNRat




def compare (reversed : Bool) : Com :=
  if reversed then RamScalarComparison.command "cut.threshold" "cut.value"
  else RamScalarComparison.command "cut.value" "cut.threshold"
def emit : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.var "cmp.le")) (.assign "rat.d" (.lit 1)))
def entry (reversed : Bool) : Com := .seq (RamArrayScalar.command "cut.potential" "cut.i" "cut.value")
  (.seq (compare reversed) emit)
def command (reversed : Bool) : Com := .seq (.assign "cut.pos" (.lit 0))
  (RamUnsignedVector.command "cut.i" "metric.n" "cut.flags" "cut.pos" (entry reversed))









end Lax455465Proofs.RamThresholdMask

end

-- Solutions.RAM_Lax455465Proofs_RamSetDistances
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamSetDistances
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open scoped NNRat





def entry (toSet : Bool) : Com := .seq (RamRootDistances.command toSet)
  (RamMaskedMinimum.command (RamRootDistances.array toSet) "potential.set")
def command (toSet : Bool) : Com := .seq (.assign "potential.pos" (.lit 0))
  (RamUnsignedVector.command "region.root" "metric.n" "potential.values" "potential.pos" (entry toSet))






end Lax455465Proofs.RamSetDistances

end

-- Solutions.RAM_Lax455465Proofs_RamSetPotential
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamSetPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open scoped NNRat

def maskArray (toSet : Bool) : String := if toSet then "region.inMask" else "region.outMask"
def targetArray (toSet : Bool) : String := if toSet then "potential.to" else "potential.from"





def setup : Com := .seq (.assign "cut.count" (.var "metric.n"))
  (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
def command (toSet : Bool) : Com := .seq setup
  (.seq (RamArrayCopy.command (maskArray toSet) "potential.set" "copy.count")
    (.seq (RamSetDistances.command toSet) (RamArrayCopy.command "potential.values" (targetArray toSet) "copy.count")))






end Lax455465Proofs.RamSetPotential

end

-- Solutions.RAM_Lax455465Proofs_RamPotentialAverage
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamPotentialAverage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat

def name (toSet : Bool) : String := if toSet then "potential.toAvg" else "potential.fromAvg"
def command (toSet : Bool) : Com := .seq (.assign "sum.count" (.var "metric.n"))
  (.seq (RamProductSum.command "flow.weights" (RamSetPotential.targetArray toSet)) (save (name toSet)))




end Lax455465Proofs.RamPotentialAverage

end

-- Solutions.RAM_Lax455465Proofs_RamPotentialChoice
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPotentialChoice
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat

def select (toSet : Bool) : Com := .seq (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
  (.seq (RamArrayCopy.command (RamSetPotential.targetArray toSet) "cut.potential" "copy.count")
    (.assign "cut.reversed" (.lit (if toSet then 1 else 0))))
def command : Com := .seq (RamScalarComparison.command "potential.toAvg" "potential.fromAvg")
  (.ite (.eq (.var "cmp.le") (.lit 1)) (select false) (select true))







end Lax455465Proofs.RamPotentialChoice

end

-- Solutions.RAM_Lax455465Proofs_RamLargePotential
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargePotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat




def scratchArrays : List String := ["potential.set","potential.values","region.in","region.out",
  "potential.to","potential.from","cut.potential"]
def Room (n : ℕ) (σ : Env) : Prop := ∀ a∈scratchArrays,2*n<(σ.arrs a).length







def command : Com := .seq (RamSetPotential.command false) (.seq (RamSetPotential.command true)
  (.seq (RamPotentialAverage.command false) (.seq (RamPotentialAverage.command true) RamPotentialChoice.command)))




end Lax455465Proofs.RamLargePotential

end

-- Solutions.RAM_Lax455465Proofs_RamScalarDifference
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamScalarDifference
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamUnsignedScalar
open scoped NNRat

def command (leftName rightName target : String) : Com :=
  .seq (RamScalarBinary.command leftName rightName RamTruncatedSubtract.command) (save target)





end Lax455465Proofs.RamScalarDifference

end

-- Solutions.RAM_Lax455465Proofs_RamCutMeasures
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamCutMeasures
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding MetricMatrix
open scoped NNRat



def command : Com := .seq (RamArcMask.command (some true) "cut.flags" "cut.crossing")
  (.seq (.assign "sum.count" (.var "metric.n2"))
    (.seq (RamMaskedSum.command "flow.capacities" "cut.crossing") (.seq (save "cut.capacity")
      (.seq (.assign "sum.count" (.var "metric.n"))
        (.seq (RamMaskedSum.command "flow.weights" "cut.flags") (save "cut.mass"))))))



end Lax455465Proofs.RamCutMeasures

end

-- Solutions.RAM_Lax455465Proofs_RamCutRatio
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamCutRatio
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat



def valid : Com := .ite (.eq (.var "cut.demand.n") (.lit 0))
  (.assign "cut.valid" (.lit 0)) (.assign "cut.valid" (.lit 1))
def command : Com := .seq (RamScalarDifference.command "round.total" "cut.mass" "cut.other")
  (.seq (RamScalarProduct.command "cut.mass" "cut.other" "cut.demand")
    (.seq (RamScalarReciprocal.command "cut.demand" "cut.inverseDemand")
      (.seq (RamScalarProduct.command "cut.capacity" "cut.inverseDemand" "cut.ratio") valid)))



end Lax455465Proofs.RamCutRatio

end

-- Solutions.RAM_Lax455465Proofs_RamCutScore
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamCutScore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat

def command : Com := .seq RamCutMeasures.command RamCutRatio.command





end Lax455465Proofs.RamCutScore

end

-- Solutions.RAM_Lax455465Proofs_RamThresholdCandidate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 4096
namespace Lax455465Proofs.RamThresholdCandidate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped NNRat








def mask : Com := .ite (.eq (.var "cut.reversed") (.lit 1))
  (RamThresholdMask.command true) (RamThresholdMask.command false)
def command : Com := .seq (RamArrayScalar.command "cut.potential" "cut.candidate" "cut.threshold")
  (.seq mask RamCutScore.command)




end Lax455465Proofs.RamThresholdCandidate

end

-- Solutions.RAM_Lax455465Proofs_RamPotentialSweep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPotentialSweep
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamThresholdCandidate
open scoped NNRat

def restore : Com := .seq (.assign "cut.candidate" (.var "best.index")) RamThresholdCandidate.command
def finish : Com := .ite (.eq (.var "best.found") (.lit 1)) restore .skip
def command : Com := .seq (RamBestFold.command RamThresholdCandidate.command) finish










end Lax455465Proofs.RamPotentialSweep

end

-- Solutions.RAM_Lax455465Proofs_RamLargeCut
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamLargeCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding
open scoped BigOperators NNRat



def command : Com := .seq RamLargePotential.command (.seq (.assign "cut.count" (.var "metric.n")) RamPotentialSweep.command)






end Lax455465Proofs.RamLargeCut

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryEntry
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamHistoryEntry
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open scoped NNRat



def command : Com := .seq (.assign "history.address" (.mul (.lit 4) (.var "find.i")))
  (.seq (.assign "history.root" (.get "region.history" (.var "history.address")))
    (.seq (.assign "history.radius.n" (.get "region.history" (.add (.var "history.address") (.lit 1))))
      (.seq (.assign "history.radius.d" (.get "region.history" (.add (.var "history.address") (.lit 2))))
        (.assign "history.outward" (.get "region.history" (.add (.var "history.address") (.lit 3)))))))





end Lax455465Proofs.RamHistoryEntry

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryTest
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryTest
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open Lax455465.RationalEncoding DirectedFlowLP
open scoped NNRat







def address : Com := .ite (.eq (.var "history.outward") (.lit 1))
  (.assign "history.edge" (.add (.mul (.var "history.root") (.var "metric.n")) (.var "history.vertex")))
  (.assign "history.edge" (.add (.mul (.var "history.vertex") (.var "metric.n")) (.var "history.root")))
def flag : Com := .ite (.eq (.var "cmp.le") (.lit 0)) (.assign "find.ok" (.lit 1)) (.assign "find.ok" (.lit 0))
def command : Com := .seq RamHistoryEntry.command (.seq address
  (.seq (RamArrayScalar.command "metric.old" "history.edge" "history.distance")
    (.seq (RamScalarComparison.command "history.radius" "history.distance") flag)))







end Lax455465Proofs.RamHistoryTest

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryLabel
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryLabel
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open Lax455465.RationalEncoding RamHistoryTest
open scoped NNRat

def position : Com := .ite (.eq (.var "history.outward") (.lit 1))
  (.assign "rat.n" (.sub (.mul (.lit 2) (.var "find.count")) (.var "find.result")))
  (.assign "rat.n" (.var "find.result"))
def choose : Com := .ite (.eq (.var "find.found") (.lit 1))
  (.seq (.assign "find.i" (.var "find.result")) (.seq RamHistoryEntry.command position))
  (.assign "rat.n" (.var "find.count"))
def finish : Com := .seq (.assign "rat.d" (.lit 1)) (.assign "rat.s" (.lit 0))
def command : Com := .seq (RamFind.command RamHistoryTest.command) (.seq choose finish)










end Lax455465Proofs.RamHistoryLabel

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryPotential
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryPotential
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open Lax455465.RationalEncoding
open scoped NNRat





def vector : Com := .seq (.assign "history.potentialPos" (.lit 0))
  (RamUnsignedVector.command "history.vertex" "metric.n" "cut.potential" "history.potentialPos" RamHistoryLabel.command)
def command : Com := .seq (.assign "find.count" (.div (.var "history.pos") (.lit 4)))
  (.seq vector (.seq (.assign "cut.reversed" (.lit 1)) (.assign "cut.count" (.var "metric.n"))))






end Lax455465Proofs.RamHistoryPotential

end

-- Solutions.RAM_Lax455465Proofs_RamHistoryCut
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open Lax455465.RationalEncoding
open scoped BigOperators NNRat



def command : Com := .seq RamHistoryPotential.command RamPotentialSweep.command






end Lax455465Proofs.RamHistoryCut

end

-- Solutions.RAM_Lax455465Proofs_RamRegionCut
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRegionCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord
open Lax455465.RationalEncoding
open scoped BigOperators NNRat

structure Room (n : ℕ) (σ : Env) : Prop where
  potential : RamLargePotential.Room n σ
  mask : 2*n < (σ.arrs "cut.flags").length
  crossing : 2*(n*n) < (σ.arrs "cut.crossing").length



def command : Com := .ite (.eq (.var "region.phase") (.lit 1)) RamLargeCut.command RamHistoryCut.command






end Lax455465Proofs.RamRegionCut

end

-- Solutions.RAM_Lax455465Proofs_RamPositiveRounding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPositiveRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant
open Lax455465.RationalEncoding
open scoped NNRat

def command : Com := .seq RamRegionLoop.command RamRegionCut.command



end Lax455465Proofs.RamPositiveRounding

end

-- Solutions.RAM_Lax455465Proofs_RamPositivePair
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamPositivePair
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding DirectedFlowLP
open scoped NNRat







def indices : Com := .seq (.assign "pair.u" (.div (.var "find.i") (.var "metric.n")))
  (.assign "pair.v" (.sub (.var "find.i") (.mul (.var "pair.u") (.var "metric.n"))))
def flags : Com := .ite (.eq (.var "pair.left.n") (.lit 0)) (.assign "find.ok" (.lit 0))
  (.ite (.eq (.var "pair.right.n") (.lit 0)) (.assign "find.ok" (.lit 0))
    (.ite (.eq (.var "pair.distance.n") (.lit 0)) (.assign "find.ok" (.lit 0)) (.assign "find.ok" (.lit 1))))
def test : Com := .seq indices (.seq (RamArrayScalar.command "flow.weights" "pair.u" "pair.left")
  (.seq (RamArrayScalar.command "flow.weights" "pair.v" "pair.right")
    (.seq (RamArrayScalar.command "metric.old" "find.i" "pair.distance") flags)))
def command : Com := .seq (.assign "find.count" (.var "metric.n2")) (RamFind.command test)









end Lax455465Proofs.RamPositivePair

end

-- Solutions.RAM_Lax455465Proofs_RamZeroCut
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamZeroCut
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding DirectedFlowLP
open scoped BigOperators NNRat











def prepare : Com := .seq RamPositivePair.command
  (.seq (.assign "region.root" (.div (.var "find.result") (.var "metric.n")))
    (.seq (RamRootDistances.command true)
      (.seq (.assign "copy.count" (.mul (.lit 2) (.var "metric.n")))
        (.seq (RamArrayCopy.command "region.out" "cut.potential" "copy.count")
          (.seq (.assign "cut.reversed" (.lit 0)) (.assign "cut.count" (.var "metric.n")))))))

def command : Com := .seq prepare RamPotentialSweep.command






end Lax455465Proofs.RamZeroCut

end

-- Solutions.RAM_Lax455465Proofs_RamRoundingDispatch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamRoundingDispatch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

def command : Com := .ite (.eq (.var "round.cost.n") (.lit 0)) RamZeroCut.command RamPositiveRounding.command



end Lax455465Proofs.RamRoundingDispatch

end

-- Solutions.RAM_Lax455465Proofs_RamMetricRounding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 8192
namespace Lax455465Proofs.RamMetricRounding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionInvariant RamVirtualState
open Lax455465.RationalEncoding
open scoped NNRat BigOperators

structure Input {n : ℕ} (I : RationalInstance n) (length : MetricMatrix.Matrix n) (σ : Env) : Prop where
  nValue : σ.vars "metric.n"=n
  n2Value : σ.vars "metric.n2"=n*n
  weights : Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ
  capacities : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values I.capacity)) "flow.capacities" σ
  distances : Prefix (RamUnsignedBuffer.encode (MetricMatrix.values length)) "metric.old" σ
  costData : Stored "round.cost" (MetricCostData.cost I length) σ

def command : Com := .seq RamRoundingInit.command RamRoundingDispatch.command



end Lax455465Proofs.RamMetricRounding

end

-- Solutions.RAM_Lax455465Proofs_RamRoundingResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamRoundingResources
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open LpInputSize
open scoped NNRat

/-- The native instruction bound written as a polynomial expression in
vertex count and the three rational bit budgets. -/
def timeExpression {α : Type*} [Semiring α] (n w c h v : α) : α :=
  let a := c*2+1
  let b := v*2+1
  let query := (288*h+880)*(n*n)+(144*h+584)*n+144*h+554
  let initialCost := (36*a+208)*(n*n)+(36*a+166)*n+40
  let setup := (36*a+query+160)*(2*n+4+1+2*n)+84*n+query+80
  let core := initialCost+setup+96*n+200
  let loop := (core+13)*(n+1)+6
  let score := (36*b+234)*(n*n)+(36*b+152)*n+144*b+468
  let candidate := score+110*n+30
  let sweep := (candidate+92)*n+candidate+16
  let setPotential := (168*n+46)*n+8+48*n+18
  let average := (72*b+224)*n+22
  let large := 2*setPotential+2*average+24*n+80+sweep+2
  let history := (140*n+74)*n+16+sweep
  let regionCut := large+history+4
  let zero := 98*(n*n)+66*n+38+sweep
  ((36*a+200)*(n+1)+600*a+2000)+(36*(w+3)+28*n+116+loop+regionCut+zero)



noncomputable def baseBound (metricWord : Polynomial ℕ) : Polynomial ℕ :=
  RamMetricCostResources.heightBound metricWord+Polynomial.X*(Polynomial.X+1)+Polynomial.X+1+
    metricWord+3*Polynomial.X+8

noncomputable def constantsBound (base : Polynomial ℕ) : Polynomial ℕ := 3*base+2
noncomputable def queriesBound (base : Polynomial ℕ) : Polynomial ℕ :=
  let c := constantsBound base
  2*(3*(4*(2*c)*(Polynomial.X*Polynomial.X+1)+Polynomial.X*Polynomial.X+1)+1)+2*c+1
noncomputable def cutsBound (base : Polynomial ℕ) : Polynomial ℕ :=
  let c := constantsBound base
  2*c+3*(c*(Polynomial.X*Polynomial.X+1)+Polynomial.X*Polynomial.X+1)+
    (2*c*(Polynomial.X+1)+Polynomial.X+1)+2*Polynomial.X+4
noncomputable def wordBound (base : Polynomial ℕ) : Polynomial ℕ :=
  2*(constantsBound base+queriesBound base+cutsBound base)+2*Polynomial.X*Polynomial.X+12*Polynomial.X+28
noncomputable def timeBound (base : Polynomial ℕ) : Polynomial ℕ :=
  timeExpression Polynomial.X base (constantsBound base) (queriesBound base) (cutsBound base)











end Lax455465Proofs.RamRoundingResources

end

-- Solutions.RAM_Lax455465Proofs_RamHalfFraction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamHalfFraction
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamArithmetic
open scoped NNRat

def command : Com := .seq (.assign "rat.d" (.mul (.lit 2) (.var "rat.d"))) normalizeFraction



end Lax455465Proofs.RamHalfFraction

end

-- Solutions.RAM_Lax455465Proofs_RamFlowConvert
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFlowConvert
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat



def Context (kind : EdgeKind) (qs : List ℚ≥0) (σ : Env) : Prop :=
  σ.vars "flow.kind"=RamGraphHeader.tag kind ∧ σ.vars "lp.columns"=qs.length ∧
    Prefix (RamUnsignedBuffer.encode qs) "flow.primal" σ



def choose : Com := .ite (.eq (.var "flow.kind") (.lit 0))
  (.ite (.eq (.var "emit.coordinate") (.lit 0)) .skip RamHalfFraction.command) .skip

def body : Com := .seq (RamUnsignedBuffer.read "flow.primal" "emit.coordinate") choose

def command : Com := .seq (.assign "emit.convertedPos" (.lit 0))
  (RamUnsignedVector.command "emit.coordinate" "lp.columns" "flow.converted" "emit.convertedPos" body)















end Lax455465Proofs.RamFlowConvert

end

-- Solutions.RAM_Lax455465Proofs_RamEmitWords
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamEmitWords
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState

def step (array : String) (stride : ℕ) : Com := .seq (.write (.get array (.mul (.lit stride) (.var "emit.i"))))
  (.assign "emit.i" (.add (.var "emit.i") (.lit 1)))
def command (array : String) (stride : ℕ) : Com := .seq (.assign "emit.i" (.lit 0))
  (.while (.lt (.var "emit.i") (.var "emit.count")) (step array stride))






end Lax455465Proofs.RamEmitWords

end

-- Solutions.RAM_Lax455465Proofs_RamJointOutput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamJointOutput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork
open scoped NNRat

def emit : Com := .seq (.assign "emit.count" (.var "metric.n"))
  (.seq (RamEmitWords.command "cut.flags" 2)
    (.seq (.assign "emit.count" (.mul (.lit 2) (.var "lp.columns")))
      (RamEmitWords.command "flow.converted" 1)))
def command : Com := .seq RamFlowConvert.command emit













end Lax455465Proofs.RamJointOutput

end

-- Solutions.RAM_Lax455465Proofs_RamOutputResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamOutputResources
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open scoped NNRat

noncomputable def timeBound (P : Polynomial ℕ) : Polynomial ℕ :=
  (36*(P+2)+90)*(1+Polynomial.X^4)+13*Polynomial.X+26
noncomputable def wordBound (P : Polynomial ℕ) : Polynomial ℕ :=
  2*P+2*(1+Polynomial.X^4)+2*Polynomial.X+16







end Lax455465Proofs.RamOutputResources

end

-- Solutions.RAM_Lax455465Proofs_RamRoundAndOutput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 16384
namespace Lax455465Proofs.RamRoundAndOutput
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax759944.BinaryWordEncoding
open Lax109476.LinearProgram
open scoped NNRat

def command : Com := .seq RamMetricRounding.command RamJointOutput.command
noncomputable def timeBound (metric primal : Polynomial ℕ) : Polynomial ℕ :=
  RamRoundingResources.timeBound (RamRoundingResources.baseBound metric)+RamOutputResources.timeBound primal
noncomputable def wordBound (metric primal : Polynomial ℕ) : Polynomial ℕ :=
  RamRoundingResources.wordBound (RamRoundingResources.baseBound metric)+RamOutputResources.wordBound primal





end Lax455465Proofs.RamRoundAndOutput

end

-- Solutions.RAM_Lax263307_NativeRoundedStep
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.NativeRoundedStep

open Lax808846.Ram (Program RunsTo)
open Matrix RoundedOracleSearch Lax109476.RationalEncoding

def height (q : ℚ) (h : ℕ) : Prop := q.num.natAbs ≤ 2 ^ h ∧ q.den ≤ 2 ^ h

def encodeInput {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) : List ℕ :=
  [n, k] ++ (List.ofFn fun i => encodeVector (state.1 i)).flatten ++
    encodeVector (rationalNormal a) ++ encodeVector state.2

def encodeOutput {n : ℕ} (state : State n) : List ℕ :=
  (List.ofFn fun i : Fin (n * n) => state.1 i.divNat i.modNat).flatMap encodeRational ++
    encodeVector state.2

end Lax263307.NativeRoundedStep

end

-- Solutions.RAM_Lax263307Proofs_NearOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

namespace Lax263307Proofs.NearOracle

open scoped NNRat
open Lax263307.NearOracle Lax263307.GraphClasses
open Lax263307.LinearRelaxation Lax263307.RationalConditioning
open Lax263307.AlgorithmParameters Lax263307.ComputedSeparators
open Lax263307.RepeatedCutAccounting





/-- The selected backend's separator guarantee, retained for actual
recursive child-domain and resource proofs. -/
def SeparatorCorrect (C : GraphClass) (flow : List ℕ → List ℕ) (a K B : ℕ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (x : Fin n → ℚ≥0) (k p ℓ : ℕ),
      0 < k → 0 < p → 0 < ℓ →
      (∀ v, (x v : ℝ) ≤ 1) → (∑ v, (x v : ℝ)) ≤ k →
      Lax263307.Entropy.edgeCost G (fun v => (x v : ℝ)) ≤ (k : ℝ) ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p →
      let cs := cuts (step flow G x B ℓ k) n Finset.univ
      cs.length ≤ n ∧
        Lax263307.EdgeSublinearSeparators.IsBalancedSeparator G
          (Lax263307.ComputedSeparators.separator cs) ∧
        cost (fun v => (x v : ℝ)) (Lax263307.ComputedSeparators.separator cs) ≤
          12 * (ratio B n : ℝ) * k / ℓ ∧
        ∃ P : Lax263307.SeparatorComponents.Partition G
            (Lax263307.ComputedSeparators.separator cs) (Option (Fin cs.length)),
          (∀ i, P.vertices i = pieces cs i) ∧ ∀ i, 3 * (P.vertices i).card ≤ 2 * n




end Lax263307Proofs.NearOracle

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursiveOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Correctness of the chosen projection/flow pair at every recursive node. -/
def OracleCorrect (C : GraphClass) (lp flow : List ℕ → List ℕ) (a K b : ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G ∈ C n → 0< n →
    ∀ D k h, 4≤ D → cutoff a K b n D< k →
    ∀ child, NearOracle.ChildCorrect G D h child →
    ∀ center, ProjectedOracle.Correct G k h a K b D center
      (ProjectedOracle.run lp flow a K b D G k child center)














end Lax263307Proofs.NativeRecursiveOracle

end

-- Solutions.RAM_Lax263307_WeightedAlgorithm
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The weighted independent-set approximation algorithm
type: definition
---
Clip negative weights, round the remaining weights to copy multiplicities,
and run the unweighted algorithm on the independent blow-up. Project the
answer back to the original vertices and discard nonpositive-weight
vertices. Empty and nonpositive instances return the empty set.

# Formalization notes

The function takes fixed LP and flow solvers as arguments. Blow-up vertices
are numbered by the finite-sigma equivalence. The complete correctness,
RAM execution, and running-time guarantees are supplied by the proof of
the main QPTAS theorem.
-/

namespace Lax263307.WeightedAlgorithm

open RecursiveAlgorithm (independentSet)
open WeightRounding IndependentBlowUp PositiveWeights

def labeling {n : ℕ} (copies : Fin n → ℕ) : Fin (∑ v, copies v) ≃ Vertex copies :=
  finSigmaFinEquiv.symm

def numbered {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Fin (∑ v, copies v)) := (graph G copies).comap (labeling copies)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (copies : Fin n → ℕ) :
    DecidableRel (numbered G copies).Adj := fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))

def solve {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (ε : ℚ) : Finset (Fin n) :=
  let w' := positiveWeights w
  if n = 0 ∨ maximumWeight w' ≤ 0 then ∅
  else
    let copies' := copies w' ε
    let I := independentSet lp flow a K B (numbered G copies') (ε/2)
    discardNonpositive w (project (I.image (labeling copies')))

end Lax263307.WeightedAlgorithm

end

-- Solutions.RAM_Lax263307Proofs_NativeLogarithms
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeLogarithms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open Lax455465Proofs



def small : Com := .seq (.assign "size.value" (.var "graph.n"))
  (.seq RamBitSize.word (.assign "node.log" (.var "size.count")))

def large : Com := .seq (.assign "size.value" (.mul (.lit 2) (.var "graph.n")))
  (.seq RamBitSize.word (.assign "node.logarithm" (.var "size.count")))

def command : Com := .seq small large







end Lax263307Proofs.NativeLogarithms

end

-- Solutions.RAM_Lax263307Proofs_NativeSignedAccumulate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSignedAccumulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational NativeSignedArithmetic

def command : Com := .seq (save "right")
  (.seq (load "sum.value") (.seq (save "left") (.seq addFraction (save "sum.value"))))



end Lax263307Proofs.NativeSignedAccumulate

end

-- Solutions.RAM_Lax263307Proofs_NativeFrontend
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrontend

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.WeightedIndependentSet





def metadata : Com :=
  .seq (.assign "input.matrixLength" (.mul (.var "input.n") (.var "input.n")))
  (.seq (.assign "input.weightLength" (.mul (.lit 3) (.var "input.n")))
    (.assign "input.length" (.add (.add (.var "input.matrixLength") (.var "input.weightLength")) (.lit 3))))

def readInput : Com := .seq (.read "input.n") (.seq metadata
  (.seq (.assign "input.i" (.lit 0))
    (.while (.lt (.var "input.i") (.var "input.length")) RamInputCopy.copyStep)))








def computeCopies : Com := .assign "copy.count"
  (.div (.mul (.mul (.mul (.mul (.lit 2) (.var "input.n")) (.var "weight.n"))
    (.var "accuracy.d")) (.var "maximum.d"))
    (.mul (.mul (.var "weight.d") (.var "accuracy.n")) (.var "maximum.n")))








def updateMaximum : Com :=
  .ite (.lt (.mul (.var "maximum.n") (.var "weight.d"))
    (.mul (.var "weight.n") (.var "maximum.d")))
    (.seq (.assign "maximum.n" (.var "weight.n")) (.assign "maximum.d" (.var "weight.d"))) .skip








def readWeight : Com :=
  .seq (.assign "weight.s" (.get "input.data" (.var "weight.position")))
  (.seq (.assign "weight.n" (.get "input.data" (.add (.var "weight.position") (.lit 1))))
  (.seq (.assign "weight.d" (.get "input.data" (.add (.var "weight.position") (.lit 2))))
    (.ite (.eq (.var "weight.s") (.lit 1)) (.assign "weight.n" (.lit 0)) .skip)))













def maximumStep : Com :=
  .seq (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
  (.seq readWeight (.seq updateMaximum (.assign "weight.i" (.add (.var "weight.i") (.lit 1)))))



end Lax263307Proofs.NativeFrontend

end

-- Solutions.RAM_Lax263307Proofs_NativeMaximum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeMaximum

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet















def command : Com := .seq (.assign "maximum.n" (.lit 0))
  (.seq (.assign "maximum.d" (.lit 1))
    (.seq (.assign "weight.i" (.lit 0))
      (.while (.lt (.var "weight.i") (.var "input.n")) maximumStep)))














end Lax263307Proofs.NativeMaximum

end

-- Solutions.RAM_Lax263307Proofs_NativeMultiplicities
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeMultiplicities

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet





def step : Com :=
  .seq (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
  (.seq readWeight (.seq computeCopies
    (Lax455465Proofs.RamWordBuffer.append "copy.counts" "weight.i" (.var "copy.count"))))









def command : Com := .seq (.assign "weight.i" (.lit 0))
  (.while (.lt (.var "weight.i") (.var "input.n")) step)






def readAccuracy : Com :=
  .seq (.assign "weight.position" (.add (.var "input.matrixLength") (.var "input.weightLength")))
  (.seq readWeight
    (.seq (.assign "accuracy.n" (.var "weight.n")) (.assign "accuracy.d" (.var "weight.d"))))



end Lax263307Proofs.NativeMultiplicities

end

-- Solutions.RAM_Lax263307Proofs_NativeWeightReduction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

def adjacency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

def prepare : Com := .seq readInput (.seq NativeMaximum.command
  (.seq NativeMultiplicities.readAccuracy NativeMultiplicities.command))















open Lax109476Proofs





end Lax263307Proofs.NativeWeightReduction

end

-- Solutions.RAM_Lax263307Proofs_NativeBlowUp
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeBlowUp

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm















def repeatStep : Com := .seq
  (Lax455465Proofs.RamWordBuffer.append "blowup.owner" "blowup.length" (.var "owner.value"))
  (.assign "owner.j" (.add (.var "owner.j") (.lit 1)))

def repeatCommand : Com := .seq (.assign "owner.j" (.lit 0))
  (.while (.lt (.var "owner.j") (.var "owner.count")) repeatStep)













def ownerPrepare : Com := .seq (.assign "owner.value" (.var "owner.i"))
  (.assign "owner.count" (.get "copy.counts" (.var "owner.i")))

def ownerStep : Com := .seq ownerPrepare (.seq repeatCommand
  (.assign "owner.i" (.add (.var "owner.i") (.lit 1))))





def ownerCommand : Com := .seq (.assign "blowup.length" (.lit 0))
  (.seq (.assign "owner.i" (.lit 0)) (.while (.lt (.var "owner.i") (.var "input.n")) ownerStep))















def matrixEntry : Com :=
  .seq (.assign "matrix.u" (.get "blowup.owner" (.div (.var "matrix.i") (.var "blowup.length"))))
  (.seq (.assign "matrix.v" (.get "blowup.owner" (.sub (.var "matrix.i") (.mul (.div (.var "matrix.i") (.var "blowup.length")) (.var "blowup.length")))))
    (.assign "matrix.entry" (.get "input.data"
      (.add (.mul (.var "matrix.u") (.var "input.n")) (.var "matrix.v")))))



def matrixStep : Com := .seq matrixEntry
  (Lax455465Proofs.RamWordBuffer.append "blowup.matrix" "matrix.i" (.var "matrix.entry"))







def matrixCommand : Com := .seq
  (.assign "matrix.length" (.mul (.var "blowup.length") (.var "blowup.length")))
  (.seq (.assign "matrix.i" (.lit 0))
    (.while (.lt (.var "matrix.i") (.var "matrix.length")) matrixStep))



def construct : Com := .seq ownerCommand matrixCommand



def prepare : Com := .seq NativeWeightReduction.prepare construct

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

def cost (n N : ℕ) : ℕ := 12*(n*n+3*n+3)+110*n+78+(15*N+19)*n+32*N*N+18











open Lax109476Proofs





end Lax263307Proofs.NativeBlowUp

end

-- Solutions.RAM_Lax263307Proofs_NativeCombinations
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCombinations

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState











def coordinates : Com :=
  .seq (.assign "choose.row" (.div (.var "choose.i") (.var "choose.cols")))
    (.assign "choose.col" (.sub (.var "choose.i")
      (.mul (.var "choose.row") (.var "choose.cols"))))

def entry : Com := .ite (.eq (.var "choose.col") (.lit 0))
  (.assign "choose.value" (.lit 1))
  (.ite (.eq (.var "choose.row") (.lit 0)) (.assign "choose.value" (.lit 0))
    (.seq (.assign "choose.prev" (.mul (.sub (.var "choose.row") (.lit 1)) (.var "choose.cols")))
      (.assign "choose.value" (.add
        (.get "choose.table" (.add (.var "choose.prev") (.sub (.var "choose.col") (.lit 1))))
        (.get "choose.table" (.add (.var "choose.prev") (.var "choose.col")))))))

def step : Com := .seq coordinates (.seq entry
  (Lax455465Proofs.RamWordBuffer.append "choose.table" "choose.i" (.var "choose.value")))









def metadata : Com := .seq (.assign "choose.cols" (.add (.var "choose.k") (.lit 1)))
  (.assign "choose.length" (.mul (.add (.var "choose.n") (.lit 1)) (.var "choose.cols")))

def command : Com := .seq metadata (.seq (.assign "choose.i" (.lit 0))
  (.while (.lt (.var "choose.i") (.var "choose.length")) step))

















def subsetEntry : Com := .ite (.eq (.var "subset.need") (.lit 0))
  (.assign "subset.bit" (.lit 0))
  (.seq (.assign "subset.count" (.get "choose.table"
      (.add (.mul (.sub (.sub (.var "choose.n") (.var "subset.i")) (.lit 1)) (.var "choose.cols"))
        (.var "subset.need"))))
    (.ite (.lt (.var "subset.rank") (.var "subset.count")) (.assign "subset.bit" (.lit 0))
      (.seq (.assign "subset.bit" (.lit 1))
        (.seq (.assign "subset.rank" (.sub (.var "subset.rank") (.var "subset.count")))
          (.assign "subset.need" (.sub (.var "subset.need") (.lit 1)))))))



def subsetStep : Com := .seq subsetEntry
  (Lax455465Proofs.RamWordBuffer.append "subset.bits" "subset.i" (.var "subset.bit"))





def subsetCommand : Com := .seq (.assign "subset.i" (.lit 0))
  (.while (.lt (.var "subset.i") (.var "choose.n")) subsetStep)











end Lax263307Proofs.NativeCombinations

end

-- Solutions.RAM_Lax263307_NativeCatalog
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Encoding the moment-coordinate catalogue
type: definition
---
The moment-coordinate catalogue lists subsets of the vertex set in the
order used by the relaxation. Each subset is represented by its binary
membership mask; `words` is the resulting list of masks.

# Formalization notes

Masks encode subsets of `Fin n`. The catalogue contains only the subsets
needed by the relaxation, rather than an array indexed by all $2^n$ masks.
-/

namespace Lax263307.NativeCatalog

open CoordinateCatalog (catalog)
def subsetMask {n : ℕ} (I : Finset (Fin n)) : ℕ :=
  Finset.equivBitIndices.symm (I.image Fin.val)



end Lax263307.NativeCatalog

end

-- Solutions.RAM_Lax263307Proofs_NativeMasks
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

/-- A coordinate is stored in one word; bit positions are original vertex labels. -/
abbrev mask {n : ℕ} (I : Finset (Fin n)) : ℕ :=
  Lax263307.NativeCatalog.subsetMask I























def step : Com := .seq (.assign "mask.value"
  (.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i"))))
  (.assign "mask.i" (.add (.var "mask.i") (.lit 1)))





def command : Com := .seq (.assign "mask.value" (.lit 0))
  (.seq (.assign "mask.i" (.lit 0)) (.while (.lt (.var "mask.i") (.var "graph.n")) step))



end Lax263307Proofs.NativeMasks

end

-- Solutions.RAM_Lax263307Proofs_NativeZeroScan
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeZeroScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning











def update : Com := .seq
  (.ite (.eq (.var "test.bit") (.lit 0)) .skip (.assign "test.ok" (.lit 0)))
  (.assign "test.i" (.add (.var "test.i") (.lit 1)))



def body (read : Com) : Com := .seq read update

def command (read : Com) : Com := .seq (.assign "test.ok" (.lit 1))
  (.seq (.assign "test.i" (.lit 0)) (.while (.lt (.var "test.i") (.var "test.limit")) (body read)))





end Lax263307Proofs.NativeZeroScan

end

-- Solutions.RAM_Lax263307Proofs_NativeIndependentTest
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeIndependentTest

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet













def read (graphArray membershipArray : String) : Com :=
  .seq (.assign "test.row" (.div (.var "test.i") (.var "graph.n")))
  (.seq (.assign "test.col" (.sub (.var "test.i") (.mul (.var "test.row") (.var "graph.n"))))
    (.assign "test.bit" (.mul
      (.mul (.get membershipArray (.var "test.row")) (.get membershipArray (.var "test.col")))
      (.get graphArray (.var "test.i")))))







def command (graphArray membershipArray : String) : Com := .seq
  (.assign "test.limit" (.mul (.var "graph.n") (.var "graph.n")))
  (NativeZeroScan.command (read graphArray membershipArray))



end Lax263307Proofs.NativeIndependentTest

end

-- Solutions.RAM_Lax263307Proofs_NativeExhaustive
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeExhaustive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307.ExhaustiveTargets









def prepareCandidate : Com := .seq (.assign "subset.need" (.var "target.k"))
  (.assign "subset.rank" (.var "target.i"))

def candidateCommand : Com := .seq prepareCandidate (.seq NativeCombinations.subsetCommand
  (.seq (NativeIndependentTest.command "search.graph" "subset.bits")
    (.assign "target.found" (.var "test.ok"))))















def step : Com := .seq (.ite (.eq (.var "target.found") (.lit 0)) candidateCommand .skip)
  (.assign "target.i" (.add (.var "target.i") (.lit 1)))



def search : Com := .seq (.assign "target.found" (.lit 0))
  (.seq (.assign "target.i" (.lit 0))
    (.while (.lt (.var "target.i") (.var "target.count")) step))



def setup : Com := .seq (.assign "choose.n" (.var "graph.n"))
  (.assign "choose.k" (.var "target.k"))

def readCount : Com := .assign "target.count" (.get "choose.table"
  (.add (.mul (.var "graph.n") (.var "choose.cols")) (.var "target.k")))

def prepare : Com := .seq setup (.seq NativeCombinations.command readCount)





def command : Com := .seq prepare search

def cost (n k : ℕ) : ℕ := 54*(n+1)*(k+1)+(38*n*n+54*n+44)*(n.choose k)+35




















open Lax109476Proofs





end Lax263307Proofs.NativeExhaustive

end

-- Solutions.RAM_Lax263307Proofs_NativeCatalog
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCatalog

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307











def prepareCandidate : Com := .seq (.assign "subset.need" (.var "catalog.k"))
  (.assign "subset.rank" (.var "catalog.i"))

def candidateCommand : Com := .seq prepareCandidate (.seq NativeCombinations.subsetCommand NativeMasks.command)





def blockStep : Com := .seq candidateCommand
  (.seq (Lax455465Proofs.RamWordBuffer.append "catalog.mask" "catalog.count" (.var "mask.value"))
    (.assign "catalog.i" (.add (.var "catalog.i") (.lit 1))))



def blockCommand : Com := .seq (.assign "catalog.i" (.lit 0))
  (.while (.lt (.var "catalog.i") (.var "catalog.blockLength")) blockStep)



def prepare : Com := .seq
  (.seq (.assign "choose.n" (.var "graph.n")) (.assign "choose.k" (.var "catalog.k")))
  (.seq NativeCombinations.command (.assign "catalog.blockLength"
    (.get "choose.table" (.add (.mul (.var "choose.n") (.var "choose.cols")) (.var "catalog.k")))))





















def outerStep : Com := .seq prepare (.seq blockCommand
  (.assign "catalog.k" (.add (.var "catalog.k") (.lit 1))))



def command : Com := .seq (.assign "catalog.count" (.lit 0))
  (.seq (.assign "catalog.k" (.lit 0)) (.while (.lt (.var "catalog.k") (.var "catalog.limit")) outerStep))





















open Lax109476Proofs





end Lax263307Proofs.NativeCatalog

end

-- Solutions.RAM_Lax263307Proofs_NativeTabulate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def append (array : String) : Com :=
  Lax455465Proofs.RamWordBuffer.append array "fill.i" (.var "fill.value")

def command (array : String) (read : Com) : Com := .seq (.assign "fill.i" (.lit 0))
  (.while (.lt (.var "fill.i") (.var "fill.length")) (.seq read (append array)))





end Lax263307Proofs.NativeTabulate

end

-- Solutions.RAM_Lax263307Proofs_NativeMaskUnpack
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMaskUnpack

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open NativeMasks







def read : Com := .assign "unpack.bit" (.and (.shiftr (.var "unpack.mask") (.var "unpack.i")) (.lit 1))

def step : Com := .seq read (.seq (.assign "unpack.card" (.add (.var "unpack.card") (.var "unpack.bit")))
  (Lax455465Proofs.RamWordBuffer.append "subset.bits" "unpack.i" (.var "unpack.bit")))





def command : Com := .seq (.assign "unpack.card" (.lit 0))
  (.seq (.assign "unpack.i" (.lit 0)) (.while (.lt (.var "unpack.i") (.var "graph.n")) step))



end Lax263307Proofs.NativeMaskUnpack

end

-- Solutions.RAM_Lax263307Proofs_NativeCatalogMetadata
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCatalogMetadata

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

abbrev N (n r : ℕ) := (CoordinateCatalog.catalog n r).length











def readMask : Com := .assign "unpack.mask" (.get "catalog.mask" (.var "fill.i"))



def prepareSet : Com := .seq readMask NativeMaskUnpack.command



def readCard : Com := .seq prepareSet (.assign "fill.value" (.var "unpack.card"))



def readIndependent : Com := .seq prepareSet
  (.seq (NativeIndependentTest.command "search.graph" "subset.bits") (.assign "fill.value" (.var "test.ok")))



def command : Com := .seq (.assign "fill.length" (.var "catalog.count"))
  (.seq (NativeTabulate.command "catalog.card" readCard) (NativeTabulate.command "catalog.independent" readIndependent))



end Lax263307Proofs.NativeCatalogMetadata

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentRows
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks
open Lax263307









def compare (dst left right : String) : Com :=
  .ite (.eq (.var left) (.var right)) (.assign dst (.lit 1)) (.assign dst (.lit 0))



def insertCommand : Com := .assign "row.insert" (.or (.var "row.mask") (.shiftl (.lit 1) (.var "row.v")))



def monotoneCommand : Com := .seq insertCommand
  (.seq (compare "coefficient.positive" "row.insert" "column.mask")
    (compare "coefficient.negative" "row.mask" "column.mask"))



















def countBranch : Com := .ite (.eq (.var "row.insert") (.var "column.mask"))
  (.assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))) .skip

def countStep : Com := .seq insertCommand (.seq countBranch (.assign "row.v" (.add (.var "row.v") (.lit 1))))





def countCommand : Com := .seq (.assign "coefficient.positive" (.lit 0))
  (.seq (.assign "row.v" (.lit 0)) (.while (.lt (.var "row.v") (.var "graph.n")) countStep))



def massCommand : Com := .seq countCommand (.seq (compare "coefficient.negative" "row.mask" "column.mask")
  (.assign "coefficient.negative" (.mul (.var "row.k") (.var "coefficient.negative"))))



end Lax263307Proofs.NativeMomentRows

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentAccess
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentAccess

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeCatalogMetadata



def load : Com := .seq (.assign "row.mask" (.get "catalog.mask" (.var "row.index")))
  (.seq (.assign "row.card" (.get "catalog.card" (.var "row.index")))
    (.seq (.assign "row.independent" (.get "catalog.independent" (.var "row.index")))
      (.assign "column.mask" (.get "catalog.mask" (.var "column.index")))))

def activate : Com := .ite (.lt (.var "row.card") (.add (.var "moment.r") (.lit 2)))
  (.assign "row.active" (.lit 1)) (.assign "row.active" (.lit 0))









def command : Com := .seq load activate



end Lax263307Proofs.NativeMomentAccess

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentProduce
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentProduce

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks NativeMomentRows



def zeroCommand : Com := .seq (.assign "coefficient.positive" (.lit 0)) (.assign "coefficient.negative" (.lit 0))



def singleCommand : Com := .seq (compare "coefficient.positive" "row.mask" "column.mask")
  (.assign "coefficient.negative" (.lit 0))







def swap : Com := .seq (.assign "coefficient.temp" (.var "coefficient.positive"))
  (.seq (.assign "coefficient.positive" (.var "coefficient.negative"))
    (.assign "coefficient.negative" (.var "coefficient.temp")))



def guard (flag : String) (expected : ℕ) (c : Com) : Com :=
  .ite (.eq (.var flag) (.lit expected)) c zeroCommand



end Lax263307Proofs.NativeMomentProduce

end

-- Solutions.RAM_Lax263307Proofs_NativeIntegerEncoding
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeIntegerEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding











def normalize : Com := .ite (.lt (.var "coefficient.positive") (.var "coefficient.negative"))
  (.seq (.assign "coefficient.sign" (.lit 1))
    (.assign "coefficient.magnitude" (.sub (.var "coefficient.negative") (.var "coefficient.positive"))))
  (.seq (.assign "coefficient.sign" (.lit 0))
    (.assign "coefficient.magnitude" (.sub (.var "coefficient.positive") (.var "coefficient.negative"))))



def append : Com := .seq normalize
  (.seq (Lax455465Proofs.RamWordBuffer.append "lp.input" "lp.length" (.var "coefficient.sign"))
    (.seq (Lax455465Proofs.RamWordBuffer.append "lp.input" "lp.length" (.var "coefficient.magnitude"))
      (Lax455465Proofs.RamWordBuffer.append "lp.input" "lp.length" (.lit 1))))



end Lax263307Proofs.NativeIntegerEncoding

end

-- Solutions.RAM_Lax263307Proofs_NativeRationalTabulate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeRationalTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding









def advance : Com := .assign "fill.i" (.add (.var "fill.i") (.lit 1))

def body (read : Com) : Com := .seq read (.seq NativeIntegerEncoding.append advance)

def command (read : Com) : Com := .seq (.assign "fill.i" (.lit 0))
  (.while (.lt (.var "fill.i") (.var "fill.length")) (body read))





end Lax263307Proofs.NativeRationalTabulate

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentAssembly
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeMomentAssembly

open Lax263307 Lax109476.RationalEncoding
open MomentLP CoordinateCatalog























def rowCount (n r : ℕ) : ℕ :=
  2+(dimension n r+(dimension n r+(dimension n r*n+(dimension n r+dimension n r))))






end Lax263307Proofs.NativeMomentAssembly

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentFamily
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

/-! Native entry readers for the six fixed moment-matrix row families. -/

namespace Lax263307Proofs.NativeMomentFamily

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP

inductive Kind
  | normalization | upper | nonindependent | monotone | massPositive | massNegative
  deriving DecidableEq







def coordinates : Com := .seq (.assign "family.row" (.div (.var "fill.i") (.var "catalog.count")))
  (.assign "column.index" (.sub (.var "fill.i") (.mul (.var "family.row") (.var "catalog.count"))))

def selectRow (kind : Kind) : Com := match kind with
  | .normalization => .assign "row.index" (.lit 0)
  | .monotone => .seq (.assign "row.index" (.div (.var "family.row") (.var "graph.n")))
      (.assign "row.v" (.sub (.var "family.row") (.mul (.var "row.index") (.var "graph.n"))))
  | _ => .assign "row.index" (.var "family.row")

def produce (kind : Kind) : Com := match kind with
  | .normalization => .ite (.eq (.var "family.row") (.lit 0)) NativeMomentProduce.singleCommand
      (.seq NativeMomentProduce.singleCommand NativeMomentProduce.swap)
  | .upper => NativeMomentProduce.singleCommand
  | .nonindependent => NativeMomentProduce.guard "row.independent" 0 NativeMomentProduce.singleCommand
  | .monotone => NativeMomentProduce.guard "row.active" 1 NativeMomentRows.monotoneCommand
  | .massPositive => NativeMomentProduce.guard "row.active" 1 NativeMomentRows.massCommand
  | .massNegative => .seq (NativeMomentProduce.guard "row.active" 1 NativeMomentRows.massCommand) NativeMomentProduce.swap

def read (kind : Kind) : Com := .seq coordinates (.seq (selectRow kind) (.seq NativeMomentAccess.command (produce kind)))

def appendMatrix (kind : Kind) : Com := NativeRationalTabulate.command (read kind)



























open NativeCatalogMetadata NativeMomentProduce

















def countExpr (kind : Kind) : Expr := match kind with
  | .normalization => .mul (.lit 2) (.var "catalog.count")
  | .monotone => .mul (.mul (.var "catalog.count") (.var "graph.n")) (.var "catalog.count")
  | _ => .mul (.var "catalog.count") (.var "catalog.count")

def command (kind : Kind) : Com := .seq (.assign "fill.length" (countExpr kind)) (appendMatrix kind)





end Lax263307Proofs.NativeMomentFamily

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily





def command (ks : List Kind) : Com := ks.foldr (fun kind c => .seq (NativeMomentFamily.command kind) c) .skip




def allKinds : List Kind := [.normalization,.upper,.nonindependent,.monotone,.massPositive,.massNegative]





end Lax263307Proofs.NativeMomentMatrix

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentVectors
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce









def read : Com := .seq
  (.ite (.eq (.var "fill.i") (.lit 1)) (.assign "coefficient.positive" (.lit 0))
    (.ite (.lt (.var "fill.i") (.add (.var "catalog.count") (.lit 2)))
      (.assign "coefficient.positive" (.lit 1)) (.assign "coefficient.positive" (.lit 0))))
  (.ite (.eq (.var "fill.i") (.lit 1)) (.assign "coefficient.negative" (.lit 1)) (.assign "coefficient.negative" (.lit 0)))





def countExpr : Expr := .add (.lit 2) (.mul (.var "catalog.count") (.add (.var "graph.n") (.lit 5)))

def command : Com := .seq (.assign "fill.length" countExpr) (NativeRationalTabulate.command read)









end Lax263307Proofs.NativeMomentVectors

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentInput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP NativeMomentFamily
open Lax109476.RationalEncoding

abbrev M (n r : ℕ) := NativeMomentAssembly.rowCount n r





def rowCountExpr : Expr := .add (.lit 2) (.mul (.var "catalog.count") (.add (.var "graph.n") (.lit 4)))

def header : Com := .seq (.assign "moment.rows" rowCountExpr)
  (.seq (.assign "lp.length" (.lit 0))
    (.seq (RamWordBuffer.append "lp.input" "lp.length" (.var "moment.rows"))
      (RamWordBuffer.append "lp.input" "lp.length" (.var "catalog.count"))))





def length (n r : ℕ) : ℕ := 2+3*(M n r*dimension n r)+3*(M n r+dimension n r)

def cost (n r : ℕ) : ℕ := (22*n+129)*(M n r*dimension n r)+57*(M n r+dimension n r)+111

def command : Com := .seq header (.seq (NativeMomentMatrix.command NativeMomentMatrix.allKinds) NativeMomentVectors.command)





end Lax263307Proofs.NativeMomentInput

end

-- Solutions.RAM_Lax263307Proofs_NativeRationalRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-!
A canonical rational reader whose input-buffer name is an explicit
code parameter.
-/

namespace Lax263307Proofs.NativeRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding


def command (array : String) : Com := .seq (.assign "rat.s" (.get array (.var "read.cursor")))
  (.seq (.assign "rat.n" (.get array (.add (.var "read.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get array (.add (.var "read.cursor") (.lit 2))))
      (.assign "read.cursor" (.add (.var "read.cursor") (.lit 3)))))





end Lax263307Proofs.NativeRationalRead

end

-- Solutions.RAM_Lax263307Proofs_NativeSignedSum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic









def setup : Com := .seq (.assign "sum.value.s" (.lit 0))
  (.seq (.assign "sum.value.n" (.lit 0)) (.assign "sum.value.d" (.lit 1)))

def read : Com := .seq (.assign "read.cursor" (.mul (.lit 3) (.var "sum.i")))
  (NativeRationalRead.command "sum.input")

def advance : Com := .assign "sum.i" (.add (.var "sum.i") (.lit 1))

def body : Com := .seq read (.seq NativeSignedAccumulate.command advance)

def command : Com := .seq setup
  (.seq (.seq (.assign "sum.i" (.lit 0)) (.while (.lt (.var "sum.i") (.var "sum.count")) body))
    (load "sum.value"))









end Lax263307Proofs.NativeSignedSum

end

-- Solutions.RAM_Lax263307Proofs_NativeNaturalPower
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState





def step : Com := .seq (.assign "power.value" (.mul (.var "power.value") (.var "power.base")))
  (.assign "power.i" (.add (.var "power.i") (.lit 1)))

def command : Com := .seq (.assign "power.value" (.lit 1))
  (.seq (.assign "power.i" (.lit 0))
    (.while (.lt (.var "power.i") (.var "power.exponent")) step))





end Lax263307Proofs.NativeNaturalPower

end

-- Solutions.RAM_Lax263307_ParameterResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax263307.ParameterResources

open MomentLP (dimension)
open AlgorithmParameters

def resource (a K B n D : ℕ) : ℕ :=
  n + D + load B n D + sparsity a K B n D + level a K B n D +
    dimension n (level a K B n D) + radiusDenominator a K B n D +
    precision a K B n D + iterations a K B n D + (n + 1) ^ cutoff a K B n D

end Lax263307.ParameterResources

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeParameters
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.AlgorithmParameters

def guard (a K b n D : ℕ) : ℕ :=
  a+K+12*b+n+D+2*n+(Nat.log2 n+1)+logarithm n+12*b*D+load b n D+
    (load b n D+1)+(4*a+2)+(load b n D+1)^(4*a+2)+targetThreshold a K b n D+
    sparsity a K b n D+level a K b n D+floorDenominator a K b n D+20





def setup (a b : ℕ) : Com :=
  .seq (.assign "node.load" (.mul (.mul (.lit (12*b)) (.var "node.D")) (.var "node.logarithm")))
    (.seq (.assign "power.base" (.add (.var "node.load") (.lit 1)))
      (.assign "power.exponent" (.lit (4*a+2))))

def finish (K : ℕ) : Com :=
  .seq (.assign "node.threshold" (.mul (.lit K) (.var "power.value")))
    (.seq (.assign "node.sparsity" (.mul (.lit 2) (.var "node.threshold")))
      (.seq (.assign "node.level" (.mul (.var "node.sparsity") (.var "node.log")))
        (.seq (.assign "node.cutoff" (.var "node.level"))
          (.seq (.assign "moment.r" (.var "node.level"))
            (.assign "node.floorDen" (.mul (.mul (.lit 2) (.var "graph.n")) (.var "node.level")))))))

def command (a K b : ℕ) : Com := .seq NativeLogarithms.command
  (.seq (setup a b) (.seq NativeNaturalPower.command (finish K)))











end Lax263307Proofs.NativeNodeParameters

end

-- Solutions.RAM_Lax263307Proofs_NativeTargetDriver
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeTargetDriver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks



def Reply {n : ℕ} (answer : Option (Finset (Fin n))) (σ : Env) : Prop :=
  match answer with
  | none => σ.vars "recursion.return.tag"=0
  | some I => σ.vars "recursion.return.tag"=1 ∧ σ.vars "recursion.return.mask"=mask I















end Lax263307Proofs.NativeTargetDriver

end

-- Solutions.RAM_Lax263307Proofs_NativeAttemptReply
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeAttemptReply

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

def someCommand (ret : ℕ) : Com := .seq NativeMasks.command
  (.seq (.assign "recursion.return.tag" (.lit 1))
    (.seq (.assign "recursion.return.mask" (.var "mask.value")) (.assign "machine.phase" (.lit ret))))

def noneCommand (ret : ℕ) : Com := .seq (.assign "recursion.return.tag" (.lit 0))
  (.seq (.assign "recursion.return.mask" (.lit 0)) (.assign "machine.phase" (.lit ret)))

def command (ret : ℕ) : Com := .ite (.eq (.var "target.found") (.lit 1)) (someCommand ret) (noneCommand ret)







end Lax263307Proofs.NativeAttemptReply

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeDispatch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 AlgorithmParameters







def select (small large ret : ℕ) : Com :=
  .ite (.lt (.var "node.k") (.add (.var "node.cutoff") (.lit 1)))
    (.assign "machine.phase" (.lit small))
    (.ite (.lt (.var "graph.n") (.var "node.k")) (NativeAttemptReply.noneCommand ret)
      (.ite (.eq (.var "recursion.fuel") (.lit 0)) (NativeAttemptReply.noneCommand ret)
        (.assign "machine.phase" (.lit large))))





def command (a K b small large ret : ℕ) : Com :=
  .ite (.lt (.var "graph.n") (.lit 2)) (.assign "machine.phase" (.lit small))
    (.seq (NativeNodeParameters.command a K b) (select small large ret))





end Lax263307Proofs.NativeNodeDispatch

end

-- Solutions.RAM_Lax263307Proofs_NativeSmallAttempt
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSmallAttempt

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307



def command (ret : ℕ) : Com := .seq (.assign "target.k" (.var "node.k"))
  (.seq NativeExhaustive.command (NativeAttemptReply.command ret))



end Lax263307Proofs.NativeSmallAttempt

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeAliases
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeAliases

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters

def command (b : ℕ) : Com := .seq (.assign "row.k" (.var "node.k"))
  (.seq (.assign "conditioning.k" (.var "node.k"))
    (.seq (.assign "conditioning.p" (.var "node.sparsity"))
      (.seq (.assign "algorithm.load" (.var "node.load"))
        (.seq (.assign "algorithm.D" (.var "node.D")) (.assign "class.B" (.lit b))))))





end Lax263307Proofs.NativeNodeAliases

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentSetup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP

abbrev N (n r : ℕ) := dimension n r

def guardBound (n k r : ℕ) : ℕ :=
  n*n+(n+1)*(r+3)+NativeMomentInput.length n r+n+k+r+N n r+20



def catalogCost (n r : ℕ) : ℕ :=
  (54*(n+1)*(r+3)+(69*n+33)*N n r+41)*(r+3)+8

def cost (n r : ℕ) : ℕ := catalogCost n r+(38*n*n+42*n+60)*N n r+18

def command : Com := .seq (.assign "catalog.limit" (.add (.var "moment.r") (.lit 3)))
  (.seq NativeCatalog.command NativeCatalogMetadata.command)





end Lax263307Proofs.NativeMomentSetup

end

-- Solutions.RAM_Lax263307Proofs_NativeNodePrecision
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodePrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters

def radius (n D N b r : ℕ) : ℕ := 256*N*n*n*D*D*b^r
def prec (n D N b r : ℕ) : ℕ := radius n D N b r+2
def count (n D N b r : ℕ) : ℕ := 4*(N+1)*(prec n D N b r*N+1)
def guard (n D N b r : ℕ) : ℕ :=
  256+n+D+N+b+r+b^r+256*N+256*N*n+256*N*n*n+256*N*n*n*D+
    256*N*n*n*D*D+radius n D N b r+prec n D N b r+(N+1)+prec n D N b r*N+
    (prec n D N b r*N+1)+4*(N+1)+count n D N b r+20





def setup : Com := .seq (.assign "power.base" (.var "node.floorDen"))
  (.assign "power.exponent" (.var "moment.r"))

def saveRadius : Com := .seq (.assign "node.floorPower" (.var "power.value"))
  (.assign "node.radius" (.mul (.mul (.mul (.mul (.mul (.mul (.lit 256) (.var "catalog.count"))
    (.var "graph.n")) (.var "graph.n")) (.var "node.D")) (.var "node.D")) (.var "power.value")))

def saveBudgets : Com := .seq (.assign "node.precision" (.add (.var "node.radius") (.lit 2)))
  (.seq (.assign "round.limit" (.mul (.mul (.lit 4) (.add (.var "catalog.count") (.lit 1)))
    (.add (.mul (.var "node.precision") (.var "catalog.count")) (.lit 1))))
    (.assign "vec.n" (.var "catalog.count")))

def command : Com := .seq setup (.seq NativeNaturalPower.command (.seq saveRadius saveBudgets))

















end Lax263307Proofs.NativeNodePrecision

end

-- Solutions.RAM_Lax263307Proofs_NativeSlice
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSlice

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def read (source : String) : Com := .assign "fill.value"
  (.get source (.add (.var "slice.start") (.var "fill.i")))

def command (source target : String) : Com := NativeTabulate.command target (read source)







end Lax263307Proofs.NativeSlice

end

-- Solutions.RAM_Lax263307Proofs_NativeProgramCache
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProgramCache

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def copy (source target lengthVar : String) : Com :=
  .seq (.assign "fill.length" (.var lengthVar))
    (.seq (.assign "slice.start" (.lit 0)) (NativeSlice.command source target))



def save : Com := .seq (.assign "node.programLength" (.var "lp.length"))
  (copy "lp.input" "moment.program" "lp.length")

def restore : Com := copy "moment.program" "lp.input" "node.programLength"





end Lax263307Proofs.NativeProgramCache

end

-- Solutions.RAM_Lax263307Proofs_NativeIntegerTable
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeIntegerTable

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def command (count : Expr) (read : Com) : Com := .seq (.assign "fill.length" count)
  (.seq (.assign "lp.length" (.lit 0)) (NativeRationalTabulate.command read))



end Lax263307Proofs.NativeIntegerTable

end

-- Solutions.RAM_Lax263307Proofs_NativeInitialCoordinates
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeInitialCoordinates

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Matrix



def read : Com := .seq (.assign "init.row" (.div (.var "fill.i") (.var "vec.n")))
  (.seq (.assign "init.col" (.sub (.var "fill.i") (.mul (.var "init.row") (.var "vec.n"))))
    (.seq (.ite (.eq (.var "init.row") (.var "init.col"))
      (.assign "coefficient.positive" (.lit 1)) (.assign "coefficient.positive" (.lit 0)))
      (.assign "coefficient.negative" (.lit 0))))



def zeroRead : Com := .seq (.assign "coefficient.positive" (.lit 0)) (.assign "coefficient.negative" (.lit 0))



end Lax263307Proofs.NativeInitialCoordinates

end

-- Solutions.RAM_Lax263307Proofs_NativeAppendBuffer
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState



def step (source target index cursor : String) : Com := .seq
  (RamWordBuffer.append target cursor (.get source (.var index)))
  (.assign index (.add (.var index) (.lit 1)))

def command (source target index cursor count : String) : Com := .seq (.assign index (.lit 0))
  (.while (.lt (.var index) (.var count)) (step source target index cursor))







end Lax263307Proofs.NativeAppendBuffer

end

-- Solutions.RAM_Lax263307Proofs_NativeQueryBlocks
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQueryBlocks

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def command (source : String) (count : Expr) : Com := .seq (.assign "query.length" count)
  (NativeAppendBuffer.command source "lp.word" "query.i" "lp.position" "query.length")



end Lax263307Proofs.NativeQueryBlocks

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedQuery
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRoundedQuery

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch

def shape {n : ℕ} (state : State n) : List ℕ := (List.ofFn fun i => encodeVector (state.1 i)).flatten
def normal {n : ℕ} (a : Fin n → ℤ) : List ℕ := encodeVector (rationalNormal a)
def center {n : ℕ} (state : State n) : List ℕ := encodeVector state.2





structure Data {n : ℕ} (k : ℕ) (state : State n) (a : Fin n → ℤ) (σ : Env) : Prop where
  order : σ.vars "vec.n"=n
  index : σ.vars "round.i"=k
  shape : Prefix (shape state) "round.shape" σ
  normal : Prefix (normal a) "round.normal" σ
  center : Prefix (center state) "round.center" σ
  room : (Lax263307.NativeRoundedStep.encodeInput k state a).length≤(σ.arrs "lp.word").length



def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "vec.n"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "round.i")))



def command : Com := .seq header
  (.seq (NativeQueryBlocks.command "round.shape" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))))
    (.seq (NativeQueryBlocks.command "round.normal" (.mul (.lit 3) (.var "vec.n")))
      (NativeQueryBlocks.command "round.center" (.mul (.lit 3) (.var "vec.n")))))



end Lax263307Proofs.NativeRoundedQuery

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedState
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRoundedState

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch
open NativeRoundedQuery



def shapeSetup : Com := .seq (.assign "fill.length" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))))
  (.assign "slice.start" (.lit 0))

def centerSetup : Com := .seq (.assign "fill.length" (.mul (.lit 3) (.var "vec.n")))
  (.assign "slice.start" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n"))))

def command : Com := .seq shapeSetup (.seq (NativeSlice.command "vm.output" "round.shape")
  (.seq centerSetup (NativeSlice.command "vm.output" "round.center")))







end Lax263307Proofs.NativeRoundedState

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedInitial
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeRoundedInitial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RoundedOracleSearch NativeRoundedQuery

def copy (target : String) (count : Expr) : Com :=
  .seq (.assign "fill.length" count)
    (.seq (.assign "slice.start" (.lit 0)) (NativeSlice.command "lp.input" target))









def matrixTable : Com := NativeIntegerTable.command (.mul (.var "vec.n") (.var "vec.n")) NativeInitialCoordinates.read
def centerTable : Com := NativeIntegerTable.command (.var "vec.n") NativeInitialCoordinates.zeroRead
def matrixCopy : Com := copy "round.shape" (.mul (.lit 3) (.mul (.var "vec.n") (.var "vec.n")))
def centerCopy : Com := copy "round.center" (.mul (.lit 3) (.var "vec.n"))
def command : Com := .seq matrixTable (.seq matrixCopy (.seq centerTable
  (.seq centerCopy (.assign "round.i" (.lit 0)))))











end Lax263307Proofs.NativeRoundedInitial

end

-- Solutions.RAM_Lax263307Proofs_NativeLargeSetup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeLargeSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 MomentLP RoundedOracleSearch

def command : Com := .seq NativeMomentInput.command (.seq NativeProgramCache.save
  (.seq NativeNodePrecision.command NativeRoundedInitial.command))

def timeBound (n r : ℕ) : ℕ := NativeMomentInput.cost n r+16*NativeMomentInput.length n r+
  12*r+105*(dimension n r*dimension n r)+91*dimension n r+108







end Lax263307Proofs.NativeLargeSetup

end

-- Solutions.RAM_Lax263307Proofs_NativeLargeNode
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeLargeNode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 AlgorithmParameters MomentLP RoundedOracleSearch

def command (a K b : ℕ) : Com := .seq (NativeNodeParameters.command a K b)
  (.seq (NativeNodeAliases.command b) (.seq NativeMomentSetup.command NativeLargeSetup.command))

def cost (a n r : ℕ) : ℕ := 12*n.size+12*(2*n).size+12*(4*a+2)+76+
  NativeMomentSetup.cost n r+NativeLargeSetup.timeBound n r









end Lax263307Proofs.NativeLargeNode

end

-- Solutions.RAM_Lax263307Proofs_NativeScaleFraction
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeScaleFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamArithmetic
open NativeSignedArithmetic





def command : Com := .seq (.assign "rat.n" (.mul (.var "rat.n") (.var "scale.value"))) normalizeFraction



end Lax263307Proofs.NativeScaleFraction

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionCenter
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeProjectionCenter

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding NativeSignedArithmetic







def setup : Com := .seq (.assign "scale.value" (.mul (.lit 4) (.var "vec.n")))
  (.assign "lp.position" (.lit 0))
def read : Com := .seq (.assign "read.cursor" (.mul (.lit 3) (.var "scale.i")))
  (.seq (NativeRationalRead.command "round.center") NativeScaleFraction.command)
def vector : Com := .seq setup (RamVectorEncoding.command "scale.i" "vec.n" read)
def command : Com := .seq vector (NativeProgramCache.copy "lp.word" "projection.center" "lp.position")









end Lax263307Proofs.NativeProjectionCenter

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeTolerance
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding
open Lax263307

def denominator (n D R : ℕ) : ℕ := 32*n*n*D*D*R
def tolerance (n D R : ℕ) : ℚ := 1/(denominator n D R : ℚ)
def guard (n D R : ℕ) : ℕ := 32+n+D+R+32*n+32*n*n+32*n*n*D+32*n*n*D*D+denominator n D R+20




def setup : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1))
    (.seq (.assign "rat.d" (.mul (.mul (.mul (.mul (.mul (.lit 32) (.var "graph.n"))
      (.var "graph.n")) (.var "node.D")) (.var "node.D")) (.var "node.floorPower")))
      (.assign "lp.position" (.lit 0))))

def command : Com := .seq setup (.seq RamFractionEncoding.emit
  (NativeProgramCache.copy "lp.word" "projection.tolerance" "lp.position"))









end Lax263307Proofs.NativeNodeTolerance

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionPrepare
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeProjectionPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding NativeSignedArithmetic

def command : Com := .seq NativeProgramCache.restore
  (.seq NativeProjectionCenter.command NativeNodeTolerance.command)



end Lax263307Proofs.NativeProjectionPrepare

end

-- Solutions.RAM_Lax263307Proofs_NativeLPRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeLPRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState

open Lax109476.LinearProgram Lax109476.RationalEncoding

def matrixPosition : Com := .assign "read.cursor" (.add (.lit 2) (.mul (.lit 3)
  (.add (.mul (.var "projection.i") (.var "projection.n")) (.var "projection.j"))))

def matrix : Com := .seq matrixPosition (NativeRationalRead.command "lp.input")





def boundPosition : Com := .assign "read.cursor" (.add (.lit 2) (.mul (.lit 3)
  (.add (.mul (.var "projection.m") (.var "projection.n")) (.var "projection.i"))))

def bound : Com := .seq boundPosition (NativeRationalRead.command "lp.input")





def centerPosition : Com := .assign "read.cursor" (.mul (.lit 3) (.var "projection.local"))
def center : Com := .seq centerPosition (NativeRationalRead.command "projection.center")



end Lax263307Proofs.NativeLPRead

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceUnits
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeDistanceUnits

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamFractionPrimitives

def unit (negative : Bool) : Com := if negative then negativeOne else one





def matching (negative : Bool) : Com := .ite (.eq (.var "projection.local") (.var "projection.j")) (unit negative) zero





def extended (negative : Bool) : Com := .ite (.lt (.var "projection.j") (.var "projection.n")) (matching negative) negativeOne





end Lax263307Proofs.NativeDistanceUnits

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceCoefficient
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs.RamFractionPrimitives
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceUnits

def oldRow : Com := .ite (.lt (.var "projection.j") (.var "projection.n")) NativeLPRead.matrix zero





def localRow : Com := .assign "projection.local" (.sub (.var "projection.i") (.var "projection.m"))
def subtractColumns : Com := .assign "projection.local" (.sub (.var "projection.local") (.var "projection.n"))

def newRows : Com := .seq localRow (.ite (.lt (.var "projection.local") (.var "projection.n"))
  (extended false) (.seq subtractColumns (extended true)))

def command : Com := .ite (.lt (.var "projection.i") (.var "projection.m")) oldRow newRows







end Lax263307Proofs.NativeDistanceCoefficient

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceData
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeDistanceData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection


abbrev rows (m n : ℕ) : ℕ := m+(n+n)
abbrev columns (n : ℕ) : ℕ := n+1

def wordLength (m n : ℕ) : ℕ := 2+3*(rows m n*columns n+rows m n+columns n)
def shapeSize (m n : ℕ) : ℕ := 3*(m*n)+5*m+5*n+wordLength m n+30










def Height (B : ℕ) (q : ℚ) : Prop := q.num.natAbs < B ∧ q.den < B

structure Bounded {m n : ℕ} (B : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) : Prop where
  one : 1 < B
  matrix : ∀ i j,Height B (P.A i j)
  bound : ∀ i,Height B (P.b i)
  center : ∀ i,Height B (x i)







end Lax263307Proofs.NativeDistanceData

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceMetadata
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceMetadata

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceData

def readDimensions : Com := .seq (.assign "projection.m" (.get "lp.input" (.lit 0)))
  (.assign "projection.n" (.get "lp.input" (.lit 1)))



def sizes : Com := .seq (.assign "lp.rows" (.add (.var "projection.m") (.add (.var "projection.n") (.var "projection.n"))))
  (.seq (.assign "lp.columns" (.add (.var "projection.n") (.lit 1)))
    (.assign "projection.matrixLength" (.mul (.var "lp.rows") (.var "lp.columns"))))



def command : Com := .seq readDimensions sizes



def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.rows"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.columns")))



end Lax263307Proofs.NativeDistanceMetadata

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceMatrix
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

def coordinates : Com := .seq (.assign "projection.i" (.div (.var "projection.entry") (.var "lp.columns")))
  (.assign "projection.j" (.sub (.var "projection.entry") (.mul (.var "projection.i") (.var "lp.columns"))))



def read : Com := .seq coordinates NativeDistanceCoefficient.command



def command : Com := RamVectorEncoding.command "projection.entry" "projection.matrixLength" read



end Lax263307Proofs.NativeDistanceMatrix

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceBound
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceBound

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs.RamFractionPrimitives
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceCoefficient

def newRows : Com := .seq localRow (.ite (.lt (.var "projection.local") (.var "projection.n"))
  NativeLPRead.center (.seq subtractColumns (.seq NativeLPRead.center negate)))

def command : Com := .ite (.lt (.var "projection.i") (.var "projection.m")) NativeLPRead.bound newRows







end Lax263307Proofs.NativeDistanceBound

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceVectors
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs Lax455465Proofs.RamFractionPrimitives
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

def readBound : Com := .seq (.assign "projection.i" (.var "projection.entry")) NativeDistanceBound.command



def readObjective : Com := .ite (.lt (.var "projection.entry") (.var "projection.n")) zero negativeOne





def bounds : Com := RamVectorEncoding.command "projection.entry" "lp.rows" readBound

def objectives : Com := RamVectorEncoding.command "projection.entry" "lp.columns" readObjective





end Lax263307Proofs.NativeDistanceVectors

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceInput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

def construct : Com := .seq NativeDistanceMetadata.header (.seq NativeDistanceMatrix.command
  (.seq NativeDistanceVectors.bounds NativeDistanceVectors.objectives))







def command : Com := .seq NativeDistanceMetadata.command construct

def cost (m n : ℕ) : ℕ := 85*(rows m n*columns n)+87*rows m n+45*columns n+54




end Lax263307Proofs.NativeDistanceInput

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleCalls
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOracleCalls

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- This generic invocation preserves the specific function chosen in the
functional algorithm. It applies equally to the LP and flow solvers. -/
def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq (RamLpPrepare.command coefficients) (RamVirtualProgram.execute p)



end Lax263307Proofs.NativeOracleCalls

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeDistanceOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307.DistanceProjection NativeDistanceData

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeDistanceInput.command (NativeOracleCalls.command p coeff)

def cost (m n : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ)
    (T size : ℕ) : ℕ := NativeDistanceInput.cost m n+
  (((12*size+39)*wordLength m n+6*coeff.length+29)+
    ((T+1)*(4*p.length+32*T+104)+18))



end Lax263307Proofs.NativeDistanceOracle

end

-- Solutions.RAM_Lax263307Proofs_NativeCertificateRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCertificateRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection

def tag : Com := .assign "projection.tag" (.get "vm.output" (.lit 0))





def primalPosition : Com := .assign "read.cursor"
  (.add (.lit 1) (.mul (.lit 3) (.var "certificate.index")))
def primal : Com := .seq primalPosition (NativeRationalRead.command "vm.output")



def dualPosition : Com := .assign "read.cursor" (.add (.lit 1)
  (.mul (.lit 3) (.add (.add (.var "projection.n") (.lit 1)) (.var "certificate.index"))))
def dual : Com := .seq dualPosition (NativeRationalRead.command "vm.output")



end Lax263307Proofs.NativeCertificateRead

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionDecide
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionDecide

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeSignedArithmetic

def readDistance : Com := .seq (.assign "certificate.index" (.var "projection.n")) NativeCertificateRead.primal

def record : Com := .ite (.eq (.var "cmp.le") (.lit 1))
  (.assign "projection.kind" (.lit 0)) (.assign "projection.kind" (.lit 1))

def optimal : Com := .seq readDistance (.seq (save "left") (.seq (load "projection.tolerance")
  (.seq (save "right") (.seq RamComparison.compareFraction record))))

def reject : Com := .assign "projection.kind" (.lit 2)

def command : Com := .seq NativeCertificateRead.tag
  (.ite (.eq (.var "projection.tag") (.lit 0)) optimal reject)













end Lax263307Proofs.NativeProjectionDecide

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionNormal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeSignedArithmetic

def plus : Com := .seq (.assign "certificate.index" (.add (.var "projection.m") (.var "projection.entry")))
  NativeCertificateRead.dual

def minus : Com := .seq (.assign "certificate.index"
  (.add (.add (.var "projection.m") (.var "projection.n")) (.var "projection.entry")))
  NativeCertificateRead.dual

def command : Com := .seq plus (.seq RamFractionPrimitives.negate (.seq (save "left")
  (.seq minus (.seq (save "right") RamRational.addFraction))))











end Lax263307Proofs.NativeProjectionNormal

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionVectors
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeSignedArithmetic
open NativeProjectionNormal

def normalCommand : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "projection.entry" "projection.n" NativeProjectionNormal.command)



end Lax263307Proofs.NativeProjectionVectors

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionNear
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionNear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.DistanceProjection



def setup : Com := .seq (.assign "slice.start" (.lit 1))
  (.seq (.assign "fill.length" (.mul (.lit 3) (.var "projection.n")))
    (.assign "lp.position" (.var "fill.length")))

def command : Com := .seq setup (NativeSlice.command "vm.output" "lp.word")



end Lax263307Proofs.NativeProjectionNear

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionResult
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeProjectionResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeSignedArithmetic

/-- The projected search discards the numerical dual bound, so its native
result stores only the branch tag and the point or separating normal. -/
def Output {n : ℕ} : Outcome n → Env → Prop
  | .near x, σ => σ.vars "projection.kind"=0 ∧ Prefix (encodeVector x) "lp.word" σ ∧ σ.vars "lp.position"=3*n
  | .far a _, σ => σ.vars "projection.kind"=1 ∧ Prefix (encodeVector a) "lp.word" σ ∧ σ.vars "lp.position"=3*n
  | .reject, σ => σ.vars "projection.kind"=2



def finish : Com := .ite (.eq (.var "projection.kind") (.lit 0)) NativeProjectionNear.command
  (.ite (.eq (.var "projection.kind") (.lit 1)) NativeProjectionVectors.normalCommand .skip)

def command : Com := .seq NativeDistanceMetadata.readDimensions
  (.seq NativeProjectionDecide.command finish)

def cost (M n : ℕ) : ℕ := (36*(M^2).size+300)*(n+1)+200







end Lax263307Proofs.NativeProjectionResult

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionTolerance
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding NativeSignedArithmetic

def command : Com := .seq (.assign "read.cursor" (.lit 0))
  (.seq (NativeRationalRead.command "projection.tolerance") (save "projection.tolerance"))



end Lax263307Proofs.NativeProjectionTolerance

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeProjectionOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeDistanceData

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq (NativeDistanceOracle.command p coeff)
    (.seq NativeProjectionTolerance.command NativeProjectionResult.command)







end Lax263307Proofs.NativeProjectionOracle

end

-- Solutions.RAM_Lax263307Proofs_NativeWordLookup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeWordLookup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs





def read (array : String) : Com :=
  .assign "lookup.current" (.get array (.var "lookup.j"))

def update : Com := .seq
  (.ite (.eq (.var "lookup.current") (.var "lookup.key"))
    (.assign "lookup.result" (.var "lookup.j")) .skip)
  (.assign "lookup.j" (.add (.var "lookup.j") (.lit 1)))

def step (array : String) : Com := .seq (read array) update

def command (array : String) : Com := .seq (.assign "lookup.result" (.var "lookup.count"))
  (.seq (.assign "lookup.j" (.lit 0))
    (.while (.lt (.var "lookup.j") (.var "lookup.count")) (step array)))





end Lax263307Proofs.NativeWordLookup

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentValue
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeMomentValue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic
open NativeCatalogMetadata













def command : Com := .seq (.assign "lookup.count" (.var "catalog.count"))
  (.seq (NativeWordLookup.command "catalog.mask")
    (.seq (.assign "read.cursor" (.mul (.lit 3) (.var "lookup.result")))
      (NativeRationalRead.command "near.moments")))



end Lax263307Proofs.NativeMomentValue

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentStorage
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeMomentStorage

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic NativeCatalogMetadata

def setup : Com := .seq (.assign "slice.start" (.lit 0))
  (.assign "fill.length" (.mul (.lit 3) (.var "catalog.count")))

def command : Com := .seq setup (NativeSlice.command "lp.word" "near.moments")



end Lax263307Proofs.NativeMomentStorage

end

-- Solutions.RAM_Lax263307Proofs_NativeConditioningVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeConditioningVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic
open NativeCatalogMetadata





def key : Com := .assign "lookup.key"
  (.or (.var "conditioning.mask") (.shiftl (.lit 1) (.var "conditioning.v")))

def read : Com := .seq key NativeMomentValue.command

def command : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "conditioning.v" "graph.n" read)







end Lax263307Proofs.NativeConditioningVector

end

-- Solutions.RAM_Lax263307Proofs_NativeCutRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding NativeSignedArithmetic



def command : Com := .seq (.assign "read.cursor" (.mul (.lit 3) (.var "cut.i")))
  (NativeRationalRead.command "cut.source")



end Lax263307Proofs.NativeCutRead

end

-- Solutions.RAM_Lax263307Proofs_NativeQuadraticProduct
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQuadraticProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeCutRead

def row : Com := .assign "cut.i" (.div (.var "quadratic.i") (.var "projection.n"))

def col : Com := .assign "cut.i" (.sub (.var "quadratic.i")
  (.mul (.div (.var "quadratic.i") (.var "projection.n")) (.var "projection.n")))





def command : Com := .seq row (.seq NativeCutRead.command (.seq (save "left")
  (.seq col (.seq NativeCutRead.command (.seq (save "right") multiplyFraction)))))



end Lax263307Proofs.NativeQuadraticProduct

end

-- Solutions.RAM_Lax263307Proofs_NativeQuadraticTerms
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQuadraticTerms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic









def readEdge : Com := .assign "quadratic.edge" (.get "search.graph" (.var "quadratic.i"))

def finish : Com := .ite (.eq (.var "quadratic.edge") (.lit 0))
  RamFractionPrimitives.zero NativeQuadraticProduct.command

def command : Com := .seq readEdge finish



end Lax263307Proofs.NativeQuadraticTerms

end

-- Solutions.RAM_Lax263307Proofs_NativeQuadraticVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQuadraticVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeQuadraticTerms







def setup : Com := .seq (.assign "lp.position" (.lit 0))
  (.assign "quadratic.count" (.mul (.var "projection.n") (.var "projection.n")))

def command : Com := .seq setup
  (RamVectorEncoding.command "quadratic.i" "quadratic.count" NativeQuadraticTerms.command)



end Lax263307Proofs.NativeQuadraticVector

end

-- Solutions.RAM_Lax263307Proofs_NativeQuadraticSum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQuadraticSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeQuadraticTerms

def height (M n : ℕ) : ℕ := (2*M^2)^(n*n+1)

def cost (M n : ℕ) : ℕ :=
  (36*(M^2).size+36*((height M n)^2).size+369)*(n*n)+44

def prepareSum : Com := .seq (.assign "slice.start" (.lit 0))
  (.seq (.assign "fill.length" (.mul (.lit 3) (.var "quadratic.count")))
    (.assign "sum.count" (.var "quadratic.count")))

def command : Com := .seq NativeQuadraticVector.command
  (.seq prepareSum (.seq (NativeSlice.command "lp.word" "sum.input") NativeSignedSum.command))



end Lax263307Proofs.NativeQuadraticSum

end

-- Solutions.RAM_Lax263307Proofs_NativeConditioningNumerator
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeConditioningNumerator

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata









def prepareCopy : Com := .seq (.assign "projection.n" (.var "graph.n"))
  (.seq (.assign "slice.start" (.lit 0)) (.assign "fill.length" (.mul (.lit 3) (.var "graph.n"))))

def prepare : Com := .seq NativeConditioningVector.command
  (.seq prepareCopy (NativeSlice.command "lp.word" "cut.source"))

def command : Com := .seq prepare NativeQuadraticSum.command

def cost (M n r : ℕ) : ℕ := (17*N n r+120)*n+22+NativeQuadraticSum.cost M n





end Lax263307Proofs.NativeConditioningNumerator

end

-- Solutions.RAM_Lax263307Proofs_NativeConditioningFloor
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeConditioningFloor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def base (n p : ℕ) : ℕ := 2*n*p*(Nat.log2 n+1)



def preparePower : Com := .seq
  (.assign "power.base" (.mul (.mul (.mul (.lit 2) (.var "graph.n")) (.var "conditioning.p")) (.var "size.count")))
  (.assign "power.exponent" (.var "moment.r"))

def command : Com := .seq (.assign "size.value" (.var "graph.n"))
  (.seq RamBitSize.word (.seq preparePower
    (.seq NativeNaturalPower.command (.assign "conditioning.floorDen" (.var "power.value")))))





end Lax263307Proofs.NativeConditioningFloor

end

-- Solutions.RAM_Lax263307Proofs_NativeConditioningTest
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeConditioningTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational NativeSignedArithmetic

/-- Include every intermediate unsigned product in the overflow guard. -/
def resource (k p D n d m e : ℕ) : ℕ := p+k+D+n+d+m+e+3+
  p*m+p*m*d+p*m*d*d+2*k+2*k*k+2*k*k*n+2*k*k*n*n+2*k*k*n*n*e+D*n



def products : Com := .seq
  (.assign "conditioning.left" (.mul (.mul (.mul (.var "conditioning.p") (.var "conditioning.edge.n"))
    (.var "conditioning.a.d")) (.var "conditioning.a.d")))
  (.seq (.assign "conditioning.right" (.mul (.mul (.mul (.mul (.mul (.lit 2) (.var "conditioning.k"))
    (.var "conditioning.k")) (.var "conditioning.a.n")) (.var "conditioning.a.n")) (.var "conditioning.edge.d")))
    (.assign "conditioning.floorProduct" (.mul (.var "conditioning.floorDen") (.var "conditioning.a.n"))))

def answer (b : ℕ) : Com := .assign "conditioning.passes" (.lit b)

def decideCommand : Com := .ite (.eq (.var "conditioning.a.s") (.lit 0))
  (.ite (.lt (.lit 0) (.var "conditioning.a.n"))
    (.ite (.lt (.var "conditioning.floorProduct") (.var "conditioning.a.d")) (answer 0)
      (.ite (.eq (.var "conditioning.edge.s") (.lit 1)) (answer 1)
        (.ite (.lt (.var "conditioning.right") (.var "conditioning.left")) (answer 0) (answer 1))))
    (answer 0)) (answer 0)

def command : Com := .seq products decideCommand





end Lax263307Proofs.NativeConditioningTest

end

-- Solutions.RAM_Lax263307Proofs_NativeHeavyCandidate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeHeavyCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata NativeConditioningNumerator



def command : Com := .seq (.assign "lookup.key" (.var "conditioning.mask"))
  (.seq NativeMomentValue.command (.seq (save "conditioning.a")
    (.seq NativeConditioningNumerator.command (.seq (save "conditioning.edge") NativeConditioningTest.command))))

def cost (M n r : ℕ) : ℕ := 17*N n r+91+NativeConditioningNumerator.cost M n r



end Lax263307Proofs.NativeHeavyCandidate

end

-- Solutions.RAM_Lax263307Proofs_NativeConditioningResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeConditioningResources

open Lax263307 RationalConditioning NativeSignedArithmetic

def testBound (k p D M H : ℕ) : ℕ := NativeConditioningTest.resource k p D M M H H







end Lax263307Proofs.NativeConditioningResources

end

-- Solutions.RAM_Lax263307Proofs_NativeConditioningEntry
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeConditioningEntry

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata









def read : Com := .seq
  (.assign "conditioning.mask" (.get "catalog.mask" (.var "scan.i")))
  (.assign "conditioning.card" (.get "catalog.card" (.var "scan.i")))



def choose : Com := .ite (.lt (.var "moment.r") (.var "conditioning.card"))
  (.assign "conditioning.passes" (.lit 0)) NativeHeavyCandidate.command

def command : Com := .seq read (.seq choose (.assign "scan.accepted" (.var "conditioning.passes")))

def cost (M n r : ℕ) := NativeHeavyCandidate.cost M n r+12



end Lax263307Proofs.NativeConditioningEntry

end

-- Solutions.RAM_Lax263307Proofs_NativeFirstScan
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeFirstScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def update : Com := .seq
  (.ite (.eq (.var "scan.accepted") (.lit 1))
    (.ite (.eq (.var "scan.result") (.var "scan.count"))
      (.assign "scan.result" (.var "scan.i")) .skip) .skip)
  (.assign "scan.i" (.add (.var "scan.i") (.lit 1)))

def command (read : Com) : Com := .seq (.assign "scan.result" (.var "scan.count"))
  (.seq (.assign "scan.i" (.lit 0)) (.while (.lt (.var "scan.i") (.var "scan.count")) (.seq read update)))







end Lax263307Proofs.NativeFirstScan

end

-- Solutions.RAM_Lax263307Proofs_NativeHeavySearch
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeHeavySearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata NativeConditioningEntry



def finish : Com := .ite (.lt (.var "scan.result") (.var "catalog.count"))
  (.seq (.assign "conditioning.choice" (.get "catalog.mask" (.var "scan.result")))
    (.assign "conditioning.found" (.lit 1)))
  (.assign "conditioning.found" (.lit 0))





def command : Com := .seq NativeConditioningFloor.command
  (.seq (.assign "scan.count" (.var "catalog.count"))
    (.seq (NativeFirstScan.command NativeConditioningEntry.command) finish))

def cost (M n r : ℕ) := 12*n.size+12*r+50+(NativeConditioningEntry.cost M n r+18)*N n r



end Lax263307Proofs.NativeHeavySearch

end

-- Solutions.RAM_Lax263307Proofs_NativePositiveQuotient
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativePositiveQuotient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic





def positive : Com := .ite (.eq (.var "rat.s") (.lit 1)) RamFractionPrimitives.zero .skip





def command : Com := .seq (load "quotient.denominator")
  (.seq (save "left") (.seq invertFraction (.seq (save "right")
    (.seq (load "quotient.numerator") (.seq (save "left") (.seq multiplyFraction positive))))))





end Lax263307Proofs.NativePositiveQuotient

end

-- Solutions.RAM_Lax263307Proofs_NativeNearCosts
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 900000

namespace Lax263307Proofs.NativeNearCosts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata













def read : Com := .seq NativeConditioningVector.read
  (.seq (save "quotient.numerator") NativePositiveQuotient.command)



def vector : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "conditioning.v" "graph.n" read)



def prepare : Com := .seq (.assign "lookup.key" (.var "conditioning.mask"))
  (.seq NativeMomentValue.command (save "quotient.denominator"))



def copySetup : Com := .seq (.assign "slice.start" (.lit 0)) (.assign "fill.length" (.mul (.lit 3) (.var "graph.n")))

def command : Com := .seq prepare (.seq vector (.seq copySetup (NativeSlice.command "lp.word" "near.costs")))



end Lax263307Proofs.NativeNearCosts

end

-- Solutions.RAM_Lax263307Proofs_NativeFullSetMask
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFullSetMask

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks



def step : Com := .seq (.assign "separator.remaining"
  (.or (.var "separator.remaining") (.shiftl (.lit 1) (.var "separator.init.i"))))
  (.assign "separator.init.i" (.add (.var "separator.init.i") (.lit 1)))



def command : Com := .seq (.assign "separator.remaining" (.lit 0))
  (.seq (.assign "separator.init.i" (.lit 0)) (.while (.lt (.var "separator.init.i") (.var "graph.n")) step))



end Lax263307Proofs.NativeFullSetMask

end

-- Solutions.RAM_Lax263307Proofs_NativeSelectedVertices
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeSelectedVertices

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet





def choose : Com := .ite (.eq (.var "restrict.bit") (.lit 1))
  (RamWordBuffer.append "restrict.vertices" "restrict.count" (.var "restrict.i")) .skip

def step : Com := .seq (.assign "restrict.bit" (.get "subset.bits" (.var "restrict.i")))
  (.seq choose (.assign "restrict.i" (.add (.var "restrict.i") (.lit 1))))



def command : Com := .seq (.assign "restrict.count" (.lit 0))
  (.seq (.assign "restrict.i" (.lit 0)) (.while (.lt (.var "restrict.i") (.var "graph.n")) step))



end Lax263307Proofs.NativeSelectedVertices

end

-- Solutions.RAM_Lax263307Proofs_NativeLargeCapacity
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeLargeCapacity

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax263307 NativeSignedArithmetic

def numerator (b n r k : ℕ) : ℕ := b*(Nat.log2 (2*n)+1)*(2*r)*(2*r)*(3*k)
def denominator (n load : ℕ) : ℕ := load*n*n






def resource (b n r load k : ℕ) : ℕ :=
  let L := Nat.log2 (2*n)+1
  b+n+r+load+k+L+2*n+2*r+3*k+b*L+b*L*(2*r)+b*L*(2*r)*(2*r)+
    2*numerator b n r k+load*n+2*denominator n load+20



def products : Com := .seq
  (.assign "large.numerator" (.mul (.mul (.mul (.mul (.var "class.B") (.var "size.count"))
    (.mul (.lit 2) (.var "restrict.count"))) (.mul (.lit 2) (.var "restrict.count"))) (.mul (.lit 3) (.var "conditioning.k"))))
  (.assign "large.denominator" (.mul (.mul (.var "algorithm.load") (.var "graph.n")) (.var "graph.n")))

def finish : Com := .seq
  (.assign "large.value" (.add (.div (.sub (.add (.var "large.numerator") (.var "large.denominator")) (.lit 1))
    (.var "large.denominator")) (.lit 1)))
  (.seq (.assign "split.large.s" (.lit 0))
    (.seq (.assign "split.large.n" (.var "large.value")) (.assign "split.large.d" (.lit 1))))

def command : Com := .seq (.assign "size.value" (.mul (.lit 2) (.var "graph.n")))
  (.seq RamBitSize.word (.seq products finish))



end Lax263307Proofs.NativeLargeCapacity

end

-- Solutions.RAM_Lax263307Proofs_NativeRestrictionRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeRestrictionRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic







def graphRead : Com := .seq (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row")))
  (.seq (.assign "restrict.v" (.get "restrict.vertices" (.var "restrict.col")))
    (.assign "restrict.edge" (.get "search.graph" (.add (.mul (.var "restrict.u") (.var "graph.n")) (.var "restrict.v")))))



def costRead : Com := .seq (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row")))
  (.seq (.assign "read.cursor" (.mul (.lit 3) (.var "restrict.u"))) (NativeRationalRead.command "near.costs"))



end Lax263307Proofs.NativeRestrictionRead

end

-- Solutions.RAM_Lax263307Proofs_NativeFlowPrepare
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFlowPrepare

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding

def command : Com := .seq (.assign "unpack.mask" (.var "separator.remaining"))
  (.seq NativeMaskUnpack.command (.seq NativeSelectedVertices.command NativeLargeCapacity.command))



end Lax263307Proofs.NativeFlowPrepare

end

-- Solutions.RAM_Lax263307Proofs_NativeSplitEntry
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeSplitEntry

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat





def ports : Com := .seq (.assign "split.u" (.div (.var "split.i") (.var "split.order")))
  (.seq (.assign "split.v" (.sub (.var "split.i") (.mul (.var "split.u") (.var "split.order"))))
    (.seq (.assign "restrict.row" (.div (.var "split.u") (.lit 2)))
      (.seq (.assign "restrict.col" (.div (.var "split.v") (.lit 2)))
        (.seq (.assign "split.up" (.sub (.var "split.u") (.mul (.lit 2) (.var "restrict.row"))))
          (.assign "split.vp" (.sub (.var "split.v") (.mul (.lit 2) (.var "restrict.col"))))))))



def choose : Com := .ite (.eq (.var "split.up") (.lit 0))
  (.ite (.eq (.var "split.v") (.add (.var "split.u") (.lit 1))) (load "split.cost") RamFractionPrimitives.zero)
  (.ite (.eq (.add (.var "split.v") (.lit 1)) (.var "split.u")) (load "split.large")
    (.ite (.eq (.var "split.vp") (.lit 0))
      (.ite (.eq (.var "restrict.edge") (.lit 1)) (load "split.large") RamFractionPrimitives.zero)
      RamFractionPrimitives.zero))



def command : Com := .seq ports (.seq NativeRestrictionRead.graphRead
  (.seq NativeRestrictionRead.costRead (.seq (save "split.cost") choose)))





end Lax263307Proofs.NativeSplitEntry

end

-- Solutions.RAM_Lax263307Proofs_NativeSplitVectors
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeSplitVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic NativeSplitEntry
open scoped NNRat



def matrix : Com := RamUnsignedVector.command "split.i" "split.count" "lp.word" "lp.position" NativeSplitEntry.command



def weights : Com := RamUnsignedVector.command "split.weight.i" "split.order" "lp.word" "lp.position" RamFractionPrimitives.one





end Lax263307Proofs.NativeSplitVectors

end

-- Solutions.RAM_Lax263307Proofs_NativeSplitInput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeSplitInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic NativeSplitEntry
open scoped NNRat

def wordLength (s : ℕ) : ℕ := 2+4*s+8*s*s

def sizes : Com := .seq (.assign "split.order" (.mul (.lit 2) (.var "restrict.count")))
  (.assign "split.count" (.mul (.var "split.order") (.var "split.order")))



def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.lit 1))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "split.order")))



def command : Com := .seq sizes (.seq header (.seq NativeSplitVectors.weights NativeSplitVectors.matrix))





end Lax263307Proofs.NativeSplitInput

end

-- Solutions.RAM_Lax263307Proofs_NativeSplitOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSplitOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat



def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeSplitInput.command (NativeOracleCalls.command p coeff)

def cost (r : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (T size : ℕ) : ℕ :=
  488*r*r+56*r+36+
    (((12*size+39)*NativeSplitInput.wordLength r+6*coeff.length+29)+
      ((T+1)*(4*p.length+32*T+104)+18))





end Lax263307Proofs.NativeSplitOracle

end

-- Solutions.RAM_Lax263307Proofs_NativeOutputRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOutputRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def command : Com := .ite (.lt (.var "output.index") (.var "vm.outputLength"))
  (.assign "output.value" (.get "vm.output" (.var "output.index")))
  (.assign "output.value" (.lit 0))



end Lax263307Proofs.NativeOutputRead

end

-- Solutions.RAM_Lax263307Proofs_NativeShoreUpdate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeShoreUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState


def bitCommand (invert : Bool) : Com := .seq NativeOutputRead.command
  (.ite (.eq (.var "output.value") (.lit 1))
    (.assign "shore.bit" (.lit (if invert then 0 else 1)))
    (.assign "shore.bit" (.lit (if invert then 1 else 0))))



def maskCommand (reg : String) : Com := .assign reg
  (.or (.var reg) (.shiftl (.var "shore.bit") (.var "shore.label")))



end Lax263307Proofs.NativeShoreUpdate

end

-- Solutions.RAM_Lax263307Proofs_NativeFlowShores
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeFlowShores

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting
open NativeShoreUpdate










def leftIndex : Com := .assign "output.index" (.mul (.lit 2) (.var "shore.i"))
def rightIndex : Com := .assign "output.index" (.add (.mul (.lit 2) (.var "shore.i")) (.lit 1))
def next : Com := .assign "shore.i" (.add (.var "shore.i") (.lit 1))

def step : Com := .seq (.assign "shore.label" (.get "restrict.vertices" (.var "shore.i")))
  (.seq leftIndex (.seq (bitCommand false) (.seq (maskCommand "shore.left")
    (.seq rightIndex (.seq (bitCommand true) (.seq (maskCommand "shore.right") next))))))



def command : Com := .seq (.assign "shore.left" (.lit 0)) (.seq (.assign "shore.right" (.lit 0))
  (.seq (.assign "shore.i" (.lit 0)) (.while (.lt (.var "shore.i") (.var "restrict.count")) step)))



end Lax263307Proofs.NativeFlowShores

end

-- Solutions.RAM_Lax263307Proofs_NativeShoreOrientation
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeShoreOrientation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs
open Lax263307 ComputedSeparators NativeMasks

def countCommand (reg out : String) : Com := .seq (.assign "unpack.mask" (.var reg))
  (.seq NativeMaskUnpack.command (.assign out (.var "unpack.card")))



def choose : Com := .ite (.lt (.var "shore.leftCard") (.var "shore.rightCard"))
  (.seq (.assign "cut.left" (.var "shore.right")) (.assign "cut.right" (.var "shore.left")))
  (.seq (.assign "cut.left" (.var "shore.left")) (.assign "cut.right" (.var "shore.right")))



def command : Com := .seq (countCommand "shore.left" "shore.leftCard")
  (.seq (countCommand "shore.right" "shore.rightCard") choose)



end Lax263307Proofs.NativeShoreOrientation

end

-- Solutions.RAM_Lax263307Proofs_NativeFlowCut
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFlowCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat






def decodeCommand : Com := .seq NativeFlowShores.command NativeShoreOrientation.command



def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq (NativeSplitOracle.command p coeff) decodeCommand



end Lax263307Proofs.NativeFlowCut

end

-- Solutions.RAM_Lax263307Proofs_NativeSeparatorContext
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSeparatorContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding
open scoped NNRat

def workspace : List String := ["restrict.vertices","subset.bits","lp.word","vm.input","vm.addresses","vm.values","vm.output","separator.cuts"]


structure Context {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (b load k space : ℕ) (σ : Env) : Prop where
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  costs : Prefix (encodeVector fun v => (x v : ℚ)) "near.costs" σ
  order : σ.vars "graph.n"=n
  classB : σ.vars "class.B"=b
  load : σ.vars "algorithm.load"=load
  target : σ.vars "conditioning.k"=k
  room : ∀ a∈workspace,space≤(σ.arrs a).length



def callback (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeFlowPrepare.command (NativeFlowCut.command p coeff)









end Lax263307Proofs.NativeSeparatorContext

end

-- Solutions.RAM_Lax263307Proofs_NativeFlowQueryResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat





def sizeBound (n h : ℕ) : ℕ := NativeSplitInput.wordLength n*(h+n+4)





end Lax263307Proofs.NativeFlowQueryResources

end

-- Solutions.RAM_Lax263307Proofs_NativeLargeResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeLargeResources

open Lax263307 ComputedSeparators NativeSignedArithmetic NativeLargeCapacity







def heightExponent (b n load k h : ℕ) : ℕ :=
  h+numerator b n n k+resource b n n load k+n+30







end Lax263307Proofs.NativeLargeResources

end

-- Solutions.RAM_Lax263307Proofs_NativeUniformFlow
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeUniformFlow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeFlowQueryResources
open scoped NNRat

def shape (n : ℕ) : ℕ := 8*n*n+6*n+40

def wordHeight (n H : ℕ) (p : Lax808846.Ram.Program) (wp tp op : Polynomial ℕ) : ℕ :=
  let S := sizeBound n H
  2*wp.eval (S+1)+H+shape n+S+tp.eval S+op.eval S+RamVirtualConstants.allowance p+20

def spaceBound (n H : ℕ) (tp : Polynomial ℕ) : ℕ :=
  NativeSplitInput.wordLength n+tp.eval (sizeBound n H)+n+2

def callbackTime (n H : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (tp : Polynomial ℕ) : ℕ :=
  43*n+12*(2*n).size+78+NativeSplitOracle.cost n p coeff (tp.eval (sizeBound n H)) (sizeBound n H)+59*n+42*n+42





end Lax263307Proofs.NativeUniformFlow

end

-- Solutions.RAM_Lax263307Proofs_NativeCutRecords
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutRecords

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def words {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : List ℕ :=
  cs.flatMap fun s => [mask s.1,mask s.2]







def update : Com := .seq (.assign "separator.remaining"
  (.xor (.var "cut.left") (.and (.var "cut.left") (.var "cut.right"))))
  (.seq (.assign "separator.value" (.or (.var "separator.value") (.and (.var "cut.left") (.var "cut.right"))))
    (.assign "separator.count" (.add (.var "separator.count") (.lit 1))))



def command : Com := .seq (RamWordBuffer.append "separator.cuts" "separator.position" (.var "cut.left"))
  (.seq (RamWordBuffer.append "separator.cuts" "separator.position" (.var "cut.right")) update)



end Lax263307Proofs.NativeCutRecords

end

-- Solutions.RAM_Lax263307Proofs_NativeCutTest
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeMasks

def finish : Com := .ite (.lt (.mul (.lit 2) (.var "graph.n")) (.mul (.lit 3) (.var "unpack.card")))
  (.assign "separator.active" (.lit 1)) (.assign "separator.active" (.lit 0))



def command : Com := .seq (.assign "unpack.mask" (.var "separator.remaining"))
  (.seq NativeMaskUnpack.command finish)



end Lax263307Proofs.NativeCutTest

end

-- Solutions.RAM_Lax263307Proofs_NativeCutLoop
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeCutLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks









def branch (body : Com) : Com := .ite (.eq (.var "separator.active") (.lit 1))
  (.seq body NativeCutRecords.command) .skip

def step (body : Com) : Com := .seq NativeCutTest.command
  (.seq (branch body) (.assign "separator.i" (.add (.var "separator.i") (.lit 1))))



def command (body : Com) : Com := .seq (.assign "separator.count" (.lit 0))
  (.seq (.assign "separator.position" (.lit 0)) (.seq (.assign "separator.value" (.lit 0))
    (.seq (.assign "separator.i" (.lit 0)) (.while (.lt (.var "separator.i") (.var "graph.n")) (step body)))))



end Lax263307Proofs.NativeCutLoop

end

-- Solutions.RAM_Lax263307Proofs_NativeSeparatorProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSeparatorProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs
open Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeUniformFlow
open scoped NNRat

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com := NativeCutLoop.command (callback p coeff)

def timeBound (n H : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (tp : Polynomial ℕ) : ℕ :=
  (21*n+callbackTime n H p coeff tp+62)*n+12



end Lax263307Proofs.NativeSeparatorProgram

end

-- Solutions.RAM_Lax263307Proofs_NativeCutPairRead
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutPairRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks



def command : Com := .seq (.assign "piece.left" (.get "separator.cuts" (.mul (.lit 2) (.var "piece.i"))))
  (.seq (.assign "piece.right" (.get "separator.cuts" (.add (.mul (.lit 2) (.var "piece.i")) (.lit 1))))
    (.assign "fill.value" (.xor (.var "piece.right") (.and (.var "piece.right") (.var "piece.left")))))



end Lax263307Proofs.NativeCutPairRead

end

-- Solutions.RAM_Lax263307Proofs_NativeCutPieces
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def words {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : List ℕ :=
  mask (remaining Finset.univ cs)::cs.map (fun s => mask (s.2\s.1))





def read : Com := .ite (.eq (.var "fill.i") (.lit 0))
  (.assign "fill.value" (.var "separator.remaining"))
  (.seq (.assign "piece.i" (.sub (.var "fill.i") (.lit 1))) NativeCutPairRead.command)



def command : Com := .seq (.assign "fill.length" (.add (.var "separator.count") (.lit 1)))
  (NativeTabulate.command "separator.pieces" read)




end Lax263307Proofs.NativeCutPieces

end

-- Solutions.RAM_Lax263307Proofs_NativeSeparatorOutput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSeparatorOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeUniformFlow
open scoped NNRat

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeFullSetMask.command (.seq (NativeSeparatorProgram.command p coeff) NativeCutPieces.command)

def timeBound (n H : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (tp : Polynomial ℕ) : ℕ :=
  14*n+8+NativeSeparatorProgram.timeBound n H p coeff tp+37*(n+1)+10





end Lax263307Proofs.NativeSeparatorOutput

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentCosts
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeComponentCosts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead

def read : Com := .seq (.assign "restrict.row" (.var "component.vertex")) costRead



def command : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "component.vertex" "restrict.count" read)



end Lax263307Proofs.NativeComponentCosts

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentSum
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeComponentSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead

def setup : Com := .seq (.assign "sum.count" (.var "restrict.count"))
  (.seq (.assign "fill.length" (.var "lp.position")) (.assign "slice.start" (.lit 0)))

def command : Com := .seq NativeComponentCosts.command (.seq setup
  (.seq (NativeSlice.command "lp.word" "sum.input") NativeSignedSum.command))







end Lax263307Proofs.NativeComponentSum

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentTarget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeComponentTarget

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational















def products : Com := .seq (.assign "component.numerator" (.mul (.sub (.var "algorithm.D") (.lit 1)) (.var "rat.n")))
  (.seq (.assign "component.denominator" (.mul (.var "algorithm.D") (.var "rat.d")))
    (.seq (.assign "component.left" (.mul (.mul (.mul (.lit 4) (.var "graph.n")) (.var "algorithm.D")) (.var "rat.n")))
      (.assign "component.right" (.mul (.var "conditioning.k") (.var "rat.d")))))

def finish : Com := .seq (.assign "component.target" (.add (.div (.var "component.numerator") (.var "component.denominator")) (.lit 1)))
  (.ite (.lt (.var "component.right") (.var "component.left"))
    (.assign "component.active" (.lit 1)) (.assign "component.active" (.lit 0)))

def command : Com := .seq products finish



end Lax263307Proofs.NativeComponentTarget

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeComponentResources

open Lax263307Proofs.NativeSignedArithmetic

def span (n D k : ℕ) : ℕ := n+D+k+20





end Lax263307Proofs.NativeComponentResources

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentDecision
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeComponentDecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead
open scoped NNRat

def height (n h : ℕ) : ℕ := 2^((h+1)*(n+1))
def wordHeight (n D k h : ℕ) : ℕ := 2*((h+1)*(n+1))+4*NativeComponentResources.span n D k+20
def timeBound (n h : ℕ) : ℕ := (36*((height n h)^2).size+258)*n+72

def command : Com := .seq NativeComponentSum.command NativeComponentTarget.command



end Lax263307Proofs.NativeComponentDecision

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentLoad
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeComponentLoad

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeMasks NativeSignedArithmetic
open scoped NNRat

def prepare : Com := .seq (.assign "component.mask" (.get "separator.pieces" (.var "component.i")))
  (.seq (.assign "unpack.mask" (.var "component.mask"))
    (.seq NativeMaskUnpack.command NativeSelectedVertices.command))



def command : Com := .seq prepare NativeComponentDecision.command



end Lax263307Proofs.NativeComponentLoad

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentCoefficient
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeComponentCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks









def selected : Cond := .eq
  (.and (.shiftr (.var "component.mask") (.var "cut.vertex")) (.lit 1)) (.lit 1)

def sameColumn : Cond := .eq
  (.or (.var "conditioning.choice") (.shiftl (.lit 1) (.var "cut.vertex"))) (.var "cut.column")

def increment : Com := .assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))

def collect : Com := .ite selected (.ite sameColumn increment .skip) .skip

def step : Com := .seq collect (.assign "cut.vertex" (.add (.var "cut.vertex") (.lit 1)))







def positive : Com := .seq (.assign "coefficient.positive" (.lit 0))
  (.seq (.assign "cut.vertex" (.lit 0)) (.while (.lt (.var "cut.vertex") (.var "graph.n")) step))



def negative : Com := .ite (.eq (.var "conditioning.choice") (.var "cut.column"))
  (.assign "coefficient.negative" (.var "component.target")) (.assign "coefficient.negative" (.lit 0))

def command : Com := .seq positive negative



end Lax263307Proofs.NativeComponentCoefficient

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentNormal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeComponentNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks NativeCatalogMetadata

def normal {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) : MomentLP.Index n r → ℤ :=
  MomentLP.encode (ComponentCutEncoding.coefficient A C u)









def read : Com := .seq (.assign "cut.column" (.get "catalog.mask" (.var "fill.i")))
  NativeComponentCoefficient.command



def table : Com := .seq (.assign "fill.length" (.var "catalog.count"))
  (.seq (.assign "lp.length" (.lit 0)) (NativeRationalTabulate.command read))



def command : Com := .seq table (NativeProgramCache.copy "lp.input" "round.normal" "lp.length")



end Lax263307Proofs.NativeComponentNormal

end

-- Solutions.RAM_Lax263307Proofs_NativeScaledInteger
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeScaledInteger

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational NativeSignedArithmetic











def command : Com := .seq
  (.assign "rat.n" (.mul (.var "rat.n") (.div (.var "cut.denominator") (.var "rat.d"))))
  (.assign "rat.d" (.lit 1))



end Lax263307Proofs.NativeScaledInteger

end

-- Solutions.RAM_Lax263307Proofs_NativeCutCoefficient
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutRead

def command : Com := .seq NativeCutRead.command NativeScaledInteger.command







end Lax263307Proofs.NativeCutCoefficient

end

-- Solutions.RAM_Lax263307Proofs_NativeCutVector
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutCoefficient

def command : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "cut.i" "projection.n" NativeCutCoefficient.command)



end Lax263307Proofs.NativeCutVector

end

-- Solutions.RAM_Lax263307Proofs_NativeDenominatorProduct
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeDenominatorProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeCutRead

def update : Com := .seq (.assign "cut.denominator" (.mul (.var "cut.denominator") (.var "rat.d")))
  (.assign "cut.i" (.add (.var "cut.i") (.lit 1)))

def step : Com := .seq NativeCutRead.command update

def command : Com := .seq (.assign "cut.denominator" (.lit 1))
  (.seq (.assign "cut.i" (.lit 0)) (.while (.lt (.var "cut.i") (.var "projection.n")) step))







end Lax263307Proofs.NativeDenominatorProduct

end

-- Solutions.RAM_Lax263307Proofs_NativeClearNormal
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeClearNormal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307.RationalCutBuffer NativeSignedArithmetic

def setup : Com := .seq (.assign "slice.start" (.lit 0))
  (.assign "fill.length" (.mul (.lit 3) (.var "projection.n")))

def command : Com := .seq setup (.seq (NativeSlice.command "lp.word" "cut.source")
  (.seq NativeDenominatorProduct.command NativeCutVector.command))



end Lax263307Proofs.NativeClearNormal

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleCut
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOracleCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

def far (next : ℕ) : Com := .seq NativeClearNormal.command
  (.seq (NativeProgramCache.copy "lp.word" "round.normal" "lp.position") (.assign "machine.phase" (.lit next)))



def failedChild (next : ℕ) : Com := .seq
  (.assign "component.target" (.sub (.var "component.target") (.lit 1)))
  (.seq NativeComponentNormal.command (.assign "machine.phase" (.lit next)))



end Lax263307Proofs.NativeOracleCut

end

-- Solutions.RAM_Lax263307Proofs_NativeChildLift
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeChildLift

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks











def insertCommand : Com := .assign "lift.mask"
  (.or (.var "lift.mask") (.shiftl (.lit 1) (.var "lift.vertex")))

def choose : Com := .ite (.eq (.var "lift.bit") (.lit 1)) insertCommand .skip

def step : Com := .seq (.assign "lift.bit" (.get "subset.bits" (.var "lift.i")))
  (.seq (.assign "lift.vertex" (.get "restrict.vertices" (.var "lift.i")))
    (.seq choose (.assign "lift.i" (.add (.var "lift.i") (.lit 1)))))



def command : Com := .seq (.assign "lift.mask" (.lit 0))
  (.seq (.assign "lift.i" (.lit 0)) (.while (.lt (.var "lift.i") (.var "graph.n")) step))



end Lax263307Proofs.NativeChildLift

end

-- Solutions.RAM_Lax263307Proofs_NativeChildReturn
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def setup : Com := .seq (.assign "lift.parent.n" (.var "graph.n"))
  (.seq (.assign "graph.n" (.var "restrict.count"))
    (.assign "unpack.mask" (.var "recursion.return.mask")))

def liftCommand : Com := .seq setup (.seq NativeMaskUnpack.command
  (.seq NativeChildLift.command (.assign "graph.n" (.var "lift.parent.n"))))








end Lax263307Proofs.NativeChildReturn

end

-- Solutions.RAM_Lax263307Proofs_NativeComponentControl
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeComponentControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks ComputedSeparators

def start (next : ℕ) : Com := .seq (.assign "component.count" (.add (.var "separator.count") (.lit 1)))
  (.seq (.assign "component.i" (.lit 0)) (.seq (.assign "component.union" (.lit 0))
    (.assign "machine.phase" (.lit next))))



def advance (next : ℕ) : Com := .seq (.assign "component.i" (.add (.var "component.i") (.lit 1)))
  (.assign "machine.phase" (.lit next))



def append (next : ℕ) : Com := .seq
  (.assign "component.union" (.or (.var "component.union") (.var "lift.mask"))) (advance next)



def childReply (more update : ℕ) : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1))
  (.seq NativeChildReturn.liftCommand (append more)) (NativeOracleCut.failedChild update)





def finish (ret : ℕ) : Com := .seq (.assign "recursion.return.tag" (.lit 1))
  (.seq (.assign "recursion.return.mask" (.var "component.union")) (.assign "machine.phase" (.lit ret)))



end Lax263307Proofs.NativeComponentControl

end

-- Solutions.RAM_Lax263307Proofs_NativeChildGraph
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeChildGraph

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeRestrictionRead

def read : Com := .seq (.assign "restrict.row" (.div (.var "fill.i") (.var "restrict.count")))
  (.seq (.assign "restrict.col" (.sub (.var "fill.i") (.mul (.var "restrict.row") (.var "restrict.count"))))
    (.seq graphRead (.assign "fill.value" (.var "restrict.edge"))))





def command : Com := .seq (.assign "fill.length" (.mul (.var "restrict.count") (.var "restrict.count")))
  (NativeTabulate.command "child.graph" read)



end Lax263307Proofs.NativeChildGraph

end

-- Solutions.RAM_Lax263307Proofs_NativeBlockAppend
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def step (source target : String) : Com := .seq
  (RamWordBuffer.append target "stack.words" (.get source (.var "stack.i")))
  (.assign "stack.i" (.add (.var "stack.i") (.lit 1)))

def command (source target : String) : Com := .seq (.assign "stack.i" (.lit 0))
  (.while (.lt (.var "stack.i") (.var "stack.copy.length")) (step source target))







end Lax263307Proofs.NativeBlockAppend

end

-- Solutions.RAM_Lax263307Proofs_NativeStateBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeStateBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def Bounded (B : ℕ) (σ : Env) : Prop :=
  (∀ s,σ.vars s< B) ∧ (∀ a z,z∈σ.arrs a → z< B) ∧ σ.InpBounded B











end Lax263307Proofs.NativeStateBounds

end

-- Solutions.RAM_Lax263307Proofs_NativeFrameBuffers
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState







def save : List String → Com
  | [] => .skip
  | a::as => .seq (.seq (.assign "stack.copy.length" (.var "recursion.stride"))
      (NativeBlockAppend.command a "recursion.frames")) (save as)






end Lax263307Proofs.NativeFrameBuffers

end

-- Solutions.RAM_Lax263307Proofs_NativeBlockRestore
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeBlockRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def setup : Com := .seq (.assign "fill.length" (.var "stack.copy.length"))
  (.assign "slice.start" (.var "stack.read.i"))

def command (target : String) : Com := .seq setup
  (.seq (NativeSlice.command "recursion.frames" target)
    (.assign "stack.read.i" (.add (.var "stack.read.i") (.var "stack.copy.length"))))





end Lax263307Proofs.NativeBlockRestore

end

-- Solutions.RAM_Lax263307Proofs_NativeFrameBufferRestore
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrameBufferRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def command : List String → Com
  | [] => .skip
  | a::as => .seq (.seq (.assign "stack.copy.length" (.var "recursion.stride"))
      (NativeBlockRestore.command a)) (command as)









end Lax263307Proofs.NativeFrameBufferRestore

end

-- Solutions.RAM_Lax263307Proofs_NativeFrameScalars
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState



def save : List String → Com
  | [] => .skip
  | s::ss => .seq (RamWordBuffer.append "recursion.frames" "stack.words" (.var s)) (save ss)





end Lax263307Proofs.NativeFrameScalars

end

-- Solutions.RAM_Lax263307Proofs_NativeFrameRestore
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrameRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def step (s : String) : Com := .seq (.assign s (.get "recursion.frames" (.var "stack.read.i")))
  (.assign "stack.read.i" (.add (.var "stack.read.i") (.lit 1)))

def command : List String → Com
  | [] => .skip
  | s::ss => .seq (step s) (command ss)





end Lax263307Proofs.NativeFrameRestore

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursionFrame
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState



def save (arrays scalars : List String) : Com := .seq (NativeFrameBuffers.save arrays) (NativeFrameScalars.save scalars)
def restore (arrays scalars : List String) : Com := .seq (NativeFrameBufferRestore.command arrays) (NativeFrameRestore.command scalars)











end Lax263307Proofs.NativeRecursionFrame

end

-- Solutions.RAM_Lax263307Proofs_NativeChildActivate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeChildActivate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def setup : Com := .seq (.assign "fill.length" (.mul (.var "restrict.count") (.var "restrict.count")))
  (.assign "slice.start" (.lit 0))

def command : Com := .seq setup (.seq (NativeSlice.command "child.graph" "search.graph")
  (.assign "graph.n" (.var "restrict.count")))





end Lax263307Proofs.NativeChildActivate

end

-- Solutions.RAM_Lax263307Proofs_NativeChildCall
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeChildCall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState





def enter (entry : ℕ) : Com := .seq (.assign "node.k" (.var "component.target"))
  (.seq (.assign "recursion.fuel" (.sub (.var "recursion.fuel") (.lit 1)))
    (.assign "machine.phase" (.lit entry)))



def command (arrays scalars : List String) (entry continuation : ℕ) : Com :=
  .seq (.assign "machine.phase" (.lit continuation))
    (.seq (NativeRecursionFrame.save arrays scalars) (.seq NativeChildActivate.command (enter entry)))



end Lax263307Proofs.NativeChildCall

end

-- Solutions.RAM_Lax263307Proofs_NativeStackReturn
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeStackReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState







def setup : Com := .seq (.assign "stack.words" (.sub (.var "stack.words") (.var "frame.length")))
  (.assign "stack.read.i" (.var "stack.words"))

def pop (arrays scalars : List String) : Com := .seq setup (NativeRecursionFrame.restore arrays scalars)



def command (arrays scalars : List String) (root : ℕ) : Com :=
  .ite (.eq (.var "stack.words") (.lit 0)) (.assign "machine.phase" (.lit root)) (pop arrays scalars)





end Lax263307Proofs.NativeStackReturn

end

-- Solutions.RAM_Lax263307Proofs_NativeRawOracle
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRawOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def setup : Com := .seq (.assign "fill.length" (.var "lp.position")) (.assign "slice.start" (.lit 0))

def prepare : Com := .seq setup (.seq (NativeSlice.command "lp.word" "vm.input")
  (.assign "vm.inputLength" (.var "lp.position")))





def command (p : Lax808846.Ram.Program) : Com := .seq prepare (RamVirtualProgram.execute p)

def cost (p : Lax808846.Ram.Program) (length T : ℕ) : ℕ :=
  16*length+12+(T+1)*(4*p.length+32*T+104)+18



end Lax263307Proofs.NativeRawOracle

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedUpdate
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

namespace Lax263307Proofs.NativeRoundedUpdate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch
open Matrix

def command (p : Lax808846.Ram.Program) : Com := .seq NativeRoundedQuery.command
  (.seq (NativeRawOracle.command p) NativeRoundedState.command)

def timeBound (p : Lax808846.Ram.Program) (c n h k : ℕ) : ℕ :=
  NativeRawOracle.cost p (2+3*(n*n)+6*n) (c*(n+h+k+1)^12)+96*(n*n)+144*n+78





end Lax263307Proofs.NativeRoundedUpdate

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedControl
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRoundedControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch Matrix

def finish (projection ret : ℕ) : Com := .seq
  (.assign "round.i" (.add (.var "round.i") (.lit 1)))
  (.ite (.lt (.var "round.i") (.var "round.limit")) (.assign "machine.phase" (.lit projection))
    (NativeAttemptReply.noneCommand ret))

def Output (m k limit projection ret : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=m ∧ σ.vars "round.i"=k+1 ∧
    if k+1< limit then σ.vars "machine.phase"=projection
    else NativeTargetDriver.Reply (none : Option (Finset (Fin m))) σ ∧ σ.vars "machine.phase"=ret



def command (p : Lax808846.Ram.Program) (projection ret : ℕ) : Com :=
  .seq (.assign "vm.width" (.var "algorithm.roundWidth"))
    (.seq (NativeRoundedUpdate.command p) (finish projection ret))





end Lax263307Proofs.NativeRoundedControl

end

-- Solutions.RAM_Lax263307Proofs_NativeMachineTrace
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeMachineTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def dispatch : List Com → ℕ → Com
  | [],_ => .assign "machine.running" (.lit 0)
  | c::cs,i => .ite (.eq (.var "machine.phase") (.lit i)) c (dispatch cs (i+1))

def driver (cases : List Com) : Com := .while (.eq (.var "machine.running") (.lit 1)) (dispatch cases 0)









end Lax263307Proofs.NativeMachineTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeCoreMachine
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCoreMachine

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Every field is fixed for the graph class, before the input graph,
weights, accuracy, or RAM word width is supplied. -/
structure Config where
  a : ℕ
  K : ℕ
  b : ℕ
  lp : Lax808846.Ram.Program
  flow : Lax808846.Ram.Program
  rounded : Lax808846.Ram.Program
  lpWidth : List ℕ
  flowWidth : List ℕ

def go (phase : ℕ) : Com := .assign "machine.phase" (.lit phase)

def emptyRoot : Com := .seq (.assign "root.mask" (.lit 0))
  (.seq (.assign "root.value" (.lit 0)) (.assign "machine.running" (.lit 0)))

def rootTarget : Com := .ite (.eq (.var "root.target") (.lit 0)) emptyRoot
  (.seq (.assign "node.k" (.var "root.target"))
    (.seq (.assign "recursion.fuel" (.var "root.fuel")) (go 1)))

def rootReply : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1))
  (.seq (.assign "root.mask" (.var "recursion.return.mask"))
    (.seq (.assign "root.value" (.var "root.target")) (.assign "machine.running" (.lit 0))))
  (.seq (.assign "root.target" (.sub (.var "root.target") (.lit 1))) (go 0))

def projectionReply : Com := .ite (.eq (.var "projection.kind") (.lit 0)) (go 6)
  (.ite (.eq (.var "projection.kind") (.lit 1)) (NativeOracleCut.far 13) (NativeAttemptReply.noneCommand 14))

def conditioningReply : Com := .ite (.eq (.var "conditioning.found") (.lit 1))
  (.seq (.assign "conditioning.mask" (.var "conditioning.choice"))
    (.seq NativeNearCosts.command (go 8))) (NativeAttemptReply.noneCommand 14)

def component : Com := .ite (.lt (.var "component.i") (.var "component.count"))
  (.seq NativeComponentLoad.command (go 10))
  (NativeComponentControl.finish 14)

/-- The full finite phase list. Child recursion re-enters phase 1 through
the explicit stack; no recursively expanded command syntax is used. -/
def cases (cfg : Config) (arrays scalars : List String) : List Com :=
  [rootTarget,
   NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14,
   NativeSmallAttempt.command 14,
   .seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4),
   .seq NativeProjectionPrepare.command (.seq (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (go 5)),
   projectionReply,
   .seq NativeMomentStorage.command (.seq NativeHeavySearch.command (go 7)),
   conditioningReply,
   .seq (NativeSeparatorOutput.command cfg.flow cfg.flowWidth) (NativeComponentControl.start 9),
   component,
   .ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9),
   .seq NativeChildGraph.command (NativeChildCall.command arrays scalars 1 12),
   NativeComponentControl.childReply 9 13,
   NativeRoundedControl.command cfg.rounded 4 14,
   NativeStackReturn.command arrays scalars 15,
   rootReply]

def frameArrays (cfg : Config) : List String :=
  (((cases cfg [] []).flatMap Com.warrs).dedup).filter (fun a => a != "recursion.frames")

def excludedScalars : List String :=
  ["stack.words","stack.read.i","stack.i","stack.copy.length","recursion.return.tag","recursion.return.mask"]

def frameScalars (cfg : Config) : List String :=
  (((cases cfg [] []).flatMap Com.wvars).dedup).filter (fun s => decide (s∉excludedScalars))

def phases (cfg : Config) : List Com := cases cfg (frameArrays cfg) (frameScalars cfg)

def frameSize (cfg : Config) : Com := .assign "frame.length"
  (.add (.mul (.var "recursion.stride") (.lit (frameArrays cfg).length)) (.lit (frameScalars cfg).length))

def initializeRoot : Com := .seq (.assign "root.target" (.var "graph.n"))
  (.seq (.assign "root.fuel" (.var "recursion.fuel"))
    (.seq (.assign "stack.words" (.lit 0)) (.seq (.assign "machine.running" (.lit 1)) (go 0))))

/-- The unweighted controller, starting after root accuracy and workspace
budgets have been computed. Its complete execution/resource theorem remains
to be established; these definitions do not assert correctness by themselves. -/
def command (cfg : Config) : Com := .seq (frameSize cfg)
  (.seq initializeRoot (NativeMachineTrace.driver (phases cfg)))



















end Lax263307Proofs.NativeCoreMachine

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedRounding NativeCoreMachine NativeMasks





def partCost (cfg : Config) (n r S h childTime : ℕ) : ℕ :=
  43*n+37+NativeComponentDecision.timeBound n h+
    ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(n*n)+36)+
    childTime+((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)+
    ((45*n+38)+((28*n+104)*NativeCatalogMetadata.N n r+30))







end Lax263307Proofs.NativeCollectionExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionTrace
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeSignedArithmetic



/-- This is exactly the input contract supplied by the checked, fixed LP
invocation theorem. The buffer bounds are unchanged by preparation. -/
def InvocationInput {m N : ℕ} (P : Program ℚ m N) (x : Fin N → ℚ) (ρ : ℚ)
    (oracleTime : ℕ) (σ : Env) : Prop :=
  Prefix (encodeProgram P) "lp.input" σ ∧ Prefix (encodeVector x) "projection.center" σ ∧
  Prefix (encodeRational ρ) "projection.tolerance" σ ∧
  NativeDistanceData.wordLength m N<(σ.arrs "lp.word").length ∧
  (encodeProgram (DistanceProjection.distanceProgram P x)).length<(σ.arrs "vm.input").length ∧
  oracleTime<(σ.arrs "vm.addresses").length ∧ oracleTime<(σ.arrs "vm.values").length ∧
  oracleTime<(σ.arrs "vm.output").length











end Lax263307Proofs.NativeProjectionTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleContext
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine











/-- The node-independent workspace and stack protocol. It is inherited by
an activated child and recovered when that child returns. -/
structure Protocol (B D S v : ℕ) (cfg : Config) (extent : String → ℕ)
    (front : List ℕ) (σ : Env) : Prop where
  bounded : NativeStateBounds.Bounded B σ
  lengths : ∀ a,(σ.arrs a).length=extent a
  stack : Prefix front "recursion.frames" σ
  cursor : σ.vars "stack.words"=front.length
  stride : σ.vars "recursion.stride"=S
  frameLength : σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length
  roundWidth : σ.vars "algorithm.roundWidth"=v
  accuracy : σ.vars "node.D"=D

















end Lax263307Proofs.NativeOracleContext

end

-- Solutions.RAM_Lax263307Proofs_NativeNearExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNearExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeOracleContext

/-- Numerical and allocation obligations for the complete near branch.
These are inequalities, not hypotheses that phases execute. -/
structure Bounds (n r D k p M h T fuel S w : ℕ) (cfg : Config)
    (extent : String → ℕ) (front : List ℕ) : Prop where
  positive : 0< n
  denominator : 0< D
  sparsity : 0< p
  height : 1≤ M
  reply : n+19<2^w
  moment : 3*NativeCatalogMetadata.N n r+10<2^w
  search : 3*(n*n)+3*n+r+10<2^w
  masks : 2^n<2^w
  rational : 2*M^2+3<2^w
  quadratic : 2*(NativeQuadraticSum.height M n)^2+3<2^w
  test : NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
    M (NativeQuadraticSum.height M n)<2^w
  floor : NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<2^w
  costHeight : M^2≤2^h
  component : NativeComponentDecision.wordHeight n D k h≤ w
  collection : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
    2*(n+1)+T+fuel+3*NativeCatalogMetadata.N n r+80<2^w
  frameExtents : ∀ a∈frameArrays cfg,extent a=S
  stack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤ extent "recursion.frames"
  child : n*n≤ extent "child.graph"
  graph : n*n≤ extent "search.graph"
  bits : n≤ extent "subset.bits"
  labels : n≤ extent "restrict.vertices"
  word : 3*n+3*(n*n)< extent "lp.word"
  copy : 3*n≤ extent "cut.source"
  sum : 3*(n*n)≤ extent "sum.input"
  moments : 3*NativeCatalogMetadata.N n r≤ extent "near.moments"
  costs : 3*n≤ extent "near.costs"
  input : 3*NativeCatalogMetadata.N n r≤ extent "lp.input"
  normal : 3*NativeCatalogMetadata.N n r≤ extent "round.normal"
  pieces : n+1≤ extent "separator.pieces"

def run {n r : ℕ} (flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D k p b load : ℕ) (y : RationalVector n r)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) : NearOracle.Result n :=
  match findHeavyConditioning G k p y with
  | none => .reject
  | some A =>
    let x := NearOracle.costs y A
    let cs := cuts (step flow G x b load k) n Finset.univ
    match ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D : ℚ)) k
      (fun i => ∑ v∈pieces cs i,(x v : ℚ))
      (fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))) with
    | .found I => .found I
    | .cut C u => .cut A C u



def timeBound (cfg : Config) (n r M S h childTime flowTime : ℕ) : ℕ :=
  (48*NativeCatalogMetadata.N n r+NativeHeavySearch.cost M n r+14)+10+
  ((17*NativeCatalogMetadata.N n r+72*(M^2).size+270)*n+17*NativeCatalogMetadata.N n r+67)+
  (flowTime+10)+NativeCollectionExecution.partCost cfg n r S h childTime*(n+1)+10













end Lax263307Proofs.NativeNearExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeOracleContext

def projection {n r : ℕ} (lp : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k D F : ℕ) (center : MomentLP.Index n r → ℚ) : RationalProjection.Outcome (MomentLP.dimension n r) :=
  RationalProjection.classify (MomentLP.program G k r) (NativeNodeTolerance.tolerance n D F)
    (RegisteredLP.certificate lp (DistanceProjection.distanceProgram (MomentLP.program G k r) (ProjectedOracle.raw center)))

def reply {n r : ℕ} (flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D k p b load : ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) :
    RationalProjection.Outcome (MomentLP.dimension n r) → RoundedOracleSearch.Reply (MomentLP.dimension n r) (Finset (Fin n))
  | .reject => .reject
  | .far a _ => .cut (RationalCutBuffer.integerNormal a)
  | .near x => match NativeNearExecution.run flow G D k p b load (MomentLP.decode x) child with
    | .reject => .reject
    | .found I => .found I
    | .cut A C u => .cut (RationalCutBuffer.integerNormal
        (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))



structure ProjectionBounds {n : ℕ} (D k r F M w oracleTime : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent : String → ℕ) : Prop where
  positive : 0< n
  denominator : 0< D
  floorPower : 0< F
  program : (encodeProgram (MomentLP.program G k r)).length+2<2^w
  rational : 2*M^2+3<2^w
  shape : 4*MomentLP.dimension n r+5<2^w
  scale : 4*MomentLP.dimension n r≤ M
  tolerance : NativeNodeTolerance.guard n D F<2^w
  reply : n+19<2^w
  input : (encodeProgram (MomentLP.program G k r)).length≤ extent "lp.input"
  word : 3*MomentLP.dimension n r< extent "lp.word"
  center : 3*MomentLP.dimension n r≤ extent "projection.center"
  word3 : 3≤ extent "lp.word"
  tolerance3 : 3≤ extent "projection.tolerance"
  distance : NativeDistanceData.wordLength (NativeMomentAssembly.rowCount n r) (MomentLP.dimension n r)< extent "lp.word"
  addresses : oracleTime< extent "vm.addresses"
  values : oracleTime< extent "vm.values"
  output : oracleTime< extent "vm.output"
  source : 3*MomentLP.dimension n r≤ extent "cut.source"
  normal : 3*MomentLP.dimension n r≤ extent "round.normal"













end Lax263307Proofs.NativeOracleExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeDistanceQueryResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeDistanceQueryResources

open Lax455465Proofs Lax759944.BinaryWordEncoding
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData









def sizeBound (m n h : ℕ) : ℕ := wordLength m n*(h+m+2*n+4)



end Lax263307Proofs.NativeDistanceQueryResources

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionQueryBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeProjectionQueryBounds

open Lax263307 MomentLP
open NativeSignedArithmetic Lax109476.RationalEncoding



def scaleHeight (N R : ℕ) : ℕ := 80*(R+1)+4*N+1


def rootHeight (R : ℕ) : ℕ := 100*(4*R+2)^3+10+2*scaleHeight R R+1
def rootRows (R : ℕ) : ℕ := 6*(R+1)^2
def queryBound (R : ℕ) : ℕ := NativeDistanceQueryResources.sizeBound (rootRows R) R (rootHeight R)







end Lax263307Proofs.NativeProjectionQueryBounds

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeProjectionResources

open Lax263307 Lax109476.RationalEncoding



def shape (R : ℕ) : ℕ :=
  NativeDistanceData.shapeSize (NativeProjectionQueryBounds.rootRows R) R+1000*(R+1)^5+20

def space (R T : ℕ) : ℕ := shape R+T+10

def wordHeight (R : ℕ) : ℕ := 200*(R+1)+shape R







end Lax263307Proofs.NativeProjectionResources

end

-- Solutions.RAM_Lax263307Proofs_NativeCutResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCutResources

open Lax263307.RationalCutBuffer NativeSignedArithmetic

def wordExponent (n h : ℕ) : ℕ := (n+1)*(h+1)+10







end Lax263307Proofs.NativeCutResources

end

-- Solutions.RAM_Lax263307Proofs_NativeOraclePrecision
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOraclePrecision

open Lax263307 Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime




def certificateHeight (wp : Polynomial ℕ) (R : ℕ) : ℕ :=
  wp.eval (NativeProjectionQueryBounds.queryBound R)

def roundedHeight (wp : Polynomial ℕ) (R : ℕ) : ℕ :=
  80*(R+1)+(R+1)*(2*certificateHeight wp R+1)+2*R+1






end Lax263307Proofs.NativeOraclePrecision

end

-- Solutions.RAM_Lax263307Proofs_NativeSelectedLP
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedLP

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 DistanceProjection NativeDistanceData

/-- Retain the width guarantee for the same LP program that is invoked
by the native command. No separately chosen output-width polynomial is used. -/
structure Program (f : List ℕ → List ℕ) where
  code : Lax808846.Ram.Program
  width : Polynomial ℕ
  time : Polynomial ℕ
  coeff : List ℕ
  coefficients : ∀ z : ℕ,RamPolynomial.value coeff z=width.eval z
  fits : ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (x : Fin n → ℚ),
    FitsInWords (width.eval (bitSize (encodeProgram (distanceProgram P x))))
      (f (encodeProgram (distanceProgram P x)))
  call : ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (x : Fin n → ℚ) (ρ : ℚ) (M B : ℕ),
    let query := encodeProgram (distanceProgram P x)
    shapeSize m n< B → Bounded B P x → 2^(width.eval (bitSize query))≤ M →
    NativeSignedArithmetic.Bounded M ρ → 2*M^2+3< B → bitSize query+1< B →
    width.eval (bitSize query+1)< B → time.eval (bitSize query)+1< B →
    RamVirtualConstants.allowance code< B →
    Spec B (fun σ => NativeProjectionTrace.InvocationInput P x ρ (time.eval (bitSize query)) σ)
      (NativeProjectionOracle.command code coeff)
      (fun _ τ => NativeProjectionResult.Output
        (RationalProjection.classify P ρ (RegisteredLP.certificate f (distanceProgram P x))) τ ∧
        Prefix (encodeProgram P) "lp.input" τ ∧ Prefix (encodeVector x) "projection.center" τ ∧
        τ.vars "projection.n"=n)
      (NativeDistanceOracle.cost m n code coeff (time.eval (bitSize query)) (bitSize query)+25+
        NativeProjectionResult.cost M n)



def queryBound (R : ℕ) : ℕ := NativeProjectionQueryBounds.queryBound R
def certificateHeight {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ := p.width.eval (queryBound R)
def invocationHeight {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ :=
  certificateHeight p R+1000*(R+1)^5+1
def oracleTime {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ := p.time.eval (queryBound R)
def callCost {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ :=
  NativeDistanceOracle.cost (NativeProjectionQueryBounds.rootRows R) R p.code p.coeff
    (oracleTime p R) (queryBound R)+25+NativeProjectionResult.cost (2^invocationHeight p R) R
def wordHeight {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ :=
  2*invocationHeight p R+NativeProjectionQueryBounds.rootHeight R+
    NativeProjectionResources.shape R+queryBound R+p.width.eval (queryBound R+1)+
    oracleTime p R+RamVirtualConstants.allowance p.code+100







end Lax263307Proofs.NativeSelectedLP

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeTrace
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters NativeCoreMachine

def entryCost (a n : ℕ) : ℕ := 12*n.size+12*(2*n).size+12*(4*a+2)+88











end Lax263307Proofs.NativeNodeTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeProtocol
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeOracleContext



















abbrev Eligible := (fuel n : ℕ) → SimpleGraph (Fin n) → ℕ → ℕ → Prop

def GraphData {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ









end Lax263307Proofs.NativeNodeProtocol

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleRounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleRounds

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeOracleContext

/-- The actual program specification already proved by NativeRoundedControl. -/
def Program (p : Lax808846.Ram.Program) (c : ℕ) : Prop :=
    ∀ (n m k h limit projection ret : ℕ),2≤ n → 1≤ h →
    ∀ (state : State n) (a : Fin n → ℤ),
    (∀ i j,Lax263307.NativeRoundedStep.height (state.1 i j) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (rationalNormal a i) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (state.2 i) h) →
    0< rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a) →
    ∀ (B v : ℕ),c*(n+h+k+1)^12≤ v →
    let T := c*(n+h+k+1)^12
    let xs := Lax263307.NativeRoundedStep.encodeInput k state a
    2*(2^v)^2+3< B → T+1< B → RamVirtualConstants.allowance p< B → xs.length+3< B →
    m+k+limit+projection+ret+10< B → (∀ z∈xs,z< B) →
    Spec B (fun σ => NativeRoundedQuery.Data k state a σ ∧ σ.vars "algorithm.roundWidth"=v ∧
      σ.vars "graph.n"=m ∧ σ.vars "round.limit"=limit ∧
      xs.length≤(σ.arrs "vm.input").length ∧ T<(σ.arrs "vm.addresses").length ∧
      T<(σ.arrs "vm.values").length ∧ T<(σ.arrs "vm.output").length ∧
      3*(n*n)≤(σ.arrs "round.shape").length ∧ 3*n≤(σ.arrs "round.center").length)
      (NativeRoundedControl.command p projection ret) (fun _ τ => Prefix (NativeRoundedQuery.shape (update k state a)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center (update k state a)) "round.center" τ ∧
        τ.vars "vec.n"=n ∧ NativeRoundedControl.Output m k limit projection ret τ)
      (NativeRoundedUpdate.timeBound p c n h k+16)



structure Bounds {N : ℕ} (B c h v m j limit : ℕ) (p : Lax808846.Ram.Program)
    (extent : String → ℕ) (state : State N) (a : Fin N → ℤ) : Prop where
  dimension : 2≤ N
  height : 1≤ h
  shapeHeight : ∀ i k,NativeRoundedStep.height (state.1 i k) h
  normalHeight : ∀ i,NativeRoundedStep.height (rationalNormal a i) h
  centerHeight : ∀ i,NativeRoundedStep.height (state.2 i) h
  positive : 0< rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a)
  width : c*(N+h+j+1)^12≤ v
  host : 2*(2^v)^2+3< B
  time : c*(N+h+j+1)^12+1< B
  allowance : RamVirtualConstants.allowance p< B
  query : (NativeRoundedStep.encodeInput j state a).length+3< B
  scalars : m+j+limit+4+14+10< B
  words : ∀ z∈NativeRoundedStep.encodeInput j state a,z< B
  wordRoom : (NativeRoundedStep.encodeInput j state a).length≤ extent "lp.word"
  inputRoom : (NativeRoundedStep.encodeInput j state a).length≤ extent "vm.input"
  addresses : c*(N+h+j+1)^12< extent "vm.addresses"
  values : c*(N+h+j+1)^12< extent "vm.values"
  output : c*(N+h+j+1)^12< extent "vm.output"
  shapeRoom : 3*(N*N)≤ extent "round.shape"
  centerRoom : 3*N≤ extent "round.center"











def oracle {n r : ℕ} (lp flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k p b load F : ℕ) (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) :
    ℕ → (MomentLP.Index n r → ℚ) → Reply (MomentLP.dimension n r) (Finset (Fin n)) :=
  fun _ center => NativeOracleExecution.reply flow G D k p b load child
    (NativeOracleExecution.projection lp G k D F center)









end Lax263307Proofs.NativeOracleRounds

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursiveSetup
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeRecursiveSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators RoundedOracleSearch
open NativeCoreMachine NativeOracleContext NativeNodeProtocol

structure Near {n r : ℕ} (D k p b load fuel S v M h T w space flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (flow : List ℕ → List ℕ) (x : Fin (NativeCatalogMetadata.N n r) → ℚ)
    (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) (eligible : Eligible) : Prop where
  bounds : NativeNearExecution.Bounds n r D k p M h T fuel S w cfg extent front
  hx : ∀ i,NativeSignedArithmetic.Bounded M (x i)
  hselected : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A → A.card≤ r
  htarget : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      ∀ C,ComputedRounding.target (1/(D : ℚ)) (∑ v∈C,(NearOracle.costs (MomentLP.decode x) A v : ℚ))≤ T
  hspace : ∀ a∈NativeSeparatorContext.workspace,space≤ extent a
  flowCall : ∀ A,let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      Spec (2^w) (fun σ => NativeSeparatorContext.Context G costs b load k space σ ∧
          n+1≤(σ.arrs "separator.pieces").length)
        (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
        (fun _ τ => NativeSeparatorContext.Context G costs b load k space τ ∧
          τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
          τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
          Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
          Prefix (NativeCutPieces.words cs) "separator.pieces" τ) flowTime
  children : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
    let costs := NearOracle.costs (MomentLP.decode x) A
    let cs := cuts (step flow G costs b load k) n Finset.univ
    ∀ i∈NearOracle.order cs.length,
    (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈pieces cs i,(costs v : ℚ)) → eligible fuel (pieces cs i).card (restriction G (pieces cs i))
      (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ)))
      (front.length+S*(frameArrays cfg).length+(frameScalars cfg).length)

structure Oracle {n r : ℕ} (D k p b load F fuel S v w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (state : RoundedOracleSearch.State (MomentLP.dimension n r)) (eligible : Eligible) : Prop where
  bounds : NativeOracleExecution.ProjectionBounds D k r F M w oracleTime G extent
  hcenter : ∀ i,NativeSignedArithmetic.Bounded M (state.2 i)
  hquery : (encodeProgram (DistanceProjection.distanceProgram (MomentLP.program G k r)
      (ProjectedOracle.raw state.2))).length< extent "vm.input"
  call : Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw state.2) (NativeNodeTolerance.tolerance n D F) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth)
      (fun _ τ => NativeProjectionResult.Output (NativeOracleExecution.projection lp G k D F state.2) τ ∧
        τ.vars "projection.n"=MomentLP.dimension n r) callCost
  farBounds : ∀ a β,NativeOracleExecution.projection lp G k D F state.2=.far a β →
      (∀ i,NativeSignedArithmetic.Bounded farM (a i)) ∧
      farM*RationalCutBuffer.denominator a+farM+RationalCutBuffer.denominator a+
        3*MomentLP.dimension n r+23<2^w
  nearSetup : ∀ x,NativeOracleExecution.projection lp G k D F state.2=.near x →
      Near D k p b load fuel S v nearM h T w space flowTime childSteps childTime
        cfg G flow x extent front child eligible

structure Rounds {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (eligible : Eligible) : Prop where
  program : NativeOracleRounds.Program cfg.rounded c
  setup : ∀ j,j< limit → Oracle
      D k p b load F fuel S v w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child (trajectory (NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child) j) eligible
  rounded : ∀ j,j< limit → ∀ a,
      NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child j
        (trajectory (NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child) j).2=.cut a →
      NativeOracleRounds.Bounds (2^w) c roundH v n j limit cfg.rounded extent
        (trajectory (NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child) j) a
  hcost : (16*(Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)).length+
      (36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+14+(193*MomentLP.dimension n r+48)+
      NativeNearExecution.timeBound cfg n r nearM S costH childTime flowTime+6≤ oracleCost
  hround : ∀ j,j< limit → NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) roundH j+16≤ roundCost







end Lax263307Proofs.NativeRecursiveSetup

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursionBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRecursionBudget

open Lax263307 AlgorithmParameters

def work (localCost branches : ℕ) : ℕ → ℕ
  | 0 => localCost
  | fuel+1 => localCost+branches*work localCost branches fuel






end Lax263307Proofs.NativeRecursionBudget

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters ComputedSeparators
open NativeCoreMachine NativeOracleContext NativeNodeProtocol

abbrev level (cfg : Config) (n D : ℕ) := AlgorithmParameters.level cfg.a cfg.K cfg.b n D
abbrev dimension (cfg : Config) (n D : ℕ) := MomentLP.dimension n (level cfg n D)
abbrev limit (cfg : Config) (n D : ℕ) := iterations cfg.a cfg.K cfg.b n D
abbrev child {n : ℕ} (cfg : Config) (lp flow : List ℕ → List ℕ) (D fuel : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :=
  fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (restriction G C) t

/-- All arithmetic and allocation obligations of the actual entry, small
and large initialization phases. This record contains no execution premise. -/
structure Bounds (w D k fuel n : ℕ) (cfg : Config) (extent : String → ℕ) : Prop where
  dispatch : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29<2^w
  exhaustive : n*n+(n+1)*(k+1)+n+k+24<2^w
  masks : 2^n<2^w
  choose : ∀ i≤ n,∀ j≤ k,i.choose j<2^w
  classK : 0< cfg.K
  parameters : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+k+cfg.b+5<2^w
  moment : NativeMomentSetup.guardBound n k (level cfg n D)<2^w
  precision : NativeNodePrecision.guard n D (dimension cfg n D)
    (floorDenominator cfg.a cfg.K cfg.b n D) (level cfg n D)<2^w
  round : 3*(dimension cfg n D*dimension cfg n D)+3*dimension cfg n D+20<2^w
  smallTable : (n+1)*(k+1)≤ extent "choose.table"
  largeTable : (n+1)*(level cfg n D+3)≤ extent "choose.table"
  bits : n≤ extent "subset.bits"
  catalog : dimension cfg n D≤ extent "catalog.mask"
  cards : dimension cfg n D≤ extent "catalog.card"
  independent : dimension cfg n D≤ extent "catalog.independent"
  input : NativeMomentInput.length n (level cfg n D)≤ extent "lp.input"
  cache : NativeMomentInput.length n (level cfg n D)≤ extent "moment.program"
  roundInput : 3*(dimension cfg n D*dimension cfg n D)+3*dimension cfg n D≤ extent "lp.input"
  shape : 3*(dimension cfg n D*dimension cfg n D)≤ extent "round.shape"
  center : 3*dimension cfg n D≤ extent "round.center"





/-- The numeric search data at a large node, separated from child
execution. The recursive cost appears only in its proved linear coefficient. -/
structure Search {n : ℕ} (D k fuel S v w childSteps childTime localSteps localTime branches : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ) (eligible : Eligible) where
  M : ℕ
  farM : ℕ
  nearM : ℕ
  costH : ℕ
  T : ℕ
  space : ℕ
  oracleTime : ℕ
  callCost : ℕ
  flowTime : ℕ
  c : ℕ
  roundH : ℕ
  oracleLocal : ℕ
  roundCost : ℕ
  data : NativeRecursiveSetup.Rounds (r:=level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    cfg.b (load cfg.b n D) ((floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D))
    fuel S v (limit cfg n D) w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
    c roundH (oracleLocal+(n+1)*childTime) roundCost cfg G lp flow extent front (child cfg lp flow D fuel G) eligible
  steps : 2+(5*(n+1)+7)*limit cfg n D≤ localSteps
  time : NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (level cfg n D)+2+
    (oracleLocal+roundCost)*limit cfg n D≤ localTime
  branching : (n+1)*limit cfg n D≤ branches







/-- Uniform numerical and solver data for a family of recursive nodes.
Every child-domain condition is a mathematical condition on an actual
computed part; no recursive execution assumption occurs in this record. -/
structure Resources (D S v w localSteps localTime branches : ℕ) (cfg : Config)
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (eligible : Eligible) where
  frameExtents : ∀ a∈frameArrays cfg,extent a=S
  entry : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k cursor,
    eligible fuel n G k cursor → Bounds w D k fuel n cfg extent
  entryCost : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k cursor,
    eligible fuel n G k cursor → 1≤ localSteps ∧ NativeNodeTrace.entryCost cfg.a n≤ localTime
  small : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k cursor,
    eligible fuel n G k cursor → (k≤ cutoff cfg.a cfg.K cfg.b n D ∨ n≤1) →
    2≤ localSteps ∧ NativeNodeTrace.entryCost cfg.a n+NativeExhaustive.cost n k+15*n+20≤ localTime
  large : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k (front : List ℕ),
    eligible (fuel+1) n G k front.length → ¬(k≤ cutoff cfg.a cfg.K cfg.b n D ∨ n≤1) → k≤ n →
    Search D k fuel S v w (NativeRecursionBudget.work localSteps branches fuel)
      (NativeRecursionBudget.work localTime branches fuel) localSteps localTime branches cfg G lp flow extent front eligible





end Lax263307Proofs.NativeNodeExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeNearResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNearResources

open Lax263307 NativeCoreMachine



def space (R : ℕ) : ℕ := 10*(R+1)^2

def wordHeight (cfg : Config) (R H S cursor : ℕ) : ℕ :=
  (36*(5*R+H+20)^4+10)+
  (2*((2*H+1)*(R+1))+4*(3*R+20)+20)+
  (cursor+S*(frameArrays cfg).length+(frameScalars cfg).length+R*R+2*R+
    2*(R+1)+(R+1)+(2*R+2)+3*R+80)+100



end Lax263307Proofs.NativeNearResources

end

-- Solutions.RAM_Lax263307Proofs_NativeSelectedNear
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedNear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeUniformFlow
open scoped NNRat

structure Program (f : List ℕ → List ℕ) where
  code : Lax808846.Ram.Program
  width : Polynomial ℕ
  time : Polynomial ℕ
  output : Polynomial ℕ
  coeff : List ℕ
  coefficients : ∀ z : ℕ,RamPolynomial.value coeff z=width.eval z
  call : ∀ (b n load k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0),
    0< n → 0< load → (∀ v,NativeSignedArithmetic.Bounded (2^h) (x v : ℚ)) →
    let H := NativeLargeResources.heightExponent b n load k h
    ∀ w : ℕ,wordHeight n H code width time output≤ w →
    let cs := cuts (step f G x b load k) n Finset.univ
    Spec (2^w) (fun σ => NativeSeparatorContext.Context G x b load k (spaceBound n H time) σ ∧
      n+1≤(σ.arrs "separator.pieces").length)
      (NativeSeparatorOutput.command code coeff)
      (fun _ τ => NativeSeparatorContext.Context G x b load k (spaceBound n H time) τ ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
        Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
        Prefix (NativeCutPieces.words cs) "separator.pieces" τ)
      (NativeSeparatorOutput.timeBound n H code coeff time)





end Lax263307Proofs.NativeSelectedNear

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRoundedResources

open Lax263307 RoundedOracleSearch Matrix



def space (c R H : ℕ) : ℕ := c*(2*R+H+1)^12+3*R*R+6*R+10

def wordHeight (p : Lax808846.Ram.Program) (v R H : ℕ) : ℕ :=
  2*v+H+Lax455465Proofs.RamVirtualConstants.allowance p+3*R*R+8*R+100





end Lax263307Proofs.NativeRoundedResources

end

-- Solutions.RAM_Lax263307Proofs_NativeSelectedRounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedRounds

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch Matrix
open NativeCoreMachine












def roundCost {lp : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp) (c R : ℕ) : ℕ :=
  NativeRoundedUpdate.timeBound cfg.rounded c R (NativeOraclePrecision.roundedHeight p.width R) R+16









end Lax263307Proofs.NativeSelectedRounds

end

-- Solutions.RAM_Lax263307Proofs_NativeRootResource
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

namespace Lax263307Proofs.NativeRootResource

open Lax263307 AlgorithmParameters

def envelope (C d n D : ℕ) : ℕ := 2^(C*(D*logarithm n)^d)
def budget (Q e C d n D : ℕ) : ℕ := Q*(envelope C d n D+1)^e











end Lax263307Proofs.NativeRootResource

end

-- Solutions.RAM_Lax263307Proofs_NativeEntryResources
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeEntryResources

open Lax263307 AlgorithmParameters NativeCoreMachine



def coefficient (cfg : Config) : ℕ := cfg.a+cfg.K+24*cfg.b+(4*cfg.a+2)+2000
def amount (cfg : Config) (R : ℕ) : ℕ := coefficient cfg*(R+1)^4







end Lax263307Proofs.NativeEntryResources

end

-- Solutions.RAM_Lax263307Proofs_NativePolynomialBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativePolynomialBudget

open Lax455465Proofs

set_option maxHeartbeats 1000000





noncomputable def heightPolynomial (wp : Polynomial ℕ) : Polynomial ℕ :=
  80*(Polynomial.X+1)+(Polynomial.X+1)*(2*wp.comp (1000000*(Polynomial.X+1)^6)+1)+2*Polynomial.X+1




end Lax263307Proofs.NativePolynomialBudget

end

-- Solutions.RAM_Lax263307Proofs_NativeFlowBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000

namespace Lax263307Proofs.NativeFlowBudget

open Lax455465Proofs NativeLargeCapacity NativeLargeResources NativeUniformFlow

noncomputable def numeratorPolynomial (b : ℕ) : Polynomial ℕ :=
  Polynomial.C b*(2*Polynomial.X+1)*(2*Polynomial.X)*(2*Polynomial.X)*(3*Polynomial.X)

noncomputable def resourcePolynomial (b : ℕ) : Polynomial ℕ :=
  Polynomial.C b+Polynomial.X+Polynomial.X+Polynomial.X+Polynomial.X+(2*Polynomial.X+1)+
    2*Polynomial.X+2*Polynomial.X+3*Polynomial.X+Polynomial.C b*(2*Polynomial.X+1)+
    Polynomial.C b*(2*Polynomial.X+1)*(2*Polynomial.X)+
    Polynomial.C b*(2*Polynomial.X+1)*(2*Polynomial.X)*(2*Polynomial.X)+
    2*numeratorPolynomial b+Polynomial.X*Polynomial.X+2*(Polynomial.X*Polynomial.X*Polynomial.X)+20

noncomputable def heightPolynomial (b : ℕ) (hp : Polynomial ℕ) : Polynomial ℕ :=
  hp+numeratorPolynomial b+resourcePolynomial b+Polynomial.X+30

noncomputable def lengthPolynomial : Polynomial ℕ := 2+4*Polynomial.X+8*Polynomial.X*Polynomial.X

noncomputable def queryPolynomial (b : ℕ) (hp : Polynomial ℕ) : Polynomial ℕ :=
  lengthPolynomial*(heightPolynomial b hp+Polynomial.X+4)

noncomputable def widthPolynomial (b : ℕ) (hp wp tp op : Polynomial ℕ) (p : Lax808846.Ram.Program) : Polynomial ℕ :=
  2*wp.comp (queryPolynomial b hp+1)+heightPolynomial b hp+
    (8*Polynomial.X*Polynomial.X+6*Polynomial.X+40)+queryPolynomial b hp+
    tp.comp (queryPolynomial b hp)+op.comp (queryPolynomial b hp)+Polynomial.C (RamVirtualConstants.allowance p)+20

noncomputable def spacePolynomial (b : ℕ) (hp tp : Polynomial ℕ) : Polynomial ℕ :=
  lengthPolynomial+tp.comp (queryPolynomial b hp)+Polynomial.X+2

noncomputable def splitPolynomial (b : ℕ) (hp tp : Polynomial ℕ)
    (p : Lax808846.Ram.Program) (coeff : List ℕ) : Polynomial ℕ :=
  488*Polynomial.X*Polynomial.X+56*Polynomial.X+36+
    ((12*queryPolynomial b hp+39)*lengthPolynomial+Polynomial.C (6*coeff.length+29))+
    ((tp.comp (queryPolynomial b hp)+1)*(Polynomial.C (4*p.length+104)+32*tp.comp (queryPolynomial b hp))+18)

noncomputable def timePolynomial (b : ℕ) (hp tp : Polynomial ℕ)
    (p : Lax808846.Ram.Program) (coeff : List ℕ) : Polynomial ℕ :=
  14*Polynomial.X+8+
    ((21*Polynomial.X+(168*Polynomial.X+132+splitPolynomial b hp tp p coeff)+62)*Polynomial.X+12)+
    37*(Polynomial.X+1)+10














end Lax263307Proofs.NativeFlowBudget

end

-- Solutions.RAM_Lax263307Proofs_NativeSelectedBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 350000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedBudget

open Lax263307 NativeCoreMachine

/-- The finite list of root demands, before recursion frames and local
control costs. Their latter dependence on workspace is polynomial too. -/
noncomputable def demand {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (c R : ℕ) : ℕ :=
  R+NativeSelectedLP.certificateHeight p R+NativeOraclePrecision.roundedHeight p.width R+NativeProjectionResources.wordHeight R+NativeEntryResources.amount cfg R+NativeNearResources.space R+
  NativeProjectionResources.space R (NativeSelectedLP.oracleTime p R)+NativeSelectedLP.wordHeight p R+
  (NativeCutResources.wordExponent R (2*NativeSelectedLP.certificateHeight p R+1)+4)+
  NativeSelectedLP.queryBound R+NativeSelectedLP.callCost p R+
  (NativeFlowBudget.widthPolynomial cfg.b (NativePolynomialBudget.heightPolynomial p.width) q.width q.time q.output q.code).eval R+
  (NativeFlowBudget.spacePolynomial cfg.b (NativePolynomialBudget.heightPolynomial p.width) q.time).eval R+
  (NativeFlowBudget.timePolynomial cfg.b (NativePolynomialBudget.heightPolynomial p.width) q.time q.code q.coeff).eval R+
  NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)+
  NativeSelectedRounds.roundCost cfg p c R+100









end Lax263307Proofs.NativeSelectedBudget

end

-- Solutions.RAM_Lax263307Proofs_NativeQptasImplementation
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQptasImplementation

open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet

/-- All algorithm, backend and root-budget constants are selected once
for the graph class, before any graph, weights, accuracy or host word width. -/
structure Fixed (C : GraphClass) where
  cfg : NativeCoreMachine.Config
  lp : List ℕ → List ℕ
  flow : List ℕ → List ℕ
  projection : NativeSelectedLP.Program lp
  separator : NativeSelectedNear.Program flow
  roundedConstant : ℕ
  roundedPositive : 0< roundedConstant
  projectionCode : projection.code=cfg.lp
  projectionCoeff : projection.coeff=cfg.lpWidth
  separatorCode : separator.code=cfg.flow
  separatorCoeff : separator.coeff=cfg.flowWidth
  encoded : NativeEncodedLP.Encoded lp
  separatorCorrect : NearOracle.SeparatorCorrect (blowUpClass C) flow cfg.a cfg.K cfg.b
  oracleCorrect : NativeRecursiveOracle.OracleCorrect (blowUpClass C) lp flow cfg.a cfg.K cfg.b
  classK : 0< cfg.K
  classB : 0< cfg.b
  rounded : NativeOracleRounds.Program cfg.rounded roundedConstant
  semantic : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G∈C n →
    ∀ weights ε,0<ε → ε<1 → IsApproximation G weights ε (WeightedAlgorithm.solve lp flow cfg.a cfg.K cfg.b G weights ε)
  envelopeCoefficient : ℕ
  envelopeExponent : ℕ
  budgetCoefficient : ℕ
  budgetExponent : ℕ
  envelopeCoefficientPositive : 0< envelopeCoefficient
  envelopeExponentPositive : 0< envelopeExponent
  budgetCoefficientPositive : 0< budgetCoefficient
  budgetExponentPositive : 0< budgetExponent
  uniform : ∀ n D m,0< D → 0< m → m ≤ n → ParameterResources.resource cfg.a cfg.K cfg.b m D ≤
    NativeRootResource.envelope envelopeCoefficient envelopeExponent n D
  budget : ∀ R,NativeSelectedBudget.demand cfg projection separator roundedConstant R ≤ budgetCoefficient*(R+1)^budgetExponent



end Lax263307Proofs.NativeQptasImplementation

end

-- Solutions.RAM_Lax263307Proofs_NativeRootWorkspace
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeRootWorkspace

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds

def stride (W : ℕ) : ℕ := 2*(W+1)
def frameLength (cfg : Config) (W : ℕ) : ℕ := stride W*(frameArrays cfg).length+(frameScalars cfg).length




def hostHeight (cfg : Config) (W : ℕ) : ℕ := W+
  NativeNearResources.wordHeight cfg W W (stride W) ((2*W+2)*frameLength cfg W)+
  NativeRoundedResources.wordHeight cfg.rounded W W W+100











end Lax263307Proofs.NativeRootWorkspace

end

-- Solutions.RAM_Lax263307Proofs_NativeLocalTime
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeLocalTime

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds

def rows (W : ℕ) : ℕ := 2+W*(W+4)
def inputLength (W : ℕ) : ℕ := 2+3*(rows W*W)+3*(rows W+W)
def inputCost (W : ℕ) : ℕ := (22*W+129)*(rows W*W)+57*(rows W+W)+111
def catalog (W : ℕ) : ℕ := (54*(W+1)*(W+3)+(69*W+33)*W+41)*(W+3)+8
def moment (W : ℕ) : ℕ := catalog W+(38*W*W+42*W+60)*W+18
def entry (cfg : Config) (W : ℕ) : ℕ := 36*W+12*(4*cfg.a+2)+88
def large (cfg : Config) (W : ℕ) : ℕ := 36*W+12*(4*cfg.a+2)+76+moment W+
  inputCost W+16*inputLength W+12*W+105*(W*W)+91*W+108
def component (W : ℕ) : ℕ := (36*(2*((2*W+1)*(W+1))+1)+258)*W+72
def part (cfg : Config) (W S : ℕ) : ℕ := 43*W+37+component W+
  ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(W*W)+36)+
  ((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)+
  ((45*W+38)+((28*W+104)*W+30))
def near (cfg : Config) (W S : ℕ) : ℕ := (48*W+2000*(4*W+20)^6+14)+10+
  ((17*W+72*(2*W+1)+270)*W+17*W+67)+(W+10)+part cfg W S*(W+1)+10
def oracle (cfg : Config) (W S : ℕ) : ℕ :=
  (16*inputLength W+(36*(100*(W+1)+1)+124)*W+135+W+2)+14+(193*W+48)+near cfg W S+6
def steps (W : ℕ) : ℕ := 2+(5*(W+1)+7)*W
def branches (W : ℕ) : ℕ := (W+1)*W
def time (cfg : Config) (W S : ℕ) : ℕ := entry cfg W+large cfg W+2+(oracle cfg W S+W)*W+300*(W+2)^3



















end Lax263307Proofs.NativeLocalTime

end

-- Solutions.RAM_Lax263307Proofs_NativeRootTrace
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRootTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine NativeMasks





def Answer {n : ℕ} (answer : Finset (Fin n) × ℕ) (σ : Env) : Prop :=
  σ.vars "root.mask"=mask answer.1 ∧ σ.vars "root.value"=answer.2 ∧ σ.vars "machine.running"=0





end Lax263307Proofs.NativeRootTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeCoreExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCoreExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeOracleContext NativeNodeProtocol

def Root {n : ℕ} (B D S v : ℕ) (cfg : Config) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (extent : String → ℕ) (σ : Env) : Prop :=
  Protocol B D S v cfg extent [] σ ∧ GraphData G σ







structure Input {n : ℕ} (B D fuel S v : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent : String → ℕ) (σ : Env) : Prop where
  bounded : NativeStateBounds.Bounded B σ
  graph : GraphData G σ
  accuracy : σ.vars "node.D"=D
  fuel : σ.vars "recursion.fuel"=fuel
  stride : σ.vars "recursion.stride"=S
  width : σ.vars "algorithm.roundWidth"=v
  lengths : ∀ a,(σ.arrs a).length=extent a



end Lax263307Proofs.NativeCoreExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeUnweightedExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeUnweightedExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 GraphClasses
open NativeCoreMachine NativeRootWorkspace

def cost (cfg : Config) (n W : ℕ) : ℕ :=
  let steps := NativeRecursionBudget.work (NativeLocalTime.steps W) (NativeLocalTime.branches W) (RecursionDepth.depth n)
  let time := NativeRecursionBudget.work (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W) (RecursionDepth.depth n)
  (time+26+68*(steps+3))*n+98





end Lax263307Proofs.NativeUnweightedExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursionDepth
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRecursionDepth

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.RecursionDepth

def step : Com := .seq (.assign "depth.value" (.div (.mul (.lit 2) (.var "depth.value")) (.lit 3)))
  (.assign "depth.count" (.add (.var "depth.count") (.lit 1)))
def loop : Com := .while (.lt (.lit 1) (.var "depth.value")) step
def command : Com := .seq (.assign "depth.value" (.var "graph.n"))
  (.seq (.assign "depth.count" (.lit 0)) loop)





end Lax263307Proofs.NativeRecursionDepth

end

-- Solutions.RAM_Lax263307Proofs_NativeRootAccuracy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRootAccuracy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 RecursionDepth





def finish : Com := .seq (.assign "algorithm.E"
  (.div (.sub (.add (.mul (.lit 2) (.var "accuracy.d")) (.var "accuracy.n")) (.lit 1)) (.var "accuracy.n")))
  (.seq (.assign "node.D" (.mul (.mul (.lit 4) (.add (.var "depth.count") (.lit 1))) (.var "algorithm.E")))
    (.assign "recursion.fuel" (.var "depth.count")))

def command : Com := .seq NativeRecursionDepth.command finish





end Lax263307Proofs.NativeRootAccuracy

end

-- Solutions.RAM_Lax263307Proofs_NativeOriginalAccuracy
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOriginalAccuracy

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeFrontend

/-- Read the original accuracy from the retained input, after activating
the blow-up graph. The offset uses original input.n, not the blow-up order. -/
def command : Com := .seq (.assign "source.accuracy"
  (.add (.mul (.var "input.n") (.var "input.n")) (.mul (.lit 3) (.var "input.n"))))
  (.seq (.assign "accuracy.n" (.get "input.data" (.add (.var "source.accuracy") (.lit 1))))
    (.assign "accuracy.d" (.get "input.data" (.add (.var "source.accuracy") (.lit 2)))))



end Lax263307Proofs.NativeOriginalAccuracy

end

-- Solutions.RAM_Lax263307Proofs_NativeRootBudget
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRootBudget

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open NativeRootResource

def guard (C d Q e n D : ℕ) : ℕ :=
  let X := D*logarithm n
  let H := C*X^d
  let R := envelope C d n D
  let W := budget Q e C d n D
  C+d+Q+e+2*n+D+logarithm n+X+X^d+H+R+(R+1)^e+W+2*(W+1)+100

def first (d : ℕ) : Com := .seq (.assign "power.base" (.mul (.var "node.D") (.var "node.logarithm")))
  (.assign "power.exponent" (.lit d))

def second (C : ℕ) : Com := .seq (.assign "root.exponent" (.mul (.lit C) (.var "power.value")))
  (.seq (.assign "power.base" (.lit 2)) (.assign "power.exponent" (.var "root.exponent")))

def third (e : ℕ) : Com := .seq (.assign "algorithm.resource" (.var "power.value"))
  (.seq (.assign "power.base" (.add (.var "power.value") (.lit 1))) (.assign "power.exponent" (.lit e)))

def finish (Q : ℕ) : Com := .seq (.assign "algorithm.roundWidth" (.mul (.lit Q) (.var "power.value")))
  (.assign "recursion.stride" (.mul (.lit 2) (.add (.var "algorithm.roundWidth") (.lit 1))))









def command (C d Q e : ℕ) : Com := .seq NativeLogarithms.command
  (.seq (first d) (.seq NativeNaturalPower.command (.seq (second C)
    (.seq NativeNaturalPower.command (.seq (third e) (.seq NativeNaturalPower.command (finish Q)))))))




end Lax263307Proofs.NativeRootBudget

end

-- Solutions.RAM_Lax263307Proofs_NativeEmptyOutput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeEmptyOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib Lax455465Proofs
open Lax263307 WeightedIndependentSet

def clear : Com := .seq (.assign "empty.i" (.lit 0))
  (.while (.lt (.var "empty.i") (.var "input.n")) (Fill.put "weighted.output" "empty.i" (.lit 0)))

def command : Com := .seq clear (.seq (.assign "emit.count" (.var "input.n"))
  (RamEmitWords.command "weighted.output" 1))




end Lax263307Proofs.NativeEmptyOutput

end

-- Solutions.RAM_Lax263307Proofs_NativeImageOutput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeImageOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeMasks











def read : Com := .seq
  (.assign "image.bit" (.and (.shiftr (.var "image.mask") (.var "image.i")) (.lit 1)))
  (.assign "image.owner" (.get "image.labels" (.var "image.i")))

def branch : Com := .ite (.eq (.var "image.bit") (.lit 1))
  (.store "image.output" (.var "image.owner") (.lit 1)) .skip

def step : Com := .seq read (.seq branch (.assign "image.i" (.add (.var "image.i") (.lit 1))))







def clear : Com := .seq (.assign "image.clear.i" (.lit 0))
  (.while (.lt (.var "image.clear.i") (.var "image.n")) (Fill.put "image.output" "image.clear.i" (.lit 0)))

def scan : Com := .seq (.assign "image.i" (.lit 0))
  (.while (.lt (.var "image.i") (.var "image.count")) step)

def command : Com := .seq clear (.seq scan (.seq (.assign "emit.count" (.var "image.n"))
  (RamEmitWords.command "image.output" 1)))





end Lax263307Proofs.NativeImageOutput

end

-- Solutions.RAM_Lax263307Proofs_NativeWeightedOutput
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeWeightedOutput

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedAlgorithm IndependentBlowUp WeightedIndependentSet







def metadata : Com := .seq (.assign "image.n" (.var "input.n"))
  (.seq (.assign "image.count" (.var "blowup.length")) (.assign "image.mask" (.var "root.mask")))

def command : Com := .seq metadata (.seq
  (NativeProgramCache.copy "blowup.owner" "image.labels" "image.count") NativeImageOutput.command)







end Lax263307Proofs.NativeWeightedOutput

end

-- Solutions.RAM_Lax263307Proofs_NativeQptasProgram
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeQptasProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet

def order : Com := .assign "graph.n" (.var "blowup.length")

def copyGraph : Com := .seq (.assign "matrix.length" (.mul (.var "graph.n") (.var "graph.n")))
  (NativeProgramCache.copy "blowup.matrix" "search.graph" "matrix.length")

/-- The complete finite source program. Configuration and budget constants
are fixed for the graph class; no input graph, weights, accuracy or word width
is a parameter of this program definition. Correctness still requires the
complete recursive command specification and common resource invariant. -/
def command (cfg : NativeCoreMachine.Config) (C d Q e : ℕ) : Com :=
  .seq NativeBlowUp.prepare (.seq order
    (.ite (.eq (.var "graph.n") (.lit 0)) NativeEmptyOutput.command
      (.seq copyGraph (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (.seq (NativeRootBudget.command C d Q e)
        (.seq (NativeCoreMachine.command cfg) NativeWeightedOutput.command)))))))










end Lax263307Proofs.NativeQptasProgram

end

-- Solutions.RAM_Lax263307Proofs_NativeInputBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeInputBounds

open Lax263307.IndependentSetEncoding

open Lax263307 WeightedIndependentSet

def height {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℕ := rationalBitSize w ε+1



















end Lax263307Proofs.NativeInputBounds

end

-- Solutions.RAM_Lax263307Proofs_NativeQptasPositive
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasPositive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet
open NativeQptasImplementation NativeRootWorkspace

def copies {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : Fin n → ℕ :=
  WeightRounding.copies (PositiveWeights.positiveWeights weights) ε
def order {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : ℕ := ∑ v,copies weights ε v
def denominator (N : ℕ) (ε : ℚ) : ℕ := RecursiveAlgorithm.accuracyDenominator N (ε/2)
def resource {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) : ℕ :=
  NativeRootResource.envelope i.envelopeCoefficient i.envelopeExponent N (denominator N ε)
def workspace {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) : ℕ :=
  i.budgetCoefficient*(resource i N ε+1)^i.budgetExponent

def budgetCost {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) : ℕ :=
  12*N.size+12*(2*N).size+12*i.envelopeExponent+
    12*(i.envelopeCoefficient*(denominator N ε*AlgorithmParameters.logarithm N)^i.envelopeExponent)+
    12*i.budgetExponent+78

def cost {C : GraphClass} (i : Fixed C) (n N : ℕ) (ε : ℚ) : ℕ :=
  NativeBlowUp.cost n N+(16*(N*N)+14)+18+(14*RecursionDepth.depth N+28)+budgetCost i N ε+
    NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+(24*n+44*N+36)+20









end Lax263307Proofs.NativeQptasPositive

end

-- Solutions.RAM_Lax263307Proofs_NativeQptasWordBounds
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeQptasWordBounds

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive

def shape (n N : ℕ) : ℕ := 100*(n+N+1)^4

def width {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : ℕ :=
  let N := order weights ε
  NativeRootWorkspace.hostHeight i.cfg (workspace i N ε)+
    NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent N (denominator N ε)+
    shape n N+16*NativeInputBounds.height weights ε+100











end Lax263307Proofs.NativeQptasWordBounds

end

-- Solutions.RAM_Lax263307Proofs_NativeWeightedExecution
section
set_option maxHeartbeats 0
set_option maxErrors 1000
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeWeightedExecution

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation

def command {C : GraphClass} (i : Fixed C) : Com :=
  NativeQptasProgram.command i.cfg i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent

def cost {C : GraphClass} (i : Fixed C) {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : ℕ :=
  NativeQptasPositive.cost i n (NativeQptasPositive.order weights ε) ε





end Lax263307Proofs.NativeWeightedExecution

end


