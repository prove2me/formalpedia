-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle003
-- name    : ThreeSum1960614_Machine_Bundle003
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:02:19.096001+00:00
-- url     : https://prove2.me/theorems/10a50742-b394-49ef-852d-3607f543d887
-- title:
--   Light-language execution and exact schedule foundations
-- statement:
--   The arithmetic interfaces describe coefficient bounds $|a_j|\le U$ (using zero outside a coefficient list), and local cover parameters at length $464h$ for $h\in\mathbb N$. The local threshold is the output count times $2^{2h}$; a deterministically selected prime $p$ has square between that positive threshold and sixteen times it, and determines the local bucket cap. The executable integer schedule for $m\in\mathbb N$ is
--
--   $$k(m)=2\left\lfloor\frac{\lfloor\sqrt[3]{m}\rfloor}{2}\right\rfloor,\quad b(m)=20\left\lfloor\frac{203889696m}{20000000000k(m)}\right\rfloor,\quad s(m)=b(m)k(m),$$
--   $$d(m)=2^{\lfloor62656016s(m)/1000000000\rfloor}.$$
--
--   The divisions here are natural-number divisions, including their total zero-denominator convention. The even-microblock construction follows the pinned Apache-2.0 upstream formalization.
--
--   The Light language has finite expression and statement trees, integer local variables and memory, arithmetic addition, subtraction and multiplication, memory accesses, branches, loops, and procedure calls. An execution judgment $\operatorname{Exec}(\lambda,P,d,s,\sigma,\sigma',c)$ records an execution of statement $s$ in finite program $P$, at call depth $d$, from state $\sigma$ to state $\sigma'$ in exactly $c$ steps. Limits $\lambda$ bound word magnitudes, memory addresses, and call depth; expression and test costs count their primitive operations. Memory-preservation predicates say that two memories agree on a specified set of natural addresses, including complements of output regions and cells below a free pointer.
--
--   For the target word RAM, the bundle defines an exact number of non-verdict steps between configurations, code placement at an instruction offset, agreement outside a set of integer addresses, and which instructions write only inside a specified set. For any parameter type $A$, domain $D\subseteq A$, and functions $f,g:A\to\mathbb R$, the one-sided domination predicate is
--
--   $$\exists C\ge0\;\forall x\in D,\quad f(x)\le Cg(x).$$
--
--   It also defines absolute bounds on all entries of an integer list. These interfaces support memory framing, compositional step counts, and asymptotic cost estimates in the complete deterministic integer 3SUM runtime proof; the definitions themselves do not assert the final solver theorem.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/KaratsubaBounds.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LocalCoverBounds.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ScaleDefinitions.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Regions.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Syntax.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Machine/Steps.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Util/List.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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

namespace Asymptotics
end Asymptotics
namespace Filter
end Filter
namespace Light
end Light
namespace List
end List
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.List
end ThreeSum1960614.Machine.List
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.Schedule
end ThreeSum1960614.Machine.ThreeSum1960614.Schedule
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Dominated
end ThreeSum1960614.Machine.ThreeSumApsp.Dominated
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSum1960614.Schedule
end ThreeSum1960614.Schedule
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Dominated
end ThreeSumApsp.Dominated
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial
open scoped _root_.BigOperators







def CoeffBound (as : List ℤ) (U : ℤ) : Prop := ∀ j, |as.getD j 0| ≤ U





















end ThreeSum.Karatsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalCoverBounds


open scoped _root_.BigOperators


































/-! ## A deterministic selected prime -/































/-! ## Exact integer rounding of the separable bucket cap -/













/-! ## The actual local parameters at `L=464*h` -/

def localThreshold (h : ℕ) : ℕ := _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h * 2 ^ (2 * h)
def localPrime (h : ℕ) : ℕ := _root_.ThreeSum.LocalCoverBounds.selectedPrime (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)
def localBucketCap (h : ℕ) : ℕ := _root_.ThreeSum.LocalCoverBounds.bucketCap (_root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)

theorem localThreshold_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos (by decide))



theorem localPrime_prime (h : ℕ) : Nat.Prime (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) :=
  (_root_.ThreeSum.LocalCoverBounds.selectedPrime_spec (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)).1

theorem localPrime_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_prime h).pos



theorem localPrime_sq_lower (h : ℕ) :
    _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h * 2 ^ (2 * h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ^ 2 :=
  _root_.ThreeSum.LocalCoverBounds.selectedPrime_sq_lower (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h)

theorem localPrime_sq_upper (h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ^ 2 ≤ 16 * (_root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h * 2 ^ (2 * h)) :=
  _root_.ThreeSum.LocalCoverBounds.selectedPrime_sq_upper (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold_pos h)

















end ThreeSum.LocalCoverBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Executable natural-number schedules from PROOF.md, Section 4.1.
The even microblock construction follows c0ldzy17/three-sum-lean,
Submission/ThreeSum/Scales.lean at commit
2b639655e07421b9ac743de9090459bab473a7c0 (Apache-2.0).
These definitions describe the changed schedule; their integration into
the complete Light/word-RAM solver is a separate obligation.
-/

namespace ThreeSum1960614.Schedule
open _root_.ThreeSum1960614.Schedule




def microSize (m : ℕ) : ℕ := 2 * (Nat.nthRoot 3 m / 2)

def blockCount (m : ℕ) : ℕ :=
  20 * (203889696 * m / (20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m))

def totalSize (m : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.blockCount m * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m

def bandExponent (m : ℕ) : ℕ := 62656016 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m / 1000000000

def bandDivisor (m : ℕ) : ℕ := 2 ^ _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m

end ThreeSum1960614.Schedule

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/

/-- The memory `μ'` agrees with `μ` on every cell that satisfies `K`. -/
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b

/-- The memory `μ'` agrees with `μ` outside the `n` cells from address `a`. -/
abbrev SameOutside (μ μ' : ℕ → ℤ) (a n : ℕ) : Prop := _root_.ThreeSum1960614.Machine.Light.SameOn (_root_.Light.Outside a n) μ μ'

/-- The memory `μ'` agrees with `μ` outside the `n` cells from `a` and the `m` cells from `b`. -/
abbrev SameOutside2 (μ μ' : ℕ → ℤ) (a n b m : ℕ) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.SameOn (fun x => _root_.Light.Outside a n x ∧ _root_.Light.Outside b m x) μ μ'



/-- No cell below the free pointer has changed. -/
abbrev Kept (μ μ' : ℕ → ℤ) (fr : ℕ) : Prop := _root_.ThreeSum1960614.Machine.Light.SameOn (· < fr) μ μ'

/-- No cell below the free pointer has changed, except the `len` cells from `out`. -/
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  _root_.ThreeSum1960614.Machine.Light.SameOn (fun x => x < fr ∧ _root_.Light.Outside out len x) μ μ'

variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}

/-- The case of a single cell. -/
theorem SameOn.cell (h : _root_.ThreeSum1960614.Machine.Light.SameOn (· = b) μ μ') : μ' b = μ b := h b rfl











/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The light language

A small imperative language with procedures and recursion, in which the paper's procedures can be
written almost as printed.  It is a proof device: a program of this language is compiled
(`compileProgram`) to the word RAM of the end statement, and the compiler is proved to keep results
and, up to a constant factor that depends on the program text only, step counts.

* A program is a finite piece of data: a list of procedure bodies.  It contains no Lean functions.
* The memory is an array of integers addressed by natural numbers.  Each running procedure has local
  variables 0, 1, 2, ….
* Arithmetic: +, −, ×.  There is no division.  Comparisons (<, =) occur as the tests of if and
  while.
* Every executed operation costs one step: each constant, variable, operation and load of an
  expression, each comparison, assignment, store, branch, call and return.
* A run is subject to limits: it forms no value of absolute value above `word`, touches no cell at
  an address ≥ `space`, and nests calls at most `depth` deep.  A run that would break a limit does
  not exist.
-/

@[expose] public section

namespace Light
open _root_.Light






/-- Expressions: constants, local variables, operations, and the content of the memory cell at an
address. -/
inductive Expr : Type
  | const (n : ℕ)
  | var (x : ℕ)
  | op (o : _root_.Light.Op) (a b : Expr)
  | load (a : Expr)
  deriving Repr

/-- Tests. -/
inductive Cond : Type
  | lt (a b : _root_.ThreeSum1960614.Machine.Light.Expr)
  | eq (a b : _root_.ThreeSum1960614.Machine.Light.Expr)
  deriving Repr

/-- Statements.  `call p args x` runs procedure number p on the values of args and puts its result
into x. -/
inductive Stmt : Type
  | skip
  | set (x : ℕ) (e : _root_.ThreeSum1960614.Machine.Light.Expr)
  | store (a e : _root_.ThreeSum1960614.Machine.Light.Expr)
  | seq (s₁ s₂ : Stmt)
  | ite (c : _root_.ThreeSum1960614.Machine.Light.Cond) (s₁ s₂ : Stmt)
  | while (c : _root_.ThreeSum1960614.Machine.Light.Cond) (s : Stmt)
  | call (p : ℕ) (args : List _root_.ThreeSum1960614.Machine.Light.Expr) (x : ℕ)
  deriving Repr

/-- A program: the bodies of its procedures, numbered from 0. -/
abbrev Program : Type := List _root_.ThreeSum1960614.Machine.Light.Stmt

/-- What a running procedure sees: its local variables and the memory. -/
structure State : Type where
  loc : ℕ → ℤ
  mem : ℕ → ℤ

/-- The limits on a run: largest absolute value of a word, number of memory cells, nesting depth of
calls. -/
structure Limits : Type where
  word : ℤ
  space : ℕ
  depth : ℕ

/-- The value of an expression. -/
def Expr.val (s : _root_.ThreeSum1960614.Machine.Light.State) : _root_.ThreeSum1960614.Machine.Light.Expr → ℤ
  | _root_.ThreeSum1960614.Machine.Light.Expr.const n => n
  | _root_.ThreeSum1960614.Machine.Light.Expr.var x => s.loc x
  | _root_.ThreeSum1960614.Machine.Light.Expr.op o a b => o.eval (a.val s) (b.val s)
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a => s.mem (a.val s).toNat

/-- The number of steps that evaluating an expression takes: one for each of its constants,
variables, operations, loads. -/
def Expr.cost : _root_.ThreeSum1960614.Machine.Light.Expr → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Expr.const _ => 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.var _ => 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.op _ a b => a.cost + b.cost + 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a => a.cost + 1

/-- An address within the limits. -/
def Limits.Addr (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (a : ℤ) : Prop := 0 ≤ a ∧ a < lim.space

/-- The evaluation of an expression stays within the limits: every value that is formed fits in a
word, and every address that is read is within the memory. -/
def Expr.Safe (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (s : _root_.ThreeSum1960614.Machine.Light.State) : _root_.ThreeSum1960614.Machine.Light.Expr → Prop
  | _root_.ThreeSum1960614.Machine.Light.Expr.const n => (n : ℤ) ≤ lim.word
  | _root_.ThreeSum1960614.Machine.Light.Expr.var _ => True
  | _root_.ThreeSum1960614.Machine.Light.Expr.op o a b => a.Safe lim s ∧ b.Safe lim s ∧ |o.eval (a.val s) (b.val s)| ≤ lim.word
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a => a.Safe lim s ∧ lim.Addr (a.val s)

/-- Whether a test holds. -/
def Cond.Holds (s : _root_.ThreeSum1960614.Machine.Light.State) : _root_.ThreeSum1960614.Machine.Light.Cond → Prop
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b => a.val s < b.val s
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b => a.val s = b.val s

/-- The number of steps of a test: its two sides and the comparison. -/
def Cond.cost : _root_.ThreeSum1960614.Machine.Light.Cond → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b => a.cost + b.cost + 1
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b => a.cost + b.cost + 1

/-- The evaluation of a test stays within the limits. -/
def Cond.Safe (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (s : _root_.ThreeSum1960614.Machine.Light.State) : _root_.ThreeSum1960614.Machine.Light.Cond → Prop
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b => a.Safe lim s ∧ b.Safe lim s
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b => a.Safe lim s ∧ b.Safe lim s





/-- `Exec lim P d s σ σ' c`: within the limits lim, and at nesting depth d of calls, the statement
s of the program P, started in the state σ, ends in the state σ' after exactly c steps. -/
inductive Exec (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (P : _root_.ThreeSum1960614.Machine.Light.Program) : ℕ → _root_.ThreeSum1960614.Machine.Light.Stmt → _root_.ThreeSum1960614.Machine.Light.State → _root_.ThreeSum1960614.Machine.Light.State → ℕ → Prop
  | skip {d σ} : Exec lim P d _root_.ThreeSum1960614.Machine.Light.Stmt.skip σ σ 0
  | set {d σ x e} : e.Safe lim σ →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } (e.cost + 1)
  | store {d σ a e} : a.Safe lim σ → e.Safe lim σ → lim.Addr (a.val σ) →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) σ { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
        (a.cost + e.cost + 1)
  | seq {d σ σ' σ'' s₁ s₂ c₁ c₂} : Exec lim P d s₁ σ σ' c₁ → Exec lim P d s₂ σ' σ'' c₂ →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂) σ σ'' (c₁ + c₂)
  | iteTrue {d σ σ' c s₁ s₂ k} : c.Safe lim σ → c.Holds σ → Exec lim P d s₁ σ σ' k →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | iteFalse {d σ σ' c s₁ s₂ k} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d s₂ σ σ' k →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ σ' (c.cost + 1 + k)
  | whileFalse {d σ c s} : c.Safe lim σ → ¬ c.Holds σ → Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ σ (c.cost + 1)
  | whileTrue {d σ σ' σ'' c s k₁ k₂} : c.Safe lim σ → c.Holds σ → Exec lim P d s σ σ' k₁ →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ' σ'' k₂ → Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ σ'' (c.cost + 1 + k₁ + k₂)
  | call {d σ σ' p args x body k} : (∀ e ∈ args, e.Safe lim σ) → P[p]? = some body → d < lim.depth →
      Exec lim P (d + 1) body ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ σ' k →
      Exec lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩
        ((args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + k)

/-- Everything held in a variable or in a cell fits in a word. -/
def State.Bounded (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  (∀ x, |σ.loc x| ≤ lim.word) ∧ ∀ a, |σ.mem a| ≤ lim.word

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Running the word RAM: words, steps, pieces of code, straight-line code, branches

What the proofs about compiled code need to know about the word RAM in which the paper's claims are
stated.

* **Words.**  `wd W v` is the word of the integer v.  If v is in the range of signed words
  (`InRange`), the word gives back v (`toInt_wd`).
* **Steps.**  The end statement defines only whole runs (`exec`).  A configuration (`Cfg`) and a
  single step (`step`) are defined here; `exec_succ_of_step` and `exec_succ_of_verdict` say that
  `exec` takes one step at a time.
* **Runs.**  `Steps P n c c'`: exactly n steps lead from c to c', none of them a verdict.
  Runs are composed by `Steps.trans`; a run that ends before a verdict gives the value of `exec`
  (`exec_of_steps`), and more time does not change that value (`exec_mono`).
* **Code.**  `CodeAt P pos l`: the program P has the instructions of the list l from position pos
  on.
* **Straight-line code.**  Six instructions only change the memory (`Straight`, `effect`); a list
  of them runs through in its length (`steps_straight`).
* **Known numbers.**  On cells that hold the words of known numbers, an instruction writes the word
  of a known number: `effect_add`, …, `effect_store` for the memory; `steps_add`, `steps_sub`,
  `steps_load`, `steps_store` for the step.
* **Branches and verdicts.**  A branch on a cell that holds a known number is `steps_bltz`;
  `Steps.branch` turns its two outcomes into the two outcomes of a test.  The verdicts are
  `step_accept` and `step_reject`.
* **Framing.**  `AgreeOutside s m m'`: the memories m and m' are equal outside the set s of cells.
  For code without stores such a set can be read off the text (`WritesIn`, `agreeOutside_effects`).
-/

@[expose] public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam


open _root_.EndStatement renaming Instr -> Instr
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

variable {W : ℕ} {P : List _root_.EndStatement.Instr}

/-! ## Words -/























/-! ## Configurations and single steps -/





/-! ## Runs -/

/-- n steps of the machine, none of which gives a verdict, lead from c to c'. -/
def Steps (P : List _root_.EndStatement.Instr) : ℕ → _root_.ThreeSumApsp.WordRam.Cfg W → _root_.ThreeSumApsp.WordRam.Cfg W → Prop
  | 0, c, c' => c = c'
  | n + 1, c, c' => ∃ c₁, _root_.ThreeSumApsp.WordRam.step P c = .inl c₁ ∧ Steps P n c₁ c'























/-! ## Pieces of code -/

/-- The program P has the instructions of the list l from position pos on. -/
def CodeAt (P : List _root_.EndStatement.Instr) (pos : ℕ) (l : List _root_.EndStatement.Instr) : Prop := l <+: P.drop pos













/-! ## Straight-line code -/



















/-! ## Single instructions on cells that hold known numbers -/

section known

variable {m : ℤ → BitVec W} {i j k a b : ℤ}





















end known

/-! ## Branches and verdicts -/









/-! ## Framing -/

section framing

variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}

/-- The memory m' differs from m only in cells of the set s. -/
def AgreeOutside (s : Set ℤ) (m m' : ℤ → BitVec W) : Prop := Set.EqOn m' m sᶜ















/-- The instruction writes no cell outside s, whatever the memory holds. -/
def WritesIn (s : Set ℤ) : _root_.EndStatement.Instr → Prop
  | _root_.EndStatement.Instr.one i | _root_.EndStatement.Instr.add i _ _ | _root_.EndStatement.Instr.sub i _ _ | _root_.EndStatement.Instr.mul i _ _ | _root_.EndStatement.Instr.load i _ => i ∈ s
  | _root_.EndStatement.Instr.store _ _ => False
  | _ => True







end framing

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Bounds up to a constant factor, in several parameters

The paper writes `f = O(g)` for functions of several parameters that are tied by side conditions,
such as `D ^ 18 ≤ n` for the parameters `n`, `D`, `w`. `Dominated dom f g` says this: there is a
constant `C ≥ 0` with `f x ≤ C * g x` for every tuple `x` of parameters that satisfies `dom x`. If
there is no side condition, `dom` is `fun _ => True`. The type `α` of the parameters is best a
structure with one named field for each of them, so that a bound reads
`Dominated (fun p => p.D ^ 18 ≤ p.n) (fun p => cost p) fun p => p.n ^ 2 / p.D`.

The lemmas of this file are the steps that the paper takes without comment: such bounds can be
chained (`Dominated.trans`), added (`Dominated.add`, `Dominated.add_add`), multiplied and divided
(`Dominated.mul`, `Dominated.mul_left`, `Dominated.const_mul`, `Dominated.pow`,
`Dominated.div_right`), joined by a case distinction (`Dominated.ite`), restricted to a smaller
domain (`Dominated.mono_dom`) and specialized (`Dominated.comp`). With them no proof has to name a
constant. A bound enters the calculus by `Dominated.of_le`, `Dominated.of_le_const_mul` or
`Dominated.of_exists_const`, and leaves it by `obtain ⟨C, hC, hle⟩` or `Dominated.exists_const_and`.
For functions of one natural number, `Dominated.of_eventually` takes a bound for all large `n`,
`Dominated.isBigO` gives Mathlib's `f =O[atTop] g`, and `isBigO_comp_add_one` substitutes a size
that need not tend to infinity.

In every closure lemma the bound comes first and the side conditions follow.

For nonnegative `f` and `g` the notion is Mathlib's `f =O[𝓟 {x | dom x}] g`, big-O along the
principal filter of the domain (`dominated_iff_isBigO_principal`). The one-sided form is taken
because a running time is bounded from above only.

## The notions of "bounded up to a constant" in this library

* `f =O[atTop] g` of Mathlib bounds `|f|` for large `n`. In this sense `IsBigOPow f a` is `O(n^a)`,
  `IsPowPolylog f a` is `O(n^a (log n)^e)` for some `e`, and `IsPowLittleO f a` is `n^{a+o(1)}`.
  The exponents of the theorems are stated with them.
* `UpperBigOPow`, `UpperPowPolylog` and `UpperPowLittleO` are the same three classes as bounds on
  `f` and not on `|f|`, for running times. A two-sided bound gives the one-sided one
  (`IsBigOPow.upperBigOPow`, `IsPowPolylog.upperPowPolylog`, `IsPowLittleO.upperPowLittleO`).
* `Dominated dom f g` bounds `f` on the whole domain, for several parameters. It comes from a bound
  for large `n` by `Dominated.of_eventually` and gives one by `Dominated.isBigO`.
* `Scale.SoftO t e` says that a count `t` with values in `ℕ` is `Dominated` by a monomial with the
  exponents `e`, up to powers of one more quantity; the tactic `growth` reads the exponents off an
  explicit expression. It gives a `Dominated` bound by `Scale.SoftO.dominated`. Its instance
  `SoftOSqrtPow` gives `IsPowPolylog` by `SoftOSqrtPow.isPowPolylog`.
-/

@[expose] public section

open _root_.Filter
open _root_.Asymptotics

namespace ThreeSumApsp
open _root_.ThreeSumApsp


/-- `f = O(g)` on the domain `dom`: there is a constant `C ≥ 0` with `f x ≤ C * g x` whenever
`dom x`. It is an upper bound on `f` and not on `|f|`. -/
def Dominated {α : Type*} (dom : α → Prop) (f g : α → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, dom x → f x ≤ C * g x

namespace Dominated
open _root_.ThreeSumApsp.Dominated


variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

/-! ### Entering the calculus -/













/-! ### Leaving the calculus -/



/-! ### Chaining, restricting, substituting -/













/-! ### Sums and case distinctions -/







/-! ### Products and quotients -/

















/-! ### Functions of one natural number -/







end Dominated



end ThreeSumApsp

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List
open _root_.List


variable {α β : Type*}

/-! ## Entries with a default -/



















/-! ## Blocks one after the other -/

















/-! ## Sums -/













section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]





end









/-! ## A running minimum -/





/-! ## Counting -/

















/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]







end Sorted

end List

namespace ThreeSumApsp
open _root_.ThreeSumApsp


variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U







/-! ## The entrywise sum of lists -/





end ThreeSumApsp

end

end ThreeSum1960614.Machine


