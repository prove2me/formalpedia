-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle009
-- name    : ThreeSum1960614_Machine_Bundle009
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:23:07.568272+00:00
-- url     : https://prove2.me/theorems/f59214e1-2624-4929-90c9-41ed838bdf0f
-- title:
--   Arithmetic routines and Light-to-word-RAM solver specifications
-- statement:
--   This bundle defines finite Light programs for Euclidean remainder, rounded logarithms, rounded cube root, rounded halving, merging, power tables, and integer square root. For an integer $x$ and positive modulus $M$, the remainder program uses a doubling table and sign correction; its precondition reserves logarithmically many cells and a word bound at least $4V+4M+16$ for inputs bounded by $V$. The local-only routines target $\lfloor\log_2x\rfloor$ (zero at $x=0$), $\lceil\log_2x\rceil$ (zero for $x\le1$), $\lceil\sqrt[3]{x}\rceil$, $\lceil x/2\rceil$, and $\lfloor\sqrt{x}\rfloor$. Merge copies the recursively defined merge of two integer lists into a disjoint output segment; its invariant records consumed prefixes, the output length, and preservation outside that segment. Power-table invariants record the entries $1,b,\ldots,b^{j-1}$ and current power $b^j$.
--
--   For a word-RAM problem, a Light program specification quantifies over every input in the stated domain and requires a correct terminating execution within its real time bound. Run limits are polynomially bounded in the input parameters. A two-stage matrix specification additionally bounds preprocessing time, space and call depth, establishes a memory predicate, and requires every subsequent query to return the requested matrix-product entry while preserving that predicate. The bundle defines the program-dependent word-size slope and time constant used when transferring these specifications to the target word RAM. Its 3SUM task takes $N,U\ge1$, a length-$N$ integer list bounded by $U$, and a memory segment below the free pointer; the specified result indicates whether three distinct positions sum to zero.
--
--   For a global output $q$, a set $I$ of completed blocks, and fixed left subsets $u_i$, completed choice tuples have output $q$ and those fixed left endpoints on $I$. Residual subsets lie in the remaining output coordinates and must reconstruct independently admissible left and right endpoints. With finite index sets $B,C$, integer label maps $b,c$, and integer modulus/offset parameters $P,d$, the stored prefix value is a signed subset-Moebius query of the product of the two partial zeta transforms, evaluated over the residual output set.
--
--   These definitions expose the executable arithmetic, machine-transfer contracts, and forced-prefix query meaning needed to prove the full deterministic integer 3SUM runtime bound. The underlying language-library routines retain the pinned upstream attribution.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Emod.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Logs.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Merge.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/PowTable.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Sqrt.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/ToMachine.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Programs/Tasks.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BlockForced.lean

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
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Flag
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
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
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
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

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace Light.Emod
end Light.Emod
namespace Light.Logs
end Light.Logs
namespace Light.Merge
end Light.Merge
namespace Light.PowTable
end Light.PowTable
namespace Light.Sqrt
end Light.Sqrt
namespace Light.ThinArg
end Light.ThinArg
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.Light.Logs
end ThreeSum1960614.Machine.Light.Logs
namespace ThreeSum1960614.Machine.Light.Merge
end ThreeSum1960614.Machine.Light.Merge
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.Light.Sqrt
end ThreeSum1960614.Machine.Light.Sqrt
namespace ThreeSum1960614.Machine.Light.ThinArg
end ThreeSum1960614.Machine.Light.ThinArg
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Spec
end ThreeSum1960614.Machine.ThreeSumApsp.Spec
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Spec
end ThreeSumApsp.Spec
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

/-!
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
namespace Emod
open _root_.Light.Emod









end Emod

open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod in
/-- One entry of the table: the multiple is written to the table and doubled. -/
def emodTableRound : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Free) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Count)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Mult)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Count ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Count) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Mult ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Mult) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Mult)))))

open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod in
/-- The table: M, 2M, 4M, … are written to the free pointer as long as they are at most |x|. -/
def emodTable : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.while ((_root_.ThreeSum1960614.Machine.Light.Cond.le (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Mult) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Rest))) _root_.ThreeSum1960614.Machine.Light.emodTableRound

open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod in
/-- The last entry of the table that has not been tried is subtracted if possible. -/
def emodReduceRound : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Count ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Count) (_root_.ThreeSum1960614.Machine.Light.k 1))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.le (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Free) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Count))) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Rest)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Rest ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Rest) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Free) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Count))))) _root_.ThreeSum1960614.Machine.Light.Stmt.skip))

open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod in
/-- The entries of the table are subtracted, from the largest down, where possible. -/
def emodReduce : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.while ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Count))) _root_.ThreeSum1960614.Machine.Light.emodReduceRound

open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod in
/-- The sign: the remainder r of |x| gives the remainder of x. -/
def emodSign : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Arg) (_root_.ThreeSum1960614.Machine.Light.k 0)))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.eq (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Rest) (_root_.ThreeSum1960614.Machine.Light.k 0))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Arg (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Arg (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Modulus) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Rest)))))
    (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Arg (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Rest))

open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod in
/-- emod(x, M, fr). -/
def emodBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Arg) (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Rest ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (_root_.ThreeSum1960614.Machine.Light.k 0) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Arg))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Rest (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Arg))) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Count (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Emod.Mult (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Emod.Modulus)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq _root_.ThreeSum1960614.Machine.Light.emodTable (_root_.ThreeSum1960614.Machine.Light.Stmt.seq _root_.ThreeSum1960614.Machine.Light.emodReduce _root_.ThreeSum1960614.Machine.Light.emodSign)))))










namespace Emod
open _root_.Light.Emod


/-- What emod asks of the limits, for a modulus M ≥ 1, numbers up to V and the free pointer fr. -/
structure Pre (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (Mo V fr : ℕ) : Prop where
  mod_pos : 1 ≤ Mo
  space : (lim.space : ℤ) ≤ lim.word
  word : (4 * V + 4 * Mo + 16 : ℤ) ≤ lim.word
  free : fr + (Nat.log 2 (V + 1) + 2) ≤ lim.space

/-- The first i entries of the table are in place, and no cell below the free pointer has changed.
-/
def Table (μ μ' : ℕ → ℤ) (Mo fr i : ℕ) : Prop :=
  (∀ j < i, μ' (fr + j) = ((Mo * 2 ^ j : ℕ) : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr

variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}









end Emod

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

namespace Logs
open _root_.Light.Logs






end Logs

open _root_.Light.Logs
open _root_.ThreeSum1960614.Machine.Light.Logs

/-! ## The logarithm, rounded down -/

/-- log2(x): the candidate is L, and the power is 2^(L + 1). -/
def log2Body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Power (_root_.ThreeSum1960614.Machine.Light.k 2)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.le (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Power) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Arg)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Power ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Power) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Power))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand) (_root_.ThreeSum1960614.Machine.Light.k 1))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Arg (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand)))))





/-! ## The logarithm, rounded up -/

/-- clog2(x): the candidate is L, and the power is 2^L. -/
def clog2Body : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Power (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Power) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Arg)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Power ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Power) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Power))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand) (_root_.ThreeSum1960614.Machine.Light.k 1))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Arg (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand)))))





/-! ## The cube root, rounded up -/



















/-- cbrtCeil(n): the candidate is s. -/
def cbrtCeilBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.lt ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Arg)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Arg (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand))))





/-! ## Halves, rounded up -/

/-- half(h): the candidate is r. -/
def halfBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.lt ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Arg)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Cand ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand) (_root_.ThreeSum1960614.Machine.Light.k 1)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Logs.Arg (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Logs.Cand))))





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Merging two segments

merge(a, na, b, nb, dst) writes the merge of the na cells from a and the nb cells from b to the na +
nb cells from dst, within `mergeTime (na + nb)` steps (`merge_meets`).  The model is `List.merge`:
the next output is the head of the first list unless the head of the second list is smaller.
Nothing is assumed about the order of the two lists.  Numbers are only compared and copied, so their
size does not matter.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

namespace Merge
open _root_.Light.Merge


/-! ## The pure side: one step of List.merge on the rests of two lists -/

variable {l r : List ℤ} {i j : ℕ}









end Merge

/-! ## The program -/

namespace Merge
open _root_.Light.Merge










end Merge

open _root_.Light.Merge
open _root_.ThreeSum1960614.Machine.Light.Merge in
/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.Dest) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.ListA) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Merge.DoneA ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA) (_root_.ThreeSum1960614.Machine.Light.k 1))))

open _root_.Light.Merge
open _root_.ThreeSum1960614.Machine.Light.Merge in
/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.Dest) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB)) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.ListB) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB)))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Merge.DoneB ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB) (_root_.ThreeSum1960614.Machine.Light.k 1))))

open _root_.Light.Merge
open _root_.ThreeSum1960614.Machine.Light.Merge in
/-- merge(a, na, b, nb, dst). -/
def mergeBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Merge.DoneA (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Merge.DoneB (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.lt ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.LenA) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.LenB))) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.LenA)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.LenB)) (_root_.ThreeSum1960614.Machine.Light.Stmt.ite (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.ListB) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneB))) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.ListA) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Merge.DoneA)))) _root_.ThreeSum1960614.Machine.Light.mergeTakeRight _root_.ThreeSum1960614.Machine.Light.mergeTakeLeft) _root_.ThreeSum1960614.Machine.Light.mergeTakeLeft) _root_.ThreeSum1960614.Machine.Light.mergeTakeRight))))

namespace Merge
open _root_.Light.Merge


/-- What merge assumes: the two lists lie in the memory, and the output region is within the memory
and meets neither of them. -/
structure Pre (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  segL : _root_.ThreeSum1960614.Machine.Light.Seg μ a l
  segR : _root_.ThreeSum1960614.Machine.Light.Seg μ b r
  spaceL : a + l.length ≤ lim.space
  spaceR : b + r.length ≤ lim.space
  spaceD : dst + (l.length + r.length) ≤ lim.space
  sepL : _root_.Light.Apart a l.length dst (l.length + r.length)
  sepR : _root_.Light.Apart b r.length dst (l.length + r.length)

/-- The state after i cells of the first list and j cells of the second have been taken: they stand,
merged, in the first i + j cells of dst, and no cell outside dst has changed. -/
def Inv (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (out : List ℤ), σ = ⟨_root_.Light.frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r

/-- The invariant of the loop: t cells have been taken. -/
def Taken (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (t : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ i j, i + j = t ∧ _root_.ThreeSum1960614.Machine.Light.Merge.Inv μ a b dst l r i j σ

variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}









end Merge

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable

/-- One round: dst[j] := p; p := p * b. -/
def powTableRound : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.PowTable.Dest) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.PowTable.Expo)) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.PowTable.Power)) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.PowTable.Power ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.PowTable.Power) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.PowTable.Base))))

/-- powTable(dst, L, b): p := 1; for j < L: dst[j] := p; p := p * b. -/
def powTableBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.PowTable.Power (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.for _root_.Light.PowTable.Expo (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.PowTable.Len) _root_.ThreeSum1960614.Machine.Light.powTableRound))



/-- The state before round j: p = b^j, the first j cells hold the powers up to b^(j-1), and no cell
outside the L cells from dst has changed.  The list t holds the local variables after the five of
powTable. -/
def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨_root_.Light.frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The integer square root by counting up

sqrt(K) returns ⌊√K⌋ within `sqrtTime K` steps (`sqrt_meets`), by running through the squares 1, 4,
9, …: after (k + 1)² comes (k + 1)² + 2k + 3.  It does not touch the memory.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

namespace Sqrt
open _root_.Light.Sqrt






end Sqrt

open _root_.Light.Sqrt
open _root_.ThreeSum1960614.Machine.Light.Sqrt in
/-- sqrt(K). -/
def sqrtBody : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Sqrt.Cand (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Sqrt.Square (_root_.ThreeSum1960614.Machine.Light.k 1)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.le (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Sqrt.Square) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Sqrt.Arg)) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Sqrt.Square ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Sqrt.Square) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (_root_.ThreeSum1960614.Machine.Light.k 2) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Sqrt.Cand))) (_root_.ThreeSum1960614.Machine.Light.k 3))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Sqrt.Cand ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Sqrt.Cand) (_root_.ThreeSum1960614.Machine.Light.k 1))))) (_root_.ThreeSum1960614.Machine.Light.Stmt.set _root_.Light.Sqrt.Arg (_root_.ThreeSum1960614.Machine.Light.v _root_.Light.Sqrt.Cand)))))





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.Light.Compiler
open _root_.ThreeSum1960614.Machine.Light.Compiler
open _root_.EndStatement renaming exec -> exec
open _root_.EndStatement renaming loadWords -> loadWords

/-! ## The notion for light programs -/

/-- The limits are at most 2^s ((p₁ + 1) (p₂ + 1) ⋯)^k in the parameters of the instance. -/
structure Small (s k : ℕ) (params : List ℕ) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) : Prop where
  nonneg : 0 ≤ lim.word
  word : lim.word ≤ (_root_.Light.polyBound s k params : ℤ)
  space : lim.space ≤ _root_.Light.polyBound s k params
  depth : lim.depth ≤ _root_.Light.polyBound s k params

/-- What is asked of the run of procedure p0 on the instance x: within the limits lim it ends in the
state σ' after c steps. -/
structure ProgramSolvesAt (prob : _root_.ThreeSumApsp.WordRam.Problem) (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (x : prob.Inst) (T : ℝ) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (σ' : _root_.ThreeSum1960614.Machine.Light.State) (c : ℕ) : Prop where
  /-- The run starts on the memory that holds the input of the problem. -/
  run : _root_.ThreeSum1960614.Machine.Light.Exec lim P 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt p0) ⟨_root_.Light.frame [0, 0, 0], _root_.Light.memOf (prob.input x)⟩ σ' c
  /-- It ends within the time bound. -/
  time : (c : ℝ) ≤ T
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ prob.input x, |v| ≤ lim.word
  /-- The limits are polynomial in the parameters of the instance. -/
  small : _root_.ThreeSum1960614.Machine.Light.Small s k (prob.params x) lim
  /-- The result gives the verdict, and the cells after the input hold the output. -/
  answer : prob.IsAnswer x (_root_.Light.verdictOf dec (σ'.loc 0)) fun i => σ'.mem ((prob.input x).length + i)

/-- **A light program solves a problem.**  Procedure p0 of P, called on the memory that holds the
input of the problem, ends within T x steps and within limits that are polynomial in the
parameters; its result gives the verdict (if dec: accept exactly if the result is positive;
otherwise accept), and the cells after the input hold the output. -/
def ProgramSolves (prob : _root_.ThreeSumApsp.WordRam.Problem) (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool) (s k : ℕ)
    (dom : prob.Inst → Prop) (T : prob.Inst → ℝ) : Prop :=
  ∀ x, dom x → ∃ (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (σ' : _root_.ThreeSum1960614.Machine.Light.State) (c : ℕ),
    _root_.ThreeSum1960614.Machine.Light.ProgramSolvesAt prob P p0 dec s k x (T x) lim σ' c



/-! ## The word size -/

/-- A number that depends on the compiled program only: times the polynomial bound on the limits,
it exceeds all four numbers that have to fit in a word (`Fits`). -/
def textBound (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : ℕ := 32 + 8 * (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P + 1) + 2 * _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec

/-- The number of binary digits of that number. -/
def textBoundBits (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : ℕ := Nat.size (_root_.ThreeSum1960614.Machine.Light.textBound P dec)

/-- The slope of the word size for a compiled program: the exponents s and k of the bound
2^s ((p₁ + 1) ⋯ (p_r + 1))^k on the limits, and the bits for the numbers that the compiled code
itself forms (offsets in a frame, positions in the code). -/
def slopeOf (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) (s k r : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.Light.textBoundBits P dec + s + k * r + k





/-! ## Time and space -/

/-- The constant of the time and space bounds of a compiled program: the two constants of the time,
and the extent of the negative cells that are in use before any call. -/
def timeConst (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : ℕ :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.startCost P dec + _root_.Light.Compiler.stepsPerStep (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) + _root_.ThreeSum1960614.Machine.Light.Compiler.lowCell P dec ⟨0, 0, 0⟩











/-! ## Runs from the initial memory -/

section run

variable {W : ℕ} {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ}





end run

/-! ## Solvers -/



/-! ## The two-stage data structure -/

/-- From every memory with the property DS, procedure pQ, called on I and J, returns the entry
(I, J) of the product within T steps and leaves a memory with the property DS. -/
def AnswersQueries (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (P : _root_.ThreeSum1960614.Machine.Light.Program) (pQ : ℕ) (x : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.ThinPair) (T : ℝ)
    (DS : (ℕ → ℤ) → Prop) : Prop :=
  ∀ μ, DS μ → ∀ I J : Fin x.N, ∃ (σ' : _root_.ThreeSum1960614.Machine.Light.State) (c : ℕ),
    _root_.ThreeSum1960614.Machine.Light.Exec lim P 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt pQ) ⟨_root_.Light.frame [0, (I : ℕ), (J : ℕ)], μ⟩ σ' c ∧ (c : ℝ) ≤ T ∧
    σ'.loc 0 = (x.X * x.Y) I J ∧ DS σ'.mem



/-- What is asked of the two procedures on the instance x, with the limits lim and the property DS
of memories, "holds the data structure for X and Y". -/
structure ProgramIsDataStructureAt (P : _root_.ThreeSum1960614.Machine.Light.Program) (pPre pQ : ℕ) (s k : ℕ) (extra : List ℤ)
    (x : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.ThinPair) (Tp Sp Tq : ℝ) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (DS : (ℕ → ℤ) → Prop) : Prop where
  /-- The limits are polynomial in N and D. -/
  small : _root_.ThreeSum1960614.Machine.Light.Small s k [x.N, x.D] lim
  /-- The indices of rows and columns fit in a word. -/
  index_fits : (x.N : ℤ) ≤ lim.word
  /-- The numbers of the input fit in a word. -/
  input_fits : ∀ v ∈ x.input extra, |v| ≤ lim.word
  time_nonneg : 0 ≤ Tq
  /-- The space bounds the addresses after the input. -/
  space : (lim.space : ℝ) ≤ (x.input extra).length + Sp
  /-- The space bounds the nesting of calls. -/
  depth : (lim.depth : ℝ) ≤ Sp
  /-- The preprocessing, on the memory that holds the input, establishes DS. -/
  pre : ∃ (σ' : _root_.ThreeSum1960614.Machine.Light.State) (c : ℕ),
    _root_.ThreeSum1960614.Machine.Light.Exec lim P 0 (_root_.ThreeSum1960614.Machine.Light.mainStmt pPre) ⟨_root_.Light.frame [0, 0, 0], _root_.Light.memOf (x.input extra)⟩ σ' c ∧
    (c : ℝ) ≤ Tp ∧ DS σ'.mem
  /-- Every query needs and keeps DS. -/
  query : _root_.ThreeSum1960614.Machine.Light.AnswersQueries lim P pQ x Tq DS









/-! ## Absorbing the additive constant -/







end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

namespace Light
open _root_.Light


open _root_.ThreeSumApsp.Spec
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Spec

/-! ## The problems for Section 3.4 -/















/-- A list of `N` numbers in the memory. -/
structure VecInst : Type where
  N : ℕ
  U : ℕ
  a : ℕ
  X : List ℤ

/-- The list lies below the free pointer, and its entries are bounded by `U`. -/
structure VecInst.Pre (x : _root_.ThreeSum1960614.Machine.Light.VecInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  U_pos : 1 ≤ x.U
  len : x.X.length = x.N
  seg : _root_.ThreeSum1960614.Machine.Light.Seg μ x.a x.X
  le : _root_.ThreeSum1960614.Machine.ThreeSumApsp.AbsLe x.X x.U
  below : x.a + x.N ≤ fr



/-- **3SUM**: s3(n, U, x, fr) returns 1 if three of the numbers, at different positions, sum to 0,
and 0 if not. -/
noncomputable def s3Task : _root_.Light.Task where
  Inst := _root_.ThreeSum1960614.Machine.Light.VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := _root_.ThreeSum1960614.Machine.Light.VecInst.Pre
  Post x μ fr r μ' := r = _root_.ThreeSumApsp.flag (_root_.ThreeSumApsp.ThreeSum (_root_.ThreeSumApsp.Spec.vecOf x.N x.X)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' fr













/-! ## The thin matrix product and the lopsided triangle problems -/





/-! The ten arguments of a procedure for one of these tasks, as local variables. -/

namespace ThinArg
open _root_.Light.ThinArg













end ThinArg

















end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced
open _root_.ThreeSum.BlockForced


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
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding

section FiniteRows

variable {J L : ℕ}























end FiniteRows

def outputRows {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) : Fin J → Finset (Fin (464 * h)) :=
  fun i => (q i).2.val

def completedTuples {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :=
  univ.filter fun t => _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q ∧ ∀ i ∈ I, (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1 = u i

def residual {h J : ℕ} (I : Finset (Fin J)) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :=
  _root_.ThreeSum.BlockRows.join Iᶜ fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1







def admissibleResiduals {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) : Finset (Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h))) :=
  (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)).powerset.filter fun x =>
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ x) ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q)
      (_root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ x))







section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



/-- The stored suffix stages evaluated by the signed subset query. -/
def transformPrefixValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h))) : ℤ :=
  _root_.ThreeSum.Subset.mobius (fun z =>
    _root_.ThreeSum.Subset.partialZeta (_root_.ThreeSum.BlockForced.suffixDomain I)
      (fun S => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b S : ℤ)) (_root_.ThreeSum.BlockForced.prefixLeft I u ∪ z) *
    _root_.ThreeSum.Subset.partialZeta (_root_.ThreeSum.BlockForced.suffixDomain I)
      (fun V => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c V : ℤ))
      (_root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u ∪ z))
    (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q))



end WeightedCounts

end ThreeSum.BlockForced

end ThreeSum1960614.Machine


