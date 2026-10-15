-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle006
-- name    : ThreeSum1960614_Machine_Bundle006
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:14:40.752444+00:00
-- url     : https://prove2.me/theorems/47e76e3c-cf12-45e4-a3e3-a6af07f44f28
-- title:
--   Block execution, original-index incidences, and whole-program compilation
-- statement:
--   This library defines the interfaces that connect finite combinatorial counts to executable programs. For a light-language statement $s$, state $\sigma$, and resource limits $L$, it defines the resulting block state, block cost, block safety, and the assertion that a safe block establishes a postcondition. It also supplies counting-loop syntax, expression-value assertions, array passes, and structural rules for sequencing, branches, assignments, and stores.
--
--   For nonnegative block parameters $h,J$, integer modulus $P$, balancing offset $d$, finite original-index sets, and integer-valued input maps $a,b,c$, the library retains both original indices and complete representation choices. Its raw mass is the cardinality of these incidences; left and right bucket sizes count indices with the required residue conditions, so equal input values retain their multiplicity. The operational exponent is the maximum of the twelve entries of the fixed cost ledger:
--   $$\rho=\max\bigl(\{0\}\cup\operatorname{costLedger}(E,\kappa,H(\theta_0))\bigr).$$
--   For a finite procedure list $P_0$, entry procedure $p_0$, and decision flag $\delta$, whole-program compilation concatenates initialization, the outermost call and verdict, compiled procedure bodies, a return dispatcher, and startup code. The compiler-test specification records the selected successor address, a step bound, and preservation of all nonscratch cells.
--
--   These definitions preserve the finite counting data and precise execution costs used by the deterministic integer 3SUM runtime proof. They adapt the attributed light-language and word-RAM infrastructure from the pinned source project; the library itself does not assert a new runtime theorem.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Rules.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/BinomialEntropy.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/RawCostExponent.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/RawIncidences.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/Conditions.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/ProgramCode.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Frames.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Pass.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
namespace Real
end Real
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BinomialEntropy
end ThreeSum.BinomialEntropy
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BinomialEntropy
end ThreeSum1960614.Machine.ThreeSum.BinomialEntropy
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/

instance Cond.decidableHolds (σ : _root_.ThreeSum1960614.Machine.Light.State) : (c : _root_.ThreeSum1960614.Machine.Light.Cond) → Decidable (c.Holds σ)
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b => inferInstanceAs (Decidable (a.val σ < b.val σ))
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b => inferInstanceAs (Decidable (a.val σ = b.val σ))

/-- The state after a block (σ itself for a loop or a call, which are not blocks). -/
@[simp] def Stmt.after : _root_.ThreeSum1960614.Machine.Light.Stmt → _root_.ThreeSum1960614.Machine.Light.State → _root_.ThreeSum1960614.Machine.Light.State
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set x e, σ => { σ with loc := Function.update σ.loc x (e.val σ) }
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e, σ => { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t, σ => t.after (s.after σ)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t, σ => if c.Holds σ then s.after σ else t.after σ
  | _, σ => σ

/-- A bound on the number of steps of a block: the longer side of each branch counts (0 for a loop
or a call). -/
@[simp] def Stmt.blockCost : _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set _ e => e.cost + 1
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e => a.cost + e.cost + 1
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t => s.blockCost + t.blockCost
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t => c.cost + 1 + max s.blockCost t.blockCost
  | _ => 0

/-- The statement is a block, and its run from σ stays within the limits. -/
@[simp] def Stmt.BlockSafe (lim : _root_.ThreeSum1960614.Machine.Light.Limits) : _root_.ThreeSum1960614.Machine.Light.Stmt → _root_.ThreeSum1960614.Machine.Light.State → Prop
  | _root_.ThreeSum1960614.Machine.Light.Stmt.skip, _ => True
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set _ e, σ => e.Safe lim σ
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e, σ => a.Safe lim σ ∧ e.Safe lim σ ∧ lim.Addr (a.val σ)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t, σ => s.BlockSafe lim σ ∧ t.BlockSafe lim (s.after σ)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t, σ =>
    c.Safe lim σ ∧ (c.Holds σ → s.BlockSafe lim σ) ∧ (¬ c.Holds σ → t.BlockSafe lim σ)
  | _, _ => False

/-- The block s, started in σ, stays within the limits and ends in a state that satisfies R. -/
abbrev Stmt.Runs (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (σ : _root_.ThreeSum1960614.Machine.Light.State) (R : _root_.ThreeSum1960614.Machine.Light.State → Prop) : Prop :=
  s.BlockSafe lim σ ∧ R (s.after σ)

/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/

/-- The first statement gets T₁ steps, the rest of the program what is left of T. -/
theorem Ends.next {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T₁ : ℕ)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T₁ fun σ' => _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by (first
                        | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                            first
                            | omega
                            | (ring_nf; omega))
                        | omega
                        |
                          (simp [] <;>
                              first
                              | omega
                              | (ring_nf; omega)))) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂)) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.seq T₁ (T - T₁) h (by omega)

/-- Brackets do not matter: a piece of several statements, followed by the rest of the program, is
run statement by statement. -/
theorem Ends.seqAssoc {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {s₁ s₂ s₃ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₂ s₃))) σ T Q) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂) s₃)) σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂₃ =>
    cases he₂₃ with
    | seq he₂ he₃ => exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.seq (_root_.ThreeSum1960614.Machine.Light.Exec.seq he₁ he₂) he₃, by omega, hq⟩

/-- A `skip` before the rest of the program takes no step. -/
theorem Ends.skipThen {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq _root_.ThreeSum1960614.Machine.Light.Stmt.skip s)) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.seq 0 T (_root_.ThreeSum1960614.Machine.Light.Ends.skip h) (by omega)

/-- A `skip` may be put behind a statement. -/
theorem Ends.skipLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s _root_.ThreeSum1960614.Machine.Light.Stmt.skip)) σ T Q) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q := by
  obtain ⟨σ', _, he, hc, hq⟩ := h
  cases he with
  | seq he₁ he₂ =>
    cases he₂
    exact ⟨σ', _, he₁, by omega, hq⟩

/-- A program that is defined as a sequence may be treated as the sequence. -/
theorem Ends.seqSelf {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂)) σ T Q) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂)) σ T Q :=
  h

/-- A piece of the program about which `h` is known, followed by the rest of the program, which gets
the steps that are left. -/
theorem Ends.pieceThen {σ : _root_.ThreeSum1960614.Machine.Light.State} {T T₁ : ℕ} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {R Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T₁ R) (rest : ∀ σ', R σ' → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ' (T - T₁) Q)
    (hT : T₁ ≤ T := by (first
                        | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                            first
                            | omega
                            | (ring_nf; omega))
                        | omega
                        |
                          (simp [] <;>
                              first
                              | omega
                              | (ring_nf; omega)))) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂)) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.next T₁ (h.mono le_rfl rest) hT

/-- A piece of the program about which `h` is known, at the end of the program. -/
theorem Ends.pieceLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T T₁ : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {R Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T₁ R) (rest : ∀ σ', R σ' → Q σ') (hT : T₁ ≤ T := by (first
                                                                                                                    | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                                                        first
                                                                                                                        | omega
                                                                                                                        | (ring_nf; omega))
                                                                                                                    | omega
                                                                                                                    |
                                                                                                                      (simp [] <;>
                                                                                                                          first
                                                                                                                          | omega
                                                                                                                          | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q :=
  h.mono hT rest











/-- A branch, followed by the rest of the program: each side, with the rest of the program behind
it, gets the steps that the test leaves. -/
theorem Ends.iteThen {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ s : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by (first
                                                                     | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) s)) σ T Q := by
  by_cases hc : c.Holds σ
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₁ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, _root_.ThreeSum1960614.Machine.Light.Exec.seq (_root_.ThreeSum1960614.Machine.Light.Exec.iteTrue hs hc he₁) he₂, by omega, hq⟩
  · obtain ⟨σ'', _, he, hk, hq⟩ := h₂ hc
    cases he with
    | seq he₁ he₂ => exact ⟨σ'', _, _root_.ThreeSum1960614.Machine.Light.Exec.seq (_root_.ThreeSum1960614.Machine.Light.Exec.iteFalse hs hc he₁) he₂, by omega, hq⟩

/-- A branch, followed by the rest of the program, where the test says `p`: the first side is run
under the hypothesis `p`, the second under `¬ p`. -/
theorem Ends.iteIffThen {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ s : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (p : Prop) (h₁ : p → _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s)) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ p → _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₂ s)) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                  (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                  simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : c.cost + 1 ≤ T := by (first
                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                    first
                                    | omega
                                    | (ring_nf; omega))
                                | omega
                                |
                                  (simp [] <;>
                                      first
                                      | omega
                                      | (ring_nf; omega)))) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) s)) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT

/-! ## Loops whose body is a block -/



/-! ## Counting loops -/

/-- for i = 0, …, hi - 1 do body. -/
abbrev Stmt.for (i : ℕ) (hi : _root_.ThreeSum1960614.Machine.Light.Expr) (body : _root_.ThreeSum1960614.Machine.Light.Stmt) : _root_.ThreeSum1960614.Machine.Light.Stmt :=
  (_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set i (_root_.ThreeSum1960614.Machine.Light.k 0)) (_root_.ThreeSum1960614.Machine.Light.Stmt.while (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v i) hi) (_root_.ThreeSum1960614.Machine.Light.Stmt.seq body (_root_.ThreeSum1960614.Machine.Light.Stmt.set i ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v i) (_root_.ThreeSum1960614.Machine.Light.k 1))))))





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A finite entropy certificate for every binomial coefficient

The proof uses the mode of the exact binomial expansion with integral weights `k`
and `n-k`. It does not invoke Stirling's formula or introduce an asymptotic assumption.
-/

noncomputable section

namespace ThreeSum.BinomialEntropy
open _root_.ThreeSum.BinomialEntropy


open _root_.Finset
open _root_.Real
open _root_.Set
open _root_.Filter
open scoped _root_.Topology

set_option maxRecDepth 10000



































/-- The actual local output count has exponent `2 E` relative to `D=2^mu`. -/
theorem output_table_rate :
    Tendsto (fun m : ℕ => Real.log ((232 * m).choose m : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E)) := by
  have h := _root_.ThreeSum.BinomialEntropy.fixed_ratio_bits_tendsto (c := 232) (r := 1) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E] <;> ring





end ThreeSum.BinomialEntropy

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
The actual finite maximum of the twelve operational charges. Using this
exponent in the complete runtime assembly retains every strict target
above the maximum, including targets below the convenient principal cap.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters


def rawCostExponent : ℝ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.costLedger _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.kappa (_root_.ThreeSum.Parameters.entropy _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.initialTheta)).foldr max 0

















end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences
open _root_.ThreeSum.RawIncidences


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds









abbrev ChoiceTuple (h J : ℕ) := Fin J → _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h

instance retainedChoiceDecidableEq (h : ℕ) : DecidableEq (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) := inferInstance

instance choiceTupleDecidableEq (h J : ℕ) : DecidableEq (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :=
  Fintype.decidablePiFintype

def tupleLeft {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : ℤ :=
  _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft (List.ofFn t)

def tupleRight {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : ℤ :=
  _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight (List.ofFn t)

def tupleOutput {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J :=
  fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockOfChoice (t i)

def tupleKey {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : ℤ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t)













def tupleOfList {h J : ℕ} (xs : List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) (hlen : xs.length = J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J := fun i => xs.get (Fin.cast hlen.symm i)







abbrev Witness (h J : ℕ) := _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J × Fin 3

instance witnessDecidableEq (h J : ℕ) : DecidableEq (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J) := inferInstance

/-- Retained representations of a fixed original triple. The C target is
shifted by the common balancing offset, and the A key uses the same shift. -/
def witnesses (h J : ℕ) (P d a b c : ℤ) : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J) :=
  Finset.univ.filter fun w : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J =>
    List.ofFn w.1 ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.representations h J (b % P) (c % P + d) ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ (a % P + _root_.ThreeSum.RawIncidences.lift w.2 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleKey w.1

















section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





abbrev RawItem (h J : ℕ) (α β γ : Type*) := Σ _t : _root_.ThreeSum.RawIncidences.Original α β γ, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.Witness h J

/-- The band is a finite set of original index triples. It is part of the
owner data, rather than an additional representation choice. -/
def rawOn (h J : ℕ) (P d : ℤ) (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ) :=
  T.sigma fun t => _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)













def rawMass (h J : ℕ) (P d : ℤ) (T : Finset (_root_.ThreeSum.RawIncidences.Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : ℕ := (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d T a b c).card



/-- Bucket multiplicity counts original B indices, including indices that
carry equal values. Only the left representation is inspected. -/
def leftBucket {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : ℕ :=
  ∑ j ∈ B, if _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b j % P - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t then 1 else 0

/-- The right bucket uses the same common offset as the A query keys. -/
def rightBucket {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : ℕ :=
  ∑ j ∈ C, if _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c j % P + d - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t then 1 else 0



















end OriginalIndices

end ThreeSum.RawIncidences

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {code rest : List _root_.EndStatement.Instr} {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos l : ℕ}
  {m : ℤ → BitVec W} {a b : _root_.ThreeSum1960614.Machine.Light.Expr}

/-! ## Two expressions -/





/-! ## Tests -/

/-- What the code of a test does, if it has size instructions, begins at pos, and tests p: in at
most size steps the machine reaches the position after the code if p holds, and the position l if
not.  Only scratch cells change. -/
def Decides (code : List _root_.EndStatement.Instr) (F pos size l : ℕ) (m : ℤ → BitVec W) (p : Prop) : Prop :=
  ∃ (m' : ℤ → BitVec W) (n : ℕ), n ≤ size ∧ _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.Light.Compiler.Scratch F) m m' ∧
    (p → _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code n ⟨pos, m⟩ ⟨pos + size, m'⟩) ∧ (¬ p → _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps code n ⟨pos, m⟩ ⟨l, m'⟩)













end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The number read off the text -/

/-- The number of local variables of every frame: the width of the text, and at least 3 for the
outermost frame. -/
def frameSize (P : _root_.ThreeSum1960614.Machine.Light.Program) : ℕ := max 3 (_root_.Light.maxOf _root_.ThreeSum1960614.Machine.Light.Stmt.width P)





/-! ## The parts of the code -/

/-- The outermost statement: procedure p0 is called on the local variables 1 and 2 of the outermost
frame, and its result goes to local variable 0. -/
def _root_.ThreeSum1960614.Machine.Light.mainStmt (p0 : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.call p0 [_root_.ThreeSum1960614.Machine.Light.Expr.var 1, _root_.ThreeSum1960614.Machine.Light.Expr.var 2] 0





/-- The position of the code that follows the outermost statement. -/
def tailPos (F : ℕ) : ℕ := _root_.Light.Compiler.mainPos + (_root_.ThreeSum1960614.Machine.Light.mainStmt 0).size F

/-- The position of the first body: after the outermost statement and what follows it. -/
def firstBody (F : ℕ) (dec : Bool) : ℕ := _root_.ThreeSum1960614.Machine.Light.Compiler.tailPos F + (_root_.Light.Compiler.tailCode dec 0).length

/-- The positions of the bodies, the first of them at pos.  A body is followed by the return
sequence. -/
def entries (F : ℕ) : List _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ → List ℕ
  | [], _ => []
  | b :: bs, pos => pos :: entries F bs (pos + b.size F + _root_.Light.Compiler.epilogueSize)

/-- The position after the bodies, the first of them at pos. -/
def endPos (F : ℕ) : List _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ → ℕ
  | [], pos => pos
  | b :: bs, pos => endPos F bs (pos + b.size F + _root_.Light.Compiler.epilogueSize)

/-- The position after the last body, which is the position of the dispatcher.  It is also the
largest number in the pool. -/
def dispPos (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : ℕ := _root_.ThreeSum1960614.Machine.Light.Compiler.endPos (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) P (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec)

/-- What the code of the statements of P needs to know about the whole code. -/
def codeLayout (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : _root_.Light.Compiler.CodeLayout :=
  ⟨_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P, _root_.ThreeSum1960614.Machine.Light.Compiler.entries (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) P (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec), _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec⟩

/-- The bodies with their return sequences, the first of them at pos. -/
def bodiesCode (G : _root_.Light.Compiler.CodeLayout) : List _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ → List _root_.EndStatement.Instr
  | [], _ => []
  | b :: bs, pos =>
    (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt G b pos ++ _root_.Light.Compiler.epilogue G) ++ bodiesCode G bs (pos + b.size G.F + _root_.Light.Compiler.epilogueSize)











/-- The first part: the numbers 1, 0, -1, and the jump to the start-up code. -/
def headCode (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : List _root_.EndStatement.Instr :=
  _root_.Light.Compiler.headStraight ++ [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG (3 * _root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec)]

/-- The second part: the outermost statement and the verdict. -/
def mainCode (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool) : List _root_.EndStatement.Instr :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) (_root_.ThreeSum1960614.Machine.Light.mainStmt p0) _root_.Light.Compiler.mainPos ++ _root_.Light.Compiler.tailCode dec (_root_.ThreeSum1960614.Machine.Light.Compiler.tailPos (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P))

/-- The last part: the start-up code and the jump back to the outermost statement. -/
def startCode (P : _root_.ThreeSum1960614.Machine.Light.Program) (dec : Bool) : List _root_.EndStatement.Instr :=
  _root_.Light.Compiler.startStraight (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) ++ [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG _root_.Light.Compiler.mainPos]

/-- **The code of a program.**  With dec = false the machine accepts at the end of the run; with
dec = true it accepts if the result of procedure p0 is positive and rejects if not. -/
def _root_.ThreeSum1960614.Machine.Light.compileProgram (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool) : List _root_.EndStatement.Instr :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.headCode P dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.mainCode P p0 dec ++ _root_.ThreeSum1960614.Machine.Light.Compiler.bodiesCode (_root_.ThreeSum1960614.Machine.Light.Compiler.codeLayout P dec) P
      (_root_.ThreeSum1960614.Machine.Light.Compiler.firstBody (_root_.ThreeSum1960614.Machine.Light.Compiler.frameSize P) dec) ++
    _root_.Light.Compiler.dispatcher (_root_.ThreeSum1960614.Machine.Light.Compiler.dispPos P dec) ++ _root_.ThreeSum1960614.Machine.Light.Compiler.startCode P dec

/-! ## Lengths and positions -/













section parts

variable (P : _root_.ThreeSum1960614.Machine.Light.Program) (p0 : ℕ) (dec : Bool)





















end parts



end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/



/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    _root_.Light.frame (_root_.Light.setLocal l x z) y = if y = x then z else _root_.Light.frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (_root_.Light.frame l) x z = _root_.Light.frame (_root_.Light.setLocal l x z) := by
  funext y
  rw [_root_.ThreeSum1960614.Machine.Light.frame_setLocal, Function.update_apply]



/-! ## The value of an expression -/

/-- The evaluation of e in σ stays within the limits and gives z. -/
@[simp] def Expr.Gives (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (σ : _root_.ThreeSum1960614.Machine.Light.State) (e : _root_.ThreeSum1960614.Machine.Light.Expr) (z : ℤ) : Prop :=
  e.Safe lim σ ∧ e.val σ = z

/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}





/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} (z : ℤ) (h : Q ⟨_root_.Light.frame (_root_.Light.setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨_root_.Light.frame l, μ⟩ z := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by (first
                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                    first
                                    | omega
                                    | (ring_nf; omega))
                                | omega
                                |
                                  (simp [] <;>
                                      first
                                      | omega
                                      | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) ⟨_root_.Light.frame l, μ⟩ T Q := by
  refine _root_.ThreeSum1960614.Machine.Light.Ends.set he.1 hT ?_
  rw [he.2]
  simp only [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} (z : ℤ)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s ⟨_root_.Light.frame (_root_.Light.setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨_root_.Light.frame l, μ⟩ z := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : e.cost + 1 ≤ T := by (first
                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                    first
                                    | omega
                                    | (ring_nf; omega))
                                | omega
                                |
                                  (simp [] <;>
                                      first
                                      | omega
                                      | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) s)) ⟨_root_.Light.frame l, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.next _ (_root_.ThreeSum1960614.Machine.Light.Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : _root_.ThreeSum1960614.Machine.Light.Expr} (b : ℕ) (z : ℤ) (h : Q ⟨_root_.Light.frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨_root_.Light.frame l, μ⟩ b ∧ e.Gives lim ⟨_root_.Light.frame l, μ⟩ z ∧ b < lim.space := by
      (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by (first
                                         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                             first
                                             | omega
                                             | (ring_nf; omega))
                                         | omega
                                         |
                                           (simp [] <;>
                                               first
                                               | omega
                                               | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) ⟨_root_.Light.frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine _root_.ThreeSum1960614.Machine.Light.Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : _root_.ThreeSum1960614.Machine.Light.Expr} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} (b : ℕ) (z : ℤ)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s ⟨_root_.Light.frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨_root_.Light.frame l, μ⟩ b ∧ e.Gives lim ⟨_root_.Light.frame l, μ⟩ z ∧ b < lim.space := by
      (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by (first
                                         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                             first
                                             | omega
                                             | (ring_nf; omega))
                                         | omega
                                         |
                                           (simp [] <;>
                                               first
                                               | omega
                                               | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) s)) ⟨_root_.Light.frame l, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.next _ (_root_.ThreeSum1960614.Machine.Light.Ends.storeTo b z h he le_rfl) hT





end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-- for c < len: dst[c] := e.  The local c is the counter. -/
abbrev pass (c : ℕ) (len dst e : _root_.ThreeSum1960614.Machine.Light.Expr) : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.for c len (_root_.ThreeSum1960614.Machine.Light.Stmt.store (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) dst (_root_.ThreeSum1960614.Machine.Light.v c))) e)

variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}







end Light

end

end ThreeSum1960614.Machine


