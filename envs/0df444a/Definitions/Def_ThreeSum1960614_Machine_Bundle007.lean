-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle007
-- name    : ThreeSum1960614_Machine_Bundle007
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:17:52.210761+00:00
-- url     : https://prove2.me/theorems/44545981-cb1a-440a-bf60-046241c34335
-- title:
--   Reporting prefixes, procedure specifications, and compiler simulation states
-- statement:
--   This library packages the state and counting interfaces for reporting and machine simulation. A row-major rectangular memory representation records an array's entries by their row and column positions. A wanted reporting query fixes an original $A$ index, a signed lift, and a global output. For finite original-index sets $A,B,C$, integer input maps $a,b,c$, modulus $P$, offset $d$, prefix length $k$, and prescribed list $u$, its bucket-prefix mass is zero unless the fixed $A$ key is compatible; otherwise it is
--   $$\sum_{t\in\operatorname{completions}(q,k,u)}\operatorname{leftBucket}(P,B,b,t)\operatorname{rightBucket}(P,d,C,c,t).$$
--   Here $q$ is the wanted global output and the completion set contains precisely the choice tuples with output $q$ and prefix $u$.
--
--   The procedure assertion $\operatorname{Meets}(L,P_0,p,d,v,\mu,T,R)$ states that procedure $p$ of program $P_0$, begun at depth $d$ with argument list $v$ and memory $\mu$, finishes within $T$ light steps and satisfies the result-and-memory relation $R$. Compiler simulation records a fixed setting, a framed starting state, and a finished word-RAM run; the latter bounds machine steps by the per-step simulation factor and records the memory relation and unchanged cells. Relocation shifts every procedure call by a common offset and composes a verified library with a prelude. Integer scale definitions specify replicated schedule counts, representation bounds, output counts, and trimmed-bucket multiplicities from the actual finite schedules and bucket caps.
--
--   Together these interfaces connect exact reporting counts, modular procedure reasoning, and concrete word-RAM execution in the deterministic integer 3SUM proof. Their source attribution and dependencies are retained from the pinned project.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/RowMajor.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/RawReporting.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/Scales.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Calls.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/Simulation.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/RawPrefixCounts.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/ReportingHostRelocation.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/TrimScales.lean

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
import Definitions.Def_ThreeSum1962Source_Bundle01
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
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
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
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.TrimScales
end ThreeSum1960614.Machine.ThreeSum.TrimScales
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
# Reading the trusted layout

Matrices are written row by row (`rowMajor`), and an input is a concatenation of lists.  This file
says which number is in which cell (`getD_rowMajor`, `seg_memOf`, `matAt_of_seg`).
-/

public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp
open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam















/-- A part of a concatenation is a segment of the memory. -/
theorem seg_memOf (l₁ l l₂ : List ℤ) : _root_.ThreeSum1960614.Machine.Light.Seg (_root_.Light.memOf (l₁ ++ l ++ l₂)) l₁.length l := by
  intro i hi
  rw [List.append_assoc, _root_.Light.memOf_append_right, _root_.Light.memOf_append_left _ hi]
  exact List.getD_eq_getElem _ _ hi









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Positive-prefix reporting for concrete guarded incidences

The band triple is fixed by the input index sets and offset passed to this
module. Its wanted queries retain the original A index, signed lift and
full output tuple, including every chosen-map occurrence. Children are
the balanced subsets of the next output block, in deterministic colex order.
-/

namespace ThreeSum.RawReporting
open _root_.ThreeSum.RawReporting


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

section

 def private_b1d266245d_colexEmbedding (L : ℕ) : Finset (Fin L) ↪ Colex (Finset (Fin L)) :=
  ⟨toColex, fun _ _ h => h⟩
end


/-- A deterministic ordering of exactly the balanced child subsets. -/
def childList {L : ℕ} (Q : Finset (Fin L)) (h : ℕ) : List (Finset (Fin L)) :=
  (((Q.powersetCard h).map (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.private_b1d266245d_colexEmbedding L)).sort (· ≤ ·)).map ofColex







def children {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ) : List (Finset (Fin (464 * h))) :=
  if hk : k < J then _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.childList (q ⟨k, hk⟩).2.val h else []





def partitionWord {h J : ℕ} (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) : List (Finset (Fin (464 * h))) :=
  List.ofFn fun i => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge (t i)).val.1



instance outputBlockDecidableEq (h : ℕ) : DecidableEq (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h) := inferInstance
instance globalOutputDecidableEq (h J : ℕ) : DecidableEq (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) :=
  Fintype.decidablePiFintype

abbrev Wanted (h J : ℕ) (α : Type*) := α × (Fin 3 × _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)

instance wantedDecidableEq (h J : ℕ) (α : Type*) [DecidableEq α] :
    DecidableEq (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) := inferInstance

def wantedOf {h J : ℕ} {α β γ : Type*} (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ) : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α :=
  (r.1.1, (r.2.2, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput r.2.1))

def word {h J : ℕ} {α β γ : Type*} (r : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ) := _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord r.2.1

section FixedBand

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def domain {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α) :=
  I.filter fun r => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.wantedOf r = w

def prefixQuery {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (464 * h)))) : ℕ :=
  _root_.ThreeSum.Reporting.mass (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w) _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word (fun _ => 1) k pre

















end FixedBand

end ThreeSum.RawReporting

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology





def blockCount (m : ℕ) : ℕ := 20 * (203889696 * m / (20000000000 * _root_.ThreeSum.Scales.microSize m))

def totalSize (m : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m * _root_.ThreeSum.Scales.microSize m



def mu (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n)

def typedOutputs (n : ℕ) : ℕ :=
  ((232 * _root_.ThreeSum.Scales.muZero n).choose (_root_.ThreeSum.Scales.muZero n)) ^ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)















def localRadix (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n))

def radix (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n ^ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)



def scoreLoss (k n : ℕ) : ℕ :=
  (16 * (k + 2) * (_root_.ThreeSum.Scales.inputBits n + 1)) ^ _root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n

















noncomputable section















theorem totalSize_ratio_tendsto :
    Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m : ℝ) / m) atTop (𝓝 _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount,_root_.ThreeSum.Scales.microSize,_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon,
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize,_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.blockCount,
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize,_root_.ThreeSum1960614.epsilon] using
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.executable_scale_limits.2.1







theorem mu_log_ratio_tendsto :
    Tendsto (fun n : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2)) := by
  have h := (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_ratio_tendsto.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).mul
    _root_.ThreeSum.Scales.inputBits_log_ratio_tendsto
  have hlim : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / Real.log 2) = _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2 := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [_root_.ThreeSum.Scales.inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (_root_.ThreeSum.Scales.inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu]
  field_simp

















































theorem even_output_rate :
    Tendsto (fun h : ℕ => Real.log (_root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E)) := by
  have ht : Tendsto (fun h : ℕ => 2 * h) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with h hh
    omega
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.BinomialEntropy.output_table_rate.comp ht
  convert hr using 1
  funext h
  simp only [Function.comp_def, _root_.ThreeSum.LocalCoverBounds.outputCount, Nat.cast_mul, Nat.cast_ofNat]
  rw [show 232 * (2 * h) = 464 * h by omega]

theorem localThreshold_log_formula (h : ℕ) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) =
      Real.log (_root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h : ℝ) +
        (2 * h : ℝ) * Real.log 2 := by
  have hM : (0 : ℝ) < _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 * h ≤ 464 * h))
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt hM) (by positivity), Real.log_pow]
  simp

theorem localThreshold_log_rate :
    Tendsto (fun h : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1)) := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.even_output_rate.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  have hpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localThreshold_log_formula]
  field_simp

theorem localPrime_log_interval (h : ℕ) :
    Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) ≤
      2 * Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℝ) ∧
    2 * Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℝ) ≤
      Real.log 16 + Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) := by
  have hN : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold_pos h
  have hp : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h
  have hl : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℝ) ^ 2 := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_lower h
  have hu : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℝ) ^ 2 ≤
      16 * (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_sq_upper h
  constructor
  · simpa [Real.log_pow] using Real.log_le_log hN hl
  · simpa [Real.log_pow, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hN.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (LocalCoverBounds.localPrime h : ℝ) ^ 2) hu

theorem localPrime_log_rate :
    Tendsto (fun h : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2)) := by
  have hmain := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localThreshold_log_rate.div_const 2
  have hmain' : Tendsto (fun h : ℕ =>
      Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) / ((2 * h : ℝ) * Real.log 2) / 2)
      atTop (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2)) := by
    convert hmain using 1 <;> ring
  have herr : Tendsto (fun h : ℕ => Real.log 16 / ((4 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 16 / (4 * Real.log 2))
  have hupper := hmain'.add herr
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain' hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localPrime_log_interval h).1
    apply (le_div_iff₀ hden).mpr
    have heq : (Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2) * ((2 * h : ℝ) * Real.log 2) =
        Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) / 2 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localPrime_log_interval h).2
    apply (div_le_iff₀ hden).mpr
    have heq : (Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2 + Real.log 16 / ((4 * h : ℝ) * Real.log 2)) *
        ((2 * h : ℝ) * Real.log 2) =
        (Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localThreshold h : ℝ) + Real.log 16) / 2 := by field_simp; ring
    rw [heq]
    linarith

theorem radix_log_ratio_tendsto :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ) / Real.log n) atTop
      (𝓝 (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2))) := by
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localPrime_log_rate.comp (_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) * (Real.log 2 * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon / Real.log 2)) =
      _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(_root_.ThreeSum.Scales.microHalf_tendsto_atTop.comp _root_.ThreeSum.Scales.inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) at hn
  have hn0 : (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix, Nat.cast_pow, Real.log_pow, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix]
  have hmu : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℝ) = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℝ) *
      (2 * _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize, _root_.ThreeSum.Scales.microSize, _root_.ThreeSum.Scales.microHalf]
  rw [hmu]
  field_simp

theorem radix_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix
  exact Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos _)

theorem radix_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℝ)) atTop atTop := by
  have hpositive : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E + 1 / 2) := by
    have h := _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E_bounds.1
    exact mul_pos _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon_positive (by linarith)
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_ratio_tendsto.pos_mul_atTop hpositive
    _root_.ThreeSum.Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem radix_eventually_ge_four : ∀ᶠ n : ℕ in atTop, 4 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by
  filter_upwards [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_log_tendsto_atTop.eventually (eventually_ge_atTop (Real.log 4))] with n hn
  have hr : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := by exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n
  have h : (4 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := (Real.log_le_log_iff (by norm_num) hr).mp hn
  exact_mod_cast h













































end

end ThreeSum.Scales

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/

/-- Procedure number p of the program P, run at depth d on the arguments vals in the memory μ, ends
within T steps with a result r and a memory μ' that satisfy R r μ'. -/
def Meets (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (P : _root_.ThreeSum1960614.Machine.Light.Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ)
    (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem

section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}











end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}

/-- `x := p(args)`, where the arguments give vals.  The procedure runs at depth d + 1. -/
theorem Ends.callLast (hp : _root_.ThreeSum1960614.Machine.Light.Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨Function.update loc x r, μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                                                        (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                                                        simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + T' ≤ T := by (first
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
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) ⟨loc, μ⟩ T Q := by
  obtain ⟨body, hb, he⟩ := hp
  obtain ⟨hs, rfl⟩ := ha
  exact _root_.ThreeSum1960614.Machine.Light.Ends.call T' hs hb hd (he.mono le_rfl fun _ hR => h _ _ hR) hT



/-- `x := p(args)`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callTo (hp : _root_.ThreeSum1960614.Machine.Light.Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → Q ⟨_root_.Light.frame (_root_.Light.setLocal l x r), μ'⟩)
    (ha : (∀ e ∈ args, e.Safe lim ⟨_root_.Light.frame l, μ⟩) ∧ args.map (·.val ⟨_root_.Light.frame l, μ⟩) = vals := by
      (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + T' ≤ T := by (first
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
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) ⟨_root_.Light.frame l, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.callLast hp (fun r μ' hR => _root_.ThreeSum1960614.Machine.Light.update_frame_setLocal l x r ▸ h r μ' hR) ha hd hT

/-- `x := p(args) ; s`, with the local variables as a list.  The procedure runs at depth d + 1. -/
theorem Ends.callToThen (hp : _root_.ThreeSum1960614.Machine.Light.Meets lim P p (d + 1) vals μ T' R)
    (h : ∀ r μ', R r μ' → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s ⟨_root_.Light.frame (_root_.Light.setLocal l x r), μ'⟩
      (T - ((args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + T')) Q)
    (ha : (∀ e ∈ args, e.Safe lim ⟨_root_.Light.frame l, μ⟩) ∧ args.map (·.val ⟨_root_.Light.frame l, μ⟩) = vals := by
      (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hd : d < lim.depth := by omega)
    (hT : (args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + T' ≤ T := by (first
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
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d ((_root_.ThreeSum1960614.Machine.Light.Stmt.seq (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) s)) ⟨_root_.Light.frame l, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.next _ (_root_.ThreeSum1960614.Machine.Light.Ends.callTo hp h ha hd le_rfl) hT

end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## Where the parts of the code of a statement are -/

section layout

variable {code : List _root_.EndStatement.Instr} {G : _root_.Light.Compiler.CodeLayout} {pos x p : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s t : _root_.ThreeSum1960614.Machine.Light.Stmt}
  {args : List _root_.ThreeSum1960614.Machine.Light.Expr}











end layout

/-! ## The setting -/

/-- What the simulation assumes once and for all: the numbers are large enough (`Sizes`), and the
program and its code fit them. -/
structure Setting (W : ℕ) extends _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W where
  /-- The light program. -/
  P : _root_.ThreeSum1960614.Machine.Light.Program
  /-- The code of the whole program. -/
  code : List _root_.EndStatement.Instr
  /-- Every procedure body is at its entry, followed by the return sequence, all before the
  dispatcher. -/
  bodyAt : ∀ (p : ℕ) (b : _root_.ThreeSum1960614.Machine.Light.Stmt), P[p]? = some b → ∃ e, entry[p]? = some e ∧
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code e (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt toCodeLayout b e ++ _root_.Light.Compiler.epilogue toCodeLayout) ∧
    e + b.size F + _root_.Light.Compiler.epilogueSize ≤ disp
  /-- The dispatcher serves the positions before it. -/
  dispatcherAt : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt code disp (_root_.Light.Compiler.dispatcher disp)
  /-- Every body has width at most F. -/
  width : ∀ b ∈ P, b.width ≤ F









variable {W : ℕ} (S : _root_.ThreeSum1960614.Machine.Light.Compiler.Setting W)

/-- The situation before the code of the statement s runs, at nesting depth d of calls: the memory m
represents the state σ in the frame q, and the following holds. -/
structure Start (d : ℕ) (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (σ : _root_.ThreeSum1960614.Machine.Light.State) (pos q : ℕ) (m : ℤ → BitVec W) : Prop
    extends _root_.ThreeSum1960614.Machine.Light.Compiler.Framed S.toSizes σ q m where
  /-- The code of s is at pos. -/
  codeAt : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.CodeAt S.code pos (_root_.ThreeSum1960614.Machine.Light.Compiler.compileStmt S.toCodeLayout s pos)
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
structure Finished (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (σ' : _root_.ThreeSum1960614.Machine.Light.State) (c pos q : ℕ) (m m' : ℤ → BitVec W) (n : ℕ) : Prop where
  /-- The machine has reached the position after the code. -/
  run : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Steps S.code n ⟨pos, m⟩ ⟨pos + s.size S.F, m'⟩
  /-- It took at most stepsPerStep machine steps for each step of the language. -/
  le : n ≤ _root_.Light.Compiler.stepsPerStep S.disp * c
  /-- The memory represents σ' in the same frame. -/
  rel : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel S.toSizes σ' q m'
  /-- Only cells that a statement in the frame q may write have changed. -/
  agree : _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.AgreeOutside (_root_.ThreeSum1960614.Machine.Light.Compiler.Writable S.toSizes q) m m'

/-- The code of s matches the run of s from σ to σ' in c steps. -/
def Simulates (d : ℕ) (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (σ σ' : _root_.ThreeSum1960614.Machine.Light.State) (c : ℕ) : Prop :=
  ∀ (pos q : ℕ) (m : ℤ → BitVec W), _root_.ThreeSum1960614.Machine.Light.Compiler.Start S d s σ pos q m →
    ∃ (m' : ℤ → BitVec W) (n : ℕ), _root_.ThreeSum1960614.Machine.Light.Compiler.Finished S s σ' c pos q m m' n

variable {S} {d pos q : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' σ₁ σ₂ : _root_.ThreeSum1960614.Machine.Light.State} {m : ℤ → BitVec W}







/-! ## Statements without calls -/

















/-! ## Calls -/

section call

variable {p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr}







end call

/-! ## The theorem -/



end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bucket products at a wanted reporting prefix

The raw fiber used by the reporting theorem is here expanded into independently
counted B and C buckets. The wanted query fixes its original A index, lift,
and all chosen-map occurrences and output subsets.
-/

namespace ThreeSum.RawPrefixCounts
open _root_.ThreeSum.RawPrefixCounts


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def prefixItems {h J : ℕ} (I : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.RawItem h J α β γ)) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (464 * h)))) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.domain I w).filter fun r => (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.word r).take k = pre



def compatiblePairs {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :=
  (B ×ˢ C).filter fun p => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ b p.1 % P - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleLeft t ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣ c p.2 % P + d - _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleRight t

def completions {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (464 * h)))) : Finset (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.ChoiceTuple h J) :=
  Finset.univ.filter fun t => _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.tupleOutput t = q ∧ (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord t).take k = pre









/-- The query first checks the fixed A key. Its remaining natural mass is
exactly a sum of products of the original-index B and C bucket sizes. -/
def bucketPrefixMass {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (464 * h)))) : ℕ :=
  if w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % P + _root_.ThreeSum.RawIncidences.lift w.2.1 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2 then
    ∑ t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions w.2.2 k pre, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket P B b t * _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket P d C c t
  else 0



end Indices

end ThreeSum.RawPrefixCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation
open _root_.ThreeSum.ReportingHostRelocation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

@[simp] def relocate (offset : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt → _root_.ThreeSum1960614.Machine.Light.Stmt
  | _root_.ThreeSum1960614.Machine.Light.Stmt.skip => _root_.ThreeSum1960614.Machine.Light.Stmt.skip
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set x e => _root_.ThreeSum1960614.Machine.Light.Stmt.set x e
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e => _root_.ThreeSum1960614.Machine.Light.Stmt.store a e
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t => _root_.ThreeSum1960614.Machine.Light.Stmt.seq (relocate offset s) (relocate offset t)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t => _root_.ThreeSum1960614.Machine.Light.Stmt.ite c (relocate offset s) (relocate offset t)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.while c s => _root_.ThreeSum1960614.Machine.Light.Stmt.while c (relocate offset s)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.call p args x => _root_.ThreeSum1960614.Machine.Light.Stmt.call (offset+p) args x

def program (prefixProgram P : _root_.ThreeSum1960614.Machine.Light.Program) : _root_.ThreeSum1960614.Machine.Light.Program := prefixProgram ++ P.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length)









end ThreeSum.ReportingHostRelocation

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales
open _root_.ThreeSum.TrimScales


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open scoped _root_.Topology

def replicatedHalf (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  f (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) ^ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)



def trimMultiplicity (n : ℕ) : ℕ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) ^ (2 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n))

def localLength (h : ℕ) : ℕ := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h).length

def scheduleCount (n : ℕ) : ℕ := _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.replicatedHalf _root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength n

def representationBound (n : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.TrimScales.localLength (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) *
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) ^ 2) ^ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)

def fullOutputs (n : ℕ) : ℕ := (232 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n).choose (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)



noncomputable section

def vertexLoad (h : ℕ) : ℝ :=
  (_root_.ThreeSum.LocalCoverBounds.vertexCount (464 * h) h : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h























































end

end ThreeSum.TrimScales

end ThreeSum1960614.Machine


