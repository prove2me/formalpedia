-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle005
-- name    : ThreeSum1960614_Machine_Bundle005
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:09:47.740995+00:00
-- url     : https://prove2.me/theorems/e715abdb-4311-48ca-838b-6b2c30c471bc
-- title:
--   Global radix encoding, exact cost parameters, and compiler memory relations
-- statement:
--   This bundle defines the concrete global encoding and the memory invariants used by the compiled deterministic integer 3SUM algorithm. For a local scale $h\in\mathbb N$, a retained choice records both an occurrence of a hash map in the deterministic local schedule and a disjoint-subset edge whose two hash buckets satisfy the prescribed cap. Keeping the occurrence preserves multiplicity even when maps repeat. Raw hashes sum canonical integer representatives before reduction modulo the selected prime $p_h$. For a depth $J\in\mathbb N$, the global modulus and representation cap are
--   $$M_{h,J}=p_h^J,\qquad R_{h,J}=(s_h b_h^2)^J,$$
--   where $s_h$ is the schedule length and $b_h$ is the local bucket cap. Output records retain the map occurrence and the union of the endpoint subsets; their global keys are positional radix hashes of the resulting integer contributions.
--
--   The analytic interface fixes the expansion-$232$ entropy quantities, the rational quartic switching function, and the exact rational constants $\varepsilon$, band shift, box saving, initial threshold, terminal fraction, and entropy ratio. Its twelve-entry cost ledger keeps each operational exponent separately. The bundle also includes the executable scale limits: if $u_m$, $s_m$, $a_m$, and $D_m$ denote the microblock size, total size, band exponent, and band divisor, respectively, then
--   $$\frac{u_m^2}{m}\to0,\quad \frac{s_m}{m}\to\varepsilon,\quad \frac{a_m}{m}\to(-\beta)\varepsilon,\quad \frac{\log D_m}{m}\to(\log2)(-\beta)\varepsilon$$
--   as the natural input scale $m$ tends to infinity, with $\beta$ the fixed band-shift parameter.
--
--   For word size $W\in\mathbb N$, the compiler's size data package its code layout, execution limits, stack capacity, and explicit word-fit inequalities. The relation between a Light state and a word-RAM memory specifies the constant cells, number pool, frame pointer, local-variable cells, and simulated nonnegative memory cells. A framed relation additionally requires the current frame to lie inside the stack. The writable-region predicate and arithmetic descriptions of temporary, stack, and pool cells support preservation under writes. Finally, a segment predicate states that a finite integer list occupies consecutive memory cells; its natural-number version uses integer casts.
--
--   These definitions connect finite radix representations and the exact analytic ledger to the concrete memory layout needed for compiler simulation and the complete runtime proof.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/Closed3Sum/executable_scale_limits.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/GlobalEncoding.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/Parameters.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Lib/Seg.lean

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Tactic
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
namespace Set
end Set
namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum1960614
end ThreeSum1960614
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
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.Schedule
end ThreeSum1960614.Machine.ThreeSum1960614.Schedule
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.WordRam
end ThreeSum1960614.Machine.ThreeSumApsp.WordRam
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.WordRam
end ThreeSumApsp.WordRam

namespace ThreeSum1960614.Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule
open _root_.Filter
open scoped _root_.Topology

/- The microblock estimates use the even cube-root construction inherited
   from the pinned upstream Scales.lean. The block and band limits concern
   the new exact integer schedule, rather than the upstream 1/5 schedule. -/

section

 theorem private_8ab924f33c_micro_rounding (m : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m ≤ Nat.nthRoot 3 m ∧ Nat.nthRoot 3 m < _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m + 2 := by
  have h := Nat.mod_add_div (Nat.nthRoot 3 m) 2
  have hr := Nat.mod_lt (Nat.nthRoot 3 m) (by decide : 0 < 2)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize
  omega
end


section

 theorem private_5f345a7c34_micro_atTop : Tendsto _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) ^ 3)] with m hm
  have hr : b + 2 ≤ Nat.nthRoot 3 m :=
    (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hm
  have hround := (_root_.ThreeSum1960614.Machine.private_8ab924f33c_micro_rounding m).2
  omega
end


section

 theorem private_e44790a5d9_square_ratio :
    Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) := by
  have hcast : Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp _root_.ThreeSum1960614.Machine.private_5f345a7c34_micro_atTop
  apply squeeze_zero' _ _ hcast.inv_tendsto_atTop
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [_root_.ThreeSum1960614.Machine.private_5f345a7c34_micro_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hx : (0 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m := by exact_mod_cast (by omega : 0 < microSize m)
    have hc : _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m ^ 3 ≤ m :=
      (Nat.pow_le_pow_left (_root_.ThreeSum1960614.Machine.private_8ab924f33c_micro_rounding m).1 3).trans
        (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))
    have hcube : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ) ^ 3 ≤ (m : ℝ) := by exact_mod_cast hc
    have hmp : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hcube
    apply (div_le_iff₀ hmp).mpr
    simp only [Pi.inv_apply]
    rw [mul_comm ((_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ)⁻¹) (m : ℝ)]
    change (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ) ^ 2 ≤ (m : ℝ) / _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m
    apply (le_div_iff₀ hx).mpr
    nlinarith only [hcube]
end


section

 theorem private_6118bf9636_micro_ratio :
    Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ) / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ _root_.ThreeSum1960614.Machine.private_e44790a5d9_square_ratio
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [_root_.ThreeSum1960614.Machine.private_5f345a7c34_micro_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hmr : (1 : ℝ) ≤ _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg m)
end


theorem ThreeSum1960614.executable_scale_limits :
    Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) / m) atTop (𝓝 _root_.ThreeSum1960614.epsilon) ∧
    Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m : ℝ) / m) atTop (𝓝 ((-_root_.ThreeSum1960614.beta) * _root_.ThreeSum1960614.epsilon)) ∧
    Tendsto (fun m : ℕ => Real.log (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandDivisor m : ℝ) / m) atTop
      (𝓝 (Real.log 2 * ((-_root_.ThreeSum1960614.beta) * _root_.ThreeSum1960614.epsilon))) := by
  have htotal : Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) / m) atTop (𝓝 _root_.ThreeSum1960614.epsilon) := by
    have hlo : Tendsto (fun m : ℕ => _root_.ThreeSum1960614.epsilon - 20 * ((_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m : ℝ) / m))
        atTop (𝓝 _root_.ThreeSum1960614.epsilon) := by
      simpa using tendsto_const_nhds.sub (_root_.ThreeSum1960614.Machine.private_6118bf9636_micro_ratio.const_mul 20)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [_root_.ThreeSum1960614.Machine.private_5f345a7c34_micro_atTop.eventually (eventually_ge_atTop 1),
        eventually_ge_atTop (1 : ℕ)] with m hm hmpos
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hl := ((_root_.ThreeSum1960614.Machine.ThreeSum1960614.executable_scale_rounding m).2.2.1 (by omega)).2.le
      apply (le_div_iff₀ hmp).mpr
      calc
        _ = _root_.ThreeSum1960614.epsilon * (m : ℝ) - 20 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m := by field_simp
        _ ≤ _ := by linarith
    · filter_upwards [_root_.ThreeSum1960614.Machine.private_5f345a7c34_micro_atTop.eventually (eventually_ge_atTop 1),
        eventually_ge_atTop (1 : ℕ)] with m hm hmpos
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      apply (div_le_iff₀ hmp).mpr
      have hu := ((_root_.ThreeSum1960614.Machine.ThreeSum1960614.executable_scale_rounding m).2.2.1 (by omega)).1
      linarith
  have hband : Tendsto (fun m : ℕ => (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m : ℝ) / m) atTop
      (𝓝 ((-_root_.ThreeSum1960614.beta) * _root_.ThreeSum1960614.epsilon)) := by
    have hid : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    have hup := htotal.const_mul (-_root_.ThreeSum1960614.beta)
    have hlo : Tendsto (fun m : ℕ => (-_root_.ThreeSum1960614.beta) * ((_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) / m) - 1 / m)
        atTop (𝓝 ((-_root_.ThreeSum1960614.beta) * _root_.ThreeSum1960614.epsilon)) := by
      simpa only [one_div, sub_zero] using hup.sub hid
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      apply (le_div_iff₀ hmp).mpr
      have hl := (_root_.ThreeSum1960614.Machine.ThreeSum1960614.executable_scale_rounding m).2.2.2.2.1
      calc
        _ = (-_root_.ThreeSum1960614.beta) * (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) - 1 := by field_simp
        _ ≤ _ := by linarith
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
      have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      apply (div_le_iff₀ hmp).mpr
      have hu := (_root_.ThreeSum1960614.Machine.ThreeSum1960614.executable_scale_rounding m).2.2.2.1
      calc
        _ ≤ (-_root_.ThreeSum1960614.beta) * (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) := by linarith
        _ = _ := by field_simp
  refine ⟨_root_.ThreeSum1960614.Machine.private_e44790a5d9_square_ratio, htotal, hband, ?_⟩
  convert hband.const_mul (Real.log 2) using 1
  ext m
  rw [_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandDivisor, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments

def scheduleSize (h : ℕ) : ℕ := _root_.ThreeSum.LocalHashMoments.scheduleLength h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)

theorem scheduleSize_eq_length (h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h = (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h).length := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule_length]
  rfl

abbrev Occurrence (h : ℕ) := Fin (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)

def mapAt (h : ℕ) (i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) : _root_.ThreeSum.LocalHashMoments.Weight (464 * h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h).get (Fin.cast (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize_eq_length h) i)





def Survives (h : ℕ) (i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (e : _root_.ThreeSum.LocalGraph.Edge (464 * h) h) : Prop :=
  _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.leftVertices (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i)
      (_root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i) (_root_.ThreeSum.LocalGraph.left e)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ∧
    _root_.ThreeSum.HashFamily.bucketSize (_root_.ThreeSum.LocalGraph.rightVertices (464 * h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i)
      (_root_.ThreeSum.HashFamily.hashValue (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h i) (_root_.ThreeSum.LocalGraph.right e)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h

instance instDecidableSurvives (h : ℕ) (i : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (e : _root_.ThreeSum.LocalGraph.Edge (464 * h) h) :
    Decidable (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h i e) := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives; infer_instance

/-- A choice includes its schedule occurrence as well as its retained edge. -/
abbrev RetainedChoice (h : ℕ) :=
  {p : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h × _root_.ThreeSum.LocalGraph.Edge (464 * h) h // _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Survives h p.1 p.2}

def occurrence {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h := c.val.1
def edge {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) : _root_.ThreeSum.LocalGraph.Edge (464 * h) h := c.val.2



/-- Sum of the canonical integer representatives of the selected symbol
weights. This is the raw integer sum before reduction modulo the prime. -/
def rawHash {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (s : Fin L → Bool) : ℤ :=
  ∑ i, ((w (i, s i)).val : ℤ)









def rawLeft {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) : ℤ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum.LocalGraph.left (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c))

def rawRight {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) : ℤ :=
  _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c)) (_root_.ThreeSum.LocalGraph.right (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c))









def representations (h J : ℕ) (a b : ℤ) : Finset (List (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h)) :=
  _root_.ThreeSum.Radix.representations (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawLeft _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawRight J a b

def globalModulus (h J : ℕ) : ℤ := (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) ^ J

def representationCap (h J : ℕ) : ℕ :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h ^ 2) ^ J









/-- The integer difference contribution is determined by the equality
positions alone. Positions in the output subset contribute zero. -/
def rawOutput {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (Q : Finset (Fin L)) : ℤ :=
  ∑ i, if i ∈ Q then 0 else ((w (i, true)).val : ℤ) - ((w (i, false)).val : ℤ)



/-- An output record retains the chosen-map occurrence and the union of the
two disjoint endpoint subsets. It forgets the internal partition. -/
abbrev OutputBlock (h : ℕ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h × {Q // Q ∈ _root_.ThreeSum.LayerCounts.vertices (464 * h) (2 * h)}

def blockOfChoice {h : ℕ} (c : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.RetainedChoice h) : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.occurrence c, ⟨_root_.ThreeSum.LocalGraph.output (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c), _root_.ThreeSum.LayerCounts.mem_vertices.mpr (_root_.ThreeSum.LocalGraph.output_card (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.edge c))⟩)

def blockKey {h : ℕ} (b : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h) : ℤ := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h b.1) b.2.val





abbrev GlobalOutput (h J : ℕ) := Fin J → _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.OutputBlock h



def globalKey {h J : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) : ℤ :=
  _root_.ThreeSum.Radix.positionalHash (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (List.ofFn q)













end ThreeSum.GlobalEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
Expansion-232 analytic interface for the actual machine-source modules.
The definition bodies use the audited rational quartic parameter choice.
Closed analytic proofs supply the bounds; no program correctness contract
is assumed by this interface. Additional operational exponents must remain
the individual raw ledger costs for the universal rational-r bridge.
-/

noncomputable section
namespace ThreeSum.Parameters
open _root_.ThreeSum.Parameters

open _root_.Set


def E : ℝ := 116 * _root_.ThreeSum.Parameters.entropy (1 / 232)
def kappa : ℝ := 464 * _root_.ThreeSum.Parameters.entropy (1 / 464) - 232 * _root_.ThreeSum.Parameters.entropy (1 / 232) - 1
def gamma (t : ℝ) : ℝ := 232 * _root_.ThreeSum.Parameters.entropy (1 / 232) - 232 * _root_.ThreeSum.Parameters.entropy ((1-t)/232)
def phi (t : ℝ) : ℝ :=
  (785174904*t+72447023*t^2+24044466*t^3+12022459*t^4)/100000000
def phiDeriv (t : ℝ) : ℝ :=
  (785174904+2*72447023*t+3*24044466*t^2+4*12022459*t^3)/100000000
def epsilon : ℝ := 203889696/1000000000
def bandShift : ℝ := -(62656016/1000000000)
def boxSaving : ℝ := 193175570/1000000000
def initialTheta : ℝ := 40409899/1000000000
def terminalFraction : ℝ := 13/20
def entropyRatio : ℝ := 2790503/10000000









theorem E_bounds : (4 : ℝ) < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E ∧ _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E < 19/4 := by
  obtain ⟨hl,hu,_,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum1960614.encoding_parameter_bounds
  have he : _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E = _root_.ThreeSum1960614.E 232 := by
    norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.E,_root_.ThreeSum.Parameters.entropy,_root_.ThreeSum1960614.E,_root_.ThreeSum1960614.entropy]
  rw [he]
  constructor <;> linarith

theorem epsilon_positive : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon := by norm_num [_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon]





/-- Every operational charge is retained for the arbitrary-target runtime bridge. -/
def costLedger (e k h : ℝ) : List ℝ :=
  [2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * e,
   1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (e - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift),
   2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving,
   2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - h),
   2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - k - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.entropyRatio * (1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift)),
   2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.terminalFraction - 1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift - k),
   _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (8 / 5) * (e + 1 / 2),
   2 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (4 / 5 - (2 / 5) * e - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift),
   1 + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (1 / 2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift),
   2 - _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (e + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift),
   2 - 2 * _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.epsilon * (e + _root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift),
   1]



























def switchThreshold (a : ℝ) : ℝ := (_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.boxSaving-2*_root_.ThreeSum1960614.Machine.ThreeSum.Parameters.bandShift+a)/(1-a)







end ThreeSum.Parameters

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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

open _root_.ThreeSumApsp.WordRam
open _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## The numbers that never change -/

/-- The word size is large enough for the limits: words hold 2 · word + 2 (so the difference of two
values, and one less, is in range), all addresses of the memory, all addresses of a stack of Q
cells, and all numbers 0, …, N of the pool. -/
structure Fits (W : ℕ) (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (N Q : ℕ) : Prop where
  word : 2 * (2 * lim.word + 2) < (2 : ℤ) ^ W
  space : 2 * (lim.space : ℤ) < (2 : ℤ) ^ W
  stack : 2 * (2 * (Q : ℤ)) < (2 : ℤ) ^ W
  pool_lt : 2 * (N : ℤ) < (2 : ℤ) ^ W



/-- The numbers on which the proofs about compiled code depend: the layout of the code, the limits
on the runs of the light program, and the number of stack cells.  The pool holds the numbers from 0
to the position of the dispatcher. -/
structure Sizes (W : ℕ) extends _root_.Light.Compiler.CodeLayout where
  /-- The limits on the runs of the light program. -/
  lim : _root_.ThreeSum1960614.Machine.Light.Limits
  /-- The number of stack cells. -/
  Q : ℕ
  /-- The word size fits the limits, the pool and the stack. -/
  fits : _root_.ThreeSum1960614.Machine.Light.Compiler.Fits W lim disp Q
  /-- The pool holds the numbers up to 2 (F + 1), which are the offsets in a frame. -/
  offsets_le : 2 * (F + 1) ≤ disp

/-! ## Sets of cells -/













/-- What the code of a statement that runs in the frame q may change: scratch cells, FP, the stack
cells from q on, and the memory cells within the limits. -/
def Writable {W : ℕ} (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) (q : ℕ) : Set ℤ :=
  _root_.Light.Compiler.Scratch Z.F ∪ {_root_.Light.Compiler.cFP} ∪ _root_.Light.Compiler.Stack q Z.Q ∪ {a | 0 ≤ a ∧ a < Z.lim.space}

/-! The temporaries, the stack and the pool are arithmetic progressions of cells. -/

theorem mem_temps_iff {k F : ℕ} {a : ℤ} :
    a ∈ _root_.Light.Compiler.Temps k F ↔ a = _root_.Light.Compiler.cADDR ∨ _root_.Light.Compiler.cT (2 * F) ≤ a ∧ a ≤ _root_.Light.Compiler.cT k ∧ 4 ∣ _root_.Light.Compiler.cT 0 - a := by
  simp only [_root_.Light.Compiler.Temps, _root_.Light.Compiler.cT, Set.mem_ofPred_eq]
  refine or_congr_right ⟨?_, fun h => ⟨((-23 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨j, hk, hj, rfl⟩
    omega
  · omega

theorem mem_stack_iff {q Q : ℕ} {a : ℤ} :
    a ∈ _root_.Light.Compiler.Stack q Q ↔ _root_.Light.Compiler.cStack Q < a ∧ a ≤ _root_.Light.Compiler.cStack q ∧ 2 ∣ a := by
  simp only [_root_.Light.Compiler.Stack, _root_.Light.Compiler.cStack, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨(-a / 2).toNat, ?_⟩⟩
  · rintro ⟨j, hq, hj, rfl⟩
    omega
  · omega

theorem mem_pool_iff {N : ℕ} {a : ℤ} :
    a ∈ _root_.Light.Compiler.Pool N ↔ _root_.Light.Compiler.cPool N ≤ a ∧ a ≤ _root_.Light.Compiler.cPool 0 ∧ 4 ∣ _root_.Light.Compiler.cPool 0 - a := by
  simp only [_root_.Light.Compiler.Pool, _root_.Light.Compiler.cPool, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨((-25 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨n, hn, rfl⟩
    omega
  · omega







variable {W : ℕ} {Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W} {F : ℕ}











/-! ## Addresses, and numbers that fit in a word -/













/-! ## The relation between a state of the light language and a memory of the machine -/

/-- The memory m of the machine represents the state σ of a procedure whose frame is at q. -/
structure Rel (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) (σ : _root_.ThreeSum1960614.Machine.Light.State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  one : m _root_.Light.Compiler.cONE = _root_.ThreeSumApsp.WordRam.wd W 1
  zero : m _root_.Light.Compiler.cZERO = _root_.ThreeSumApsp.WordRam.wd W 0
  neg : m _root_.Light.Compiler.cNEG = _root_.ThreeSumApsp.WordRam.wd W (-1)
  pool : ∀ n ≤ Z.disp, m (_root_.Light.Compiler.cPool n) = _root_.ThreeSumApsp.WordRam.wd W n
  fp : m _root_.Light.Compiler.cFP = _root_.ThreeSumApsp.WordRam.wd W (_root_.Light.Compiler.cStack q)
  loc : ∀ x < Z.F, m (_root_.Light.Compiler.cStack (q + x)) = _root_.ThreeSumApsp.WordRam.wd W (σ.loc x)
  mem : ∀ a < Z.lim.space, m (a : ℤ) = _root_.ThreeSumApsp.WordRam.wd W (σ.mem a)

section Rel

variable {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {q q' : ℕ} {m m' : ℤ → BitVec W}















end Rel

/-- The memory m represents the state σ in the frame q, and the frame lies within the stack: after
stack cell 0 and before stack cell Q. -/
structure Framed (Z : _root_.ThreeSum1960614.Machine.Light.Compiler.Sizes W) (σ : _root_.ThreeSum1960614.Machine.Light.State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  rel : _root_.ThreeSum1960614.Machine.Light.Compiler.Rel Z σ q m
  low : 1 ≤ q
  high : q + Z.F ≤ Z.Q

/-! ## Two pieces of code that occur everywhere -/

section code

variable {σ : _root_.ThreeSum1960614.Machine.Light.State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List _root_.EndStatement.Instr}







end code

end Light.Compiler

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]



variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

















































/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := _root_.ThreeSum1960614.Machine.Light.Seg μ a (l.map fun x : ℕ => (x : ℤ))





























end Light

end

end ThreeSum1960614.Machine


