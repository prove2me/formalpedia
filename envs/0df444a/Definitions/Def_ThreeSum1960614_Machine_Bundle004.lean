-- Prove2me | Definitions.Def_ThreeSum1960614_Machine_Bundle004
-- name    : ThreeSum1960614_Machine_Bundle004
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:08:32.326203+00:00
-- url     : https://prove2.me/theorems/8543a38e-f733-492e-88cf-82e47af6857b
-- title:
--   Exact parameter bounds, local schedules, and the Light compiler interface
-- statement:
--   This bundle joins the exact expansion-$232$ parameter interface to the semantics and compiler of the Light intermediate language. It includes certified rational intervals for the encoding quantities $E(232)$ and $\kappa(232)$, and the integer rounding facts for the executable schedule. For an input scale $m\in\mathbb N$, the microblock size is even, the block count is divisible by $20$, the total size has a nonnegative rounding deficit smaller than $20$ microblocks whenever the microblock size is positive, and the band divisor is positive.
--
--   For $h\in\mathbb N$, let $p_h$ be the selected local prime. The local field is $\mathbb Z/p_h\mathbb Z$; the deterministic schedule enumerates one-hot weight assignments on $464h$ coordinates and has length
--   $$320(2h+1)\bigl(\lfloor\log_2(p_h^2)\rfloor+1\bigr).$$
--
--   The compiler definitions give code and exact code-size functions for expressions, conditions, calls, and statements. Their width functions bound local-variable indices, call arities, and temporary requirements. For limits $\ell$, program $P$, call depth $d$, statement $s$, initial state $\sigma$, time allowance $T$, and postcondition $Q$, the predicate $\operatorname{Ends}(\ell,P,d,s,\sigma,T,Q)$ means that an execution ends in a state satisfying $Q$ with cost at most $T$. The bundle supplies basic compositional rules and the standard assumptions that addresses and program constants fit within the word bound.
--
--   For a problem $Q$ and real-valued time function $T(n,U)$, the word-RAM realization interface quantifies over every polynomial input bound $U=n^k$, including size zero, and allows a nonnegative constant-factor bound $c\max(T(n,U),0)+c$. The natural-valued step-bound conversion is
--   $$B_{C,a}(n)=\left\lceil C(n^a+1)\right\rceil_+\qquad(C,a\in\mathbb R,\ n\in\mathbb N).$$
--
--   These interfaces connect the exact rational parameter certificate, finite local schedules, operational Light proofs, and the final deterministic integer 3SUM runtime statement. They retain the pinned source project's compiler and machine conventions.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/Closed3Sum/encoding_parameter_bounds.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/Closed3Sum/executable_scale_rounding.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSum/LocalHashMoments.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Compiler/StatementCode.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Lang/Logic.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Machine/Realized.lean
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Statements/Exponents.lean

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Compiler_StatementCode
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Solving
import Definitions.Def_APSPSource_ThreeSumApsp_Machine_Steps
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic
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

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Compiler
end Light.Compiler
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Compiler
end ThreeSum1960614.Machine.Light.Compiler
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
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

section

 theorem private_f4e6bdc69e_entropy_eq (t : ℝ) :
    _root_.ThreeSum1960614.entropy t = (-t * Real.log t - (1 - t) * Real.log (1 - t)) / Real.log 2 := by
  simp only [_root_.ThreeSum1960614.entropy, Real.binEntropy, Real.log_inv]
  ring
end


section

 theorem private_e58ad4e0c4_scaled_entropy (c : ℝ) (hc : 1 < c) :
    c * _root_.ThreeSum1960614.entropy (1 / c) = (Real.log c + (c - 1) * Real.log (c / (c - 1))) / Real.log 2 := by
  have hcn : c ≠ 0 := by linarith
  have hcm : c - 1 ≠ 0 := by linarith
  have hln : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [_root_.ThreeSum1960614.Machine.private_f4e6bdc69e_entropy_eq]
  rw [show 1 - 1 / c = (c - 1) / c by field_simp <;> ring]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hcn,
      Real.log_div hcm hcn, Real.log_div hcn hcm]
  simp only [Real.log_one]
  field_simp [hcn, hcm, hln]
  <;> ring
end


section

 theorem private_634beb5339_log_232 : Real.log (232 : ℝ) = 7 * Real.log 2 + Real.log (29 / 16) := by
  have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 7
    norm_num at h
    exact h
  rw [show (232 : ℝ) = 128 * (29 / 16) by norm_num,
      Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (by norm_num : (29 / 16 : ℝ) ≠ 0), h128]
end


section

 theorem private_eccbdb9ff4_E_formula :
    _root_.ThreeSum1960614.E 232 = (7 * Real.log 2 + Real.log (29 / 16) + 231 * Real.log (232 / 231)) /
      (2 * Real.log 2) := by
  have h := _root_.ThreeSum1960614.Machine.private_e58ad4e0c4_scaled_entropy (232 : ℝ) (by norm_num)
  norm_num at h
  unfold _root_.ThreeSum1960614.E
  norm_num only [Nat.cast_ofNat]
  calc
    (116 : ℝ) * _root_.ThreeSum1960614.entropy (1 / 232) = (232 * _root_.ThreeSum1960614.entropy (1 / 232)) / 2 := by ring
    _ = (7 * Real.log 2 + Real.log (29 / 16) + 231 * Real.log (232 / 231)) /
        (2 * Real.log 2) := by rw [h, _root_.ThreeSum1960614.Machine.private_634beb5339_log_232]; ring
end


section

 theorem private_6034c2e24f_kappa_formula :
    _root_.ThreeSum1960614.kappa 232 = (463 * Real.log (464 / 463) - 231 * Real.log (232 / 231)) / Real.log 2 := by
  have h232 := _root_.ThreeSum1960614.Machine.private_e58ad4e0c4_scaled_entropy (232 : ℝ) (by norm_num)
  have h464 := _root_.ThreeSum1960614.Machine.private_e58ad4e0c4_scaled_entropy (464 : ℝ) (by norm_num)
  norm_num at h232 h464
  have hlog : Real.log (464 : ℝ) = Real.log 2 + Real.log 232 := by
    rw [show (464 : ℝ) = 2 * 232 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (232 : ℝ) ≠ 0)]
  have hln : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hraw : _root_.ThreeSum1960614.kappa 232 = 464 * _root_.ThreeSum1960614.entropy (1 / 464) - 232 * _root_.ThreeSum1960614.entropy (1 / 232) - 1 := by
    norm_num [_root_.ThreeSum1960614.kappa]
  rw [hraw, h464, h232, hlog]
  field_simp [hln]
  <;> ring
end


theorem ThreeSum1960614.encoding_parameter_bounds :
    4648781151243719 / 1000000000000000 < _root_.ThreeSum1960614.E 232 ∧
    _root_.ThreeSum1960614.E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < _root_.ThreeSum1960614.kappa 232 ∧
    _root_.ThreeSum1960614.kappa 232 < 1557987216579 / 1000000000000000 := by
  obtain ⟨hl, hm, hp, hq, _, _⟩ := _root_.ThreeSum1960614.Machine.ThreeSum1960614.high_precision_logs
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.ThreeSum1960614.Machine.private_eccbdb9ff4_E_formula]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    have hn : (2 * (4648781151243719 / 1000000000000000 : ℝ) - 7) *
        (6931471805599453094173 / 10^22) <
        5947071077466927895143 / 10^22 + 231 * (43196611445164148724 / 10^22) := by norm_num
    nlinarith only [hl.2, hm.1, hp.1, hn]
  · rw [_root_.ThreeSum1960614.Machine.private_eccbdb9ff4_E_formula]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    have hn : (5947071077466927895144 / 10^22 : ℝ) + 231 * (43196611445164148725 / 10^22) <
        (2 * (4648781151243720 / 1000000000000000) - 7) * (6931471805599453094172 / 10^22) := by norm_num
    nlinarith only [hl.1, hm.2, hp.2, hn]
  · rw [_root_.ThreeSum1960614.Machine.private_6034c2e24f_kappa_formula]
    apply (lt_div_iff₀ hln).2
    have hn : (1557987216578 / 1000000000000000 : ℝ) * (6931471805599453094173 / 10^22) <
        463 * (21574981400211907723 / 10^22) - 231 * (43196611445164148725 / 10^22) := by norm_num
    nlinarith only [hl.2, hq.1, hp.2, hn]
  · rw [_root_.ThreeSum1960614.Machine.private_6034c2e24f_kappa_formula]
    apply (div_lt_iff₀ hln).2
    have hn : (463 * (21574981400211907724 / 10^22) - 231 * (43196611445164148724 / 10^22) : ℝ) <
        (1557987216579 / 1000000000000000) * (6931471805599453094172 / 10^22) := by norm_num
    nlinarith only [hl.1, hq.2, hp.1, hn]

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule

theorem ThreeSum1960614.executable_scale_rounding (m : ℕ) :
    2 ∣ _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m ∧ 20 ∣ _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.blockCount m ∧
    (0 < _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m →
      0 ≤ _root_.ThreeSum1960614.epsilon * (m : ℝ) - _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m ∧
      _root_.ThreeSum1960614.epsilon * (m : ℝ) - _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m < 20 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m) ∧
    0 ≤ (-_root_.ThreeSum1960614.beta) * (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) - _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m ∧
    (-_root_.ThreeSum1960614.beta) * (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m : ℝ) - _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m < 1 ∧
    0 < _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandDivisor m := by
  refine ⟨⟨Nat.nthRoot 3 m / 2, rfl⟩,
    ⟨203889696 * m / (20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m), rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro hs
    have hd : 0 < 20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m := by positivity
    have hmod := Nat.mod_lt (203889696 * m) hd
    have hdiv := Nat.mod_add_div (203889696 * m) (20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m)
    have heq : 20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m *
        (203889696 * m / (20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m)) = 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m := by
      dsimp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize, _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.blockCount]
      ring
    rw [heq] at hdiv
    have hlo : 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m ≤ 203889696 * m := by omega
    have hhi : 203889696 * m < 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m + 20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m := by omega
    have hlor : (1000000000 : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m ≤ 203889696 * m := by exact_mod_cast hlo
    have hhir : (203889696 : ℝ) * m < 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m + 20000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.microSize m := by
      exact_mod_cast hhi
    dsimp [_root_.ThreeSum1960614.epsilon]
    constructor <;> linarith
  · have h := Nat.div_mul_le_self (62656016 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m) 1000000000
    have hr : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m : ℝ) * 1000000000 ≤ 62656016 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m := by
      exact_mod_cast h
    dsimp [_root_.ThreeSum1960614.beta]
    linarith
  · have hmod := Nat.mod_lt (62656016 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m) (by decide : 0 < 1000000000)
    have hdiv := Nat.mod_add_div (62656016 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m) 1000000000
    have h : 62656016 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m < 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m + 1000000000 := by
      dsimp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent]
      omega
    have hr : (62656016 : ℝ) * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.totalSize m < 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandExponent m + 1000000000 := by
      exact_mod_cast h
    dsimp [_root_.ThreeSum1960614.beta]
    linarith
  · dsimp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.Schedule.bandDivisor]
    positivity

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalHashMoments


open _root_.Finset
open scoped _root_.BigOperators

open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}















































/-! ## The selected local prime and its actual finite schedule -/

instance localPrimeFact (h : ℕ) : Fact (Nat.Prime (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)) :=
  ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_prime h⟩

abbrev LocalField (h : ℕ) := ZMod (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)

def localValues (h : ℕ) : List (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h) :=
  (List.range (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)).map (fun x : ℕ => (x : _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))



def localSchedule (h : ℕ) : List (_root_.ThreeSum.LocalHashMoments.Weight (464 * h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) :=
  _root_.ThreeSum.LocalHashMoments.schedule (464 * h) h (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localValues h)

theorem localSchedule_length (h : ℕ) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule h).length =
      320 * (2 * h + 1) * (Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ^ 2) + 1) := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localSchedule, _root_.ThreeSum.LocalHashMoments.scheduleLength, ZMod.card] using
    _root_.ThreeSum.LocalHashMoments.schedule_length (L := 464 * h) (h := h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.localValues h)









end ThreeSum.LocalHashMoments

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The compiler from the light language to the word RAM: cells, and the code of statements

This file holds the definitions: the cells, the code of expressions, tests, statements, calls and
returns, the length of each piece of code, and the one condition on the text of a program (its
width).  The code of a whole program, `compileProgram`, puts these pieces together.

**Cells.**  A memory cell a of the light language is the cell a ≥ 0 of the machine.  Everything else
lives in negative cells.  A whole program takes two arguments from the cells -1 and -2 (`cARG1`,
`cARG2`) and puts its result into the cell -3 (`cRESULT`); the cell -4 is not used.  Odd cells from
-5 down hold the registers of the compiled code, the temporaries T₀, T₁, … for the evaluation of
expressions, and a pool of numbers: the cell `cPool n` holds the number n, for all n up to the
largest position to return to.  Even cells hold the call stack: stack cell j is the cell -2 j
(`cStack`).  The outermost frame of a whole program begins at stack cell `mainFrame` = 4, so the
code of its statements writes no stack cell before the cell -8 and leaves the cells -1, …, -4
alone.  The lemmas about pieces of code ask less: only that a frame begins after stack cell 0.

**Numbers.**  The constants of the program text are built from their binary digits where they are
needed.  The numbers that the compiled code itself needs, offsets in a frame and positions to return
to, come from the pool: the length of the code that builds a number from its digits depends on the
number, and a position to return to depends on the lengths.

**Frames.**  With F local variables per procedure, the frame of a running procedure is given by a
number q: local variable x is the cell -2 (q + x), the position to return to is in the
cell -2 (q - 1), and the register FP holds -2 q.  A call moves q to q + F + 1.

**Jumps.**  The machine only has "branch if negative" to a fixed position.  An unconditional jump
tests a register that holds -1.  A return loads the position r to return to into the register RR and
jumps to the dispatcher, the code "RR := RR - 1; if RR < 0 go to j" for j = 0, 1, 2, …, which
arrives at position r after 2 (r + 1) steps: a constant for a fixed program.

**Calls.**  The caller evaluates the arguments into temporaries, computes the address of the new
frame, fills its local variables (arguments first, then zeros), stores the position to return to,
moves FP and jumps to the procedure.  The procedure ends with its return sequence: result into RET,
position into RR, FP back to the caller's frame, jump to the dispatcher.  Back in the caller, RET is
stored into the variable that receives the result.

**Lengths.**  A jump forward needs the length of code that is not yet written, so the lengths are
defined on the text (`Expr.size`, `Cond.size`, `Stmt.size`) and then shown to be the lengths of the
code (`length_compileExpr`, `length_compileCond`, `length_compileStmt`).
-/

@[expose] public section

namespace Light.Compiler
open _root_.Light.Compiler


open _root_.EndStatement renaming Instr -> Instr

/-! ## Cells

The names of the registers are written in capitals, as in the comments on the code. -/


















/-! ## Expressions and tests -/







/-- Code that leaves the value of the expression in the temporary T_k, using only T_k, T_{k+1}, …
and ADDR.  A constant is built from its binary digits, in at most 2 log₂ n + 3 instructions. -/
def compileExpr : _root_.ThreeSum1960614.Machine.Light.Expr → ℕ → List _root_.EndStatement.Instr
  | _root_.ThreeSum1960614.Machine.Light.Expr.const n, k => _root_.Light.Compiler.digitsCode (_root_.Light.Compiler.cT k) (Nat.digits 2 n)
  | _root_.ThreeSum1960614.Machine.Light.Expr.var x, k => [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)), _root_.EndStatement.Instr.load (_root_.Light.Compiler.cT k) _root_.Light.Compiler.cADDR]
  | _root_.ThreeSum1960614.Machine.Light.Expr.op o a b, k => compileExpr a k ++ compileExpr b (k + 1) ++ [o.instr (_root_.Light.Compiler.cT k) (_root_.Light.Compiler.cT k) (_root_.Light.Compiler.cT (k + 1))]
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a, k => compileExpr a k ++ [_root_.EndStatement.Instr.load (_root_.Light.Compiler.cT k) (_root_.Light.Compiler.cT k)]

/-- The length of the code of an expression. -/
def _root_.ThreeSum1960614.Machine.Light.Expr.size : _root_.ThreeSum1960614.Machine.Light.Expr → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Expr.const n => _root_.Light.Compiler.digitsLen (Nat.digits 2 n)
  | _root_.ThreeSum1960614.Machine.Light.Expr.var _ => 2
  | _root_.ThreeSum1960614.Machine.Light.Expr.op _ a b => a.size + b.size + 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a => a.size + 1

/-- Code that goes on to the next position if the test holds and jumps to the position l if it does
not.  Both tests evaluate a into T₀ and b into T₁.  For a < b the code forms D = b - a - 1 and
leaves if D < 0.  For a = b it forms D = a - b and leaves if D < 0, then forms -D and leaves if that
is negative. -/
def compileCond : _root_.ThreeSum1960614.Machine.Light.Cond → ℕ → List _root_.EndStatement.Instr
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b, l =>
    _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr a 0 ++ _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr b 1 ++ [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cD (_root_.Light.Compiler.cT 1) (_root_.Light.Compiler.cT 0), _root_.EndStatement.Instr.sub _root_.Light.Compiler.cD _root_.Light.Compiler.cD _root_.Light.Compiler.cONE, _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cD l]
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b, l =>
    _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr a 0 ++ _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr b 1 ++
      [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cD (_root_.Light.Compiler.cT 0) (_root_.Light.Compiler.cT 1), _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cD l, _root_.EndStatement.Instr.sub _root_.Light.Compiler.cD _root_.Light.Compiler.cZERO _root_.Light.Compiler.cD, _root_.EndStatement.Instr.bltz _root_.Light.Compiler.cD l]

/-- The length of the code of a test. -/
def _root_.ThreeSum1960614.Machine.Light.Cond.size : _root_.ThreeSum1960614.Machine.Light.Cond → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b => a.size + b.size + 3
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b => a.size + b.size + 4

/-! ## Statements -/



/-- The arguments of a call, evaluated into T_k, T_{k+1}, …. -/
def argsCode : List _root_.ThreeSum1960614.Machine.Light.Expr → ℕ → List _root_.EndStatement.Instr
  | [], _ => []
  | e :: es, k => _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e k ++ argsCode es (k + 1)

/-- The length of the code for the arguments of a call. -/
def argsSize : List _root_.ThreeSum1960614.Machine.Light.Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es





/-- A call up to and including the jump to the procedure; ret is the position after the jump. -/
def callCode (G : _root_.Light.Compiler.CodeLayout) (p : ℕ) (args : List _root_.ThreeSum1960614.Machine.Light.Expr) (ret : ℕ) : List _root_.EndStatement.Instr :=
  _root_.ThreeSum1960614.Machine.Light.Compiler.argsCode args 0 ++ _root_.Light.Compiler.newFrame G.F args.length ret ++ [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG (G.entry.getD p 0)]

/-- The length of a call up to and including the jump. -/
def callSize (F : ℕ) (args : List _root_.ThreeSum1960614.Machine.Light.Expr) : ℕ := _root_.ThreeSum1960614.Machine.Light.Compiler.argsSize args + 1 + 2 * F + 4

/-- The length of the code of a statement. -/
def _root_.ThreeSum1960614.Machine.Light.Stmt.size (F : ℕ) : _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Stmt.skip => 0
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set _ e => e.size + 2
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e => a.size + e.size + 1
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t => s.size F + t.size F
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t => c.size + s.size F + 1 + t.size F
  | _root_.ThreeSum1960614.Machine.Light.Stmt.while c s => c.size + s.size F + 1
  | _root_.ThreeSum1960614.Machine.Light.Stmt.call _ args _ => _root_.ThreeSum1960614.Machine.Light.Compiler.callSize F args + 2

/-- The code of a statement, for the position pos. -/
def compileStmt (G : _root_.Light.Compiler.CodeLayout) : _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ → List _root_.EndStatement.Instr
  | _root_.ThreeSum1960614.Machine.Light.Stmt.skip, _ => []
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set x e, _ => _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e 0 ++ [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)), _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR (_root_.Light.Compiler.cT 0)]
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e, _ => _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr a 0 ++ _root_.ThreeSum1960614.Machine.Light.Compiler.compileExpr e 1 ++ [_root_.EndStatement.Instr.store (_root_.Light.Compiler.cT 0) (_root_.Light.Compiler.cT 1)]
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t, pos => compileStmt G s pos ++ compileStmt G t (pos + s.size G.F)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t, pos =>
    _root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ++
      compileStmt G t (pos + c.size + s.size G.F + 1)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.while c s, pos =>
    _root_.ThreeSum1960614.Machine.Light.Compiler.compileCond c (pos + c.size + s.size G.F + 1) ++ compileStmt G s (pos + c.size) ++
      [_root_.EndStatement.Instr.bltz _root_.Light.Compiler.cNEG pos]
  | _root_.ThreeSum1960614.Machine.Light.Stmt.call p args x, pos =>
    _root_.ThreeSum1960614.Machine.Light.Compiler.callCode G p args (pos + _root_.ThreeSum1960614.Machine.Light.Compiler.callSize G.F args) ++
      [_root_.EndStatement.Instr.sub _root_.Light.Compiler.cADDR _root_.Light.Compiler.cFP (_root_.Light.Compiler.cPool (2 * x)), _root_.EndStatement.Instr.store _root_.Light.Compiler.cADDR _root_.Light.Compiler.cRET]







/-! ## Lengths -/



















end Compiler

/-! ## The width of a text

The compiled code gives every frame the same number F of local variables.  That is enough if F is at
least the width of every body: a number that bounds the variables, the arguments of each call, and
the temporaries that each expression needs.  Then 2 F + 1 temporaries are enough too: up to F
arguments of a call wait in temporaries while the last one is evaluated in up to F more.  "The width
is at most F" is taken apart by one lemma for each construct. -/

/-- One more than the largest variable of an expression. -/
def Expr.vars : _root_.ThreeSum1960614.Machine.Light.Expr → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Expr.const _ => 0
  | _root_.ThreeSum1960614.Machine.Light.Expr.var x => x + 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.op _ a b => max a.vars b.vars
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a => a.vars

/-- The number of temporaries that the code of an expression uses. -/
def Expr.height : _root_.ThreeSum1960614.Machine.Light.Expr → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Expr.const _ => 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.var _ => 1
  | _root_.ThreeSum1960614.Machine.Light.Expr.op _ a b => max a.height (b.height + 1)
  | _root_.ThreeSum1960614.Machine.Light.Expr.load a => a.height

/-- The width of an expression: at least its variables and its temporaries. -/
def Expr.width (e : _root_.ThreeSum1960614.Machine.Light.Expr) : ℕ := max e.vars e.height

/-- The width of a test: that of its two sides. -/
def Cond.width : _root_.ThreeSum1960614.Machine.Light.Cond → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Cond.lt a b => max a.width b.width
  | _root_.ThreeSum1960614.Machine.Light.Cond.eq a b => max a.width b.width



/-- The width of a statement: at least the width of its expressions, one more than each variable
that it writes, and the number of arguments of each of its calls. -/
def Stmt.width : _root_.ThreeSum1960614.Machine.Light.Stmt → ℕ
  | _root_.ThreeSum1960614.Machine.Light.Stmt.skip => 0
  | _root_.ThreeSum1960614.Machine.Light.Stmt.set x e => max (x + 1) e.width
  | _root_.ThreeSum1960614.Machine.Light.Stmt.store a e => max a.width e.width
  | _root_.ThreeSum1960614.Machine.Light.Stmt.seq s t => max s.width t.width
  | _root_.ThreeSum1960614.Machine.Light.Stmt.ite c s t => max c.width (max s.width t.width)
  | _root_.ThreeSum1960614.Machine.Light.Stmt.while c s => max c.width s.width
  | _root_.ThreeSum1960614.Machine.Light.Stmt.call _ args x => max (x + 1) (max args.length (_root_.Light.maxOf _root_.ThreeSum1960614.Machine.Light.Expr.width args))

section width

variable {F x p : ℕ} {o : _root_.Light.Op} {a b e : _root_.ThreeSum1960614.Machine.Light.Expr} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s t : _root_.ThreeSum1960614.Machine.Light.Stmt} {args : List _root_.ThreeSum1960614.Machine.Light.Expr}























end width

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/





/-- Procedure number i of a list that is appended to the program P₀ has the number |P₀| + i. -/
theorem getElem?_append_length_add (P₀ : _root_.ThreeSum1960614.Machine.Light.Program) {R : _root_.ThreeSum1960614.Machine.Light.Program} {i : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (h : R[i]? = some body) : (P₀ ++ R)[P₀.length + i]? = some body := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h



/-! ## The rules -/

/-- The statement s, started in σ, ends within T steps in a state that satisfies Q. -/
def Ends (lim : _root_.ThreeSum1960614.Machine.Light.Limits) (P : _root_.ThreeSum1960614.Machine.Light.Program) (d : ℕ) (s : _root_.ThreeSum1960614.Machine.Light.Stmt) (σ : _root_.ThreeSum1960614.Machine.Light.State) (T : ℕ) (Q : _root_.ThreeSum1960614.Machine.Light.State → Prop) :
    Prop :=
  ∃ σ' c, _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'

/-- More time and a weaker conclusion. -/
theorem Ends.mono {s σ T T' Q Q'} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (hT : T ≤ T')
    (hQ : ∀ σ', Q σ' → Q' σ') : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T' Q' := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc.trans hT, hQ _ hq⟩



theorem Ends.skip {σ T} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (h : Q σ) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.Light.Stmt.skip σ T Q :=
  ⟨σ, 0, _root_.ThreeSum1960614.Machine.Light.Exec.skip, Nat.zero_le _, h⟩

theorem Ends.set {σ T x e} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) }) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) σ T Q :=
  ⟨_, _, _root_.ThreeSum1960614.Machine.Light.Exec.set hs, hT, h⟩

theorem Ends.store {σ T a e} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) σ T Q :=
  ⟨_, _, _root_.ThreeSum1960614.Machine.Light.Exec.store ha he hA, hT, h⟩

theorem Ends.seq {σ T s₁ s₂} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T₁ T₂ : ℕ)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T₁ fun σ' => _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ' T₂ Q) (hT : T₁ + T₂ ≤ T) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.seq s₁ s₂) σ T Q := by
  obtain ⟨σ', c₁, he₁, hc₁, σ'', c₂, he₂, hc₂, hq⟩ := h
  exact ⟨σ'', _, _root_.ThreeSum1960614.Machine.Light.Exec.seq he₁ he₂, by omega, hq⟩













/-- Calls: verify the body from the frame made of the arguments. -/
theorem Ends.call {σ T p args x body} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T' : ℕ) (ha : ∀ e ∈ args, e.Safe lim σ)
    (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P (d + 1) body ⟨_root_.Light.frame (args.map (·.val σ)), σ.mem⟩ T'
      fun σ' => Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩)
    (hT : (args.map _root_.ThreeSum1960614.Machine.Light.Expr.cost).sum + 2 + T' ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.call p args x) σ T Q := by
  obtain ⟨σ', k, he, hk, hq⟩ := h
  exact ⟨_, _, _root_.ThreeSum1960614.Machine.Light.Exec.call ha hp hd he, by omega, hq⟩

/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/

/-- Local variable number x. -/
abbrev v (x : ℕ) : _root_.ThreeSum1960614.Machine.Light.Expr := _root_.ThreeSum1960614.Machine.Light.Expr.var x
/-- The constant n. -/
abbrev k (n : ℕ) : _root_.ThreeSum1960614.Machine.Light.Expr := _root_.ThreeSum1960614.Machine.Light.Expr.const n
/-- The memory cell at address a. -/
abbrev M (a : _root_.ThreeSum1960614.Machine.Light.Expr) : _root_.ThreeSum1960614.Machine.Light.Expr := _root_.ThreeSum1960614.Machine.Light.Expr.load a







/-- The test a ≤ b, written as a < b + 1. -/
abbrev Cond.le (a b : _root_.ThreeSum1960614.Machine.Light.Expr) : _root_.ThreeSum1960614.Machine.Light.Cond := (_root_.ThreeSum1960614.Machine.Light.Cond.lt a ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) b (_root_.ThreeSum1960614.Machine.Light.k 1)))


/-- Branching on a ≠ b: the branches of the test a = b, swapped. -/
abbrev Stmt.iteNe (a b : _root_.ThreeSum1960614.Machine.Light.Expr) (s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt) : _root_.ThreeSum1960614.Machine.Light.Stmt := _root_.ThreeSum1960614.Machine.Light.Stmt.ite ((_root_.ThreeSum1960614.Machine.Light.Cond.eq a b)) s₂ s₁



/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







/-! ## The limits -/

/-- The standing assumptions about the limits: an address fits in a word, and so do the constants
of the programs. -/
structure Std (lim : _root_.ThreeSum1960614.Machine.Light.Limits) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  const_le : (100 : ℤ) ≤ lim.word







end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A running time that is realized on the word RAM

The deductions between running-time claims are made for an arbitrary reading `M : DetTimeModel` of
"is solved by a deterministic algorithm in time T".  `RealizedWithin` is the link to programs: the
problem is solved on the word RAM, in its input layout, within `c T + c` steps.
-/

@[expose] public section

open _root_.EndStatement renaming Instr -> Instr

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam




/-- `RealizedWithin` for a problem of the form of `EndStatement.lean`, on the instances of all
sizes, 0 included: for every exponent `κ` some program solves all instances whose numbers are
bounded by `U = n^κ`, within `c max(T, 0) + c` steps. (A running time `T n U` says nothing at
`n = 0`.) -/
def Realized (Q : _root_.EndStatement.Problem) (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ κ : ℕ, ∃ (P : List _root_.EndStatement.Instr) (b : ℕ) (c : ℝ), 0 ≤ c ∧
    _root_.ThreeSum1960614.Machine.ThreeSumApsp.WordRam.Solves (_root_.ThreeSumApsp.WordRam.ofEnd Q) P b (fun x => x.U = x.n ^ κ) (fun x => c * max (T x.n x.U) 0 + c)

end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From a real exponent to a rational one

An item statement bounds the steps of a program by `C (n^a + 1)`, with real numbers `C` and `a`.
The end statement uses Lean's core library only.  It asks for a step bound `T` with natural values
that depends on the size alone, and it writes `T(n) = O(n^r)`, for a rational `r = p/q`, as
`T(n)^q ≤ K n^p`.  Here the first bound, rounded up, is shown to be a bound of the second kind
(`bigO_stepBound`), and a program that meets the first is shown to meet the second
(`SolvedInTime.endStatement`).  The program and the slope of the word size stay the same.
-/

public section

namespace ThreeSumApsp.WordRam
open _root_.ThreeSumApsp.WordRam






/-- The bound `C (n^a + 1)` of `SolvedInTimeAt` for `e = 0`, rounded up. -/
noncomputable def stepBound (C a : ℝ) (n : ℕ) : ℕ := ⌈C * ((n : ℝ) ^ a + 1)⌉₊





end ThreeSumApsp.WordRam

end

end ThreeSum1960614.Machine


