-- Prove2me | Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
-- name    : MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:35:05.631704+00:00
-- url     : https://prove2.me/theorems/89a9fc06-2912-4b09-98ed-2209577bebb8
-- title:
--   MarkovProcess: MarkovProcess_V3H_Semigroup_YosidaStrongLimit_932a76ce
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_DenseCoreConvergence_48a35d65
import Definitions.Def_MarkovProcess_V3H_Semigroup_Duhamel_d67aa5ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaApproximation_2f7df37a
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strong limits of Yosida approximations

This file constructs the canonical contraction obtained by taking the strong
limit of the Yosida exponentials along the shifts `n + 1`.  Continuity of its
orbits is proved in `Semigroup/Generation.lean`, from the criterion of
`Semigroup/OrbitContinuity.lean`.
-/

open Filter NormedSpace Set Topology

noncomputable section

namespace MarkovProcess.Semigroup

/-- The canonical sequence of positive shifts, `n + 1`. -/
def naturalShift (n : ℕ) : PositiveShift :=
  ⟨(n : ℝ) + 1, by
    change 0 < (n : ℝ) + 1
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one⟩



/-- The canonical positive shifts tend to infinity. -/
theorem tendsto_naturalShift_atTop : Tendsto naturalShift atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro α
  obtain ⟨n, hn⟩ := exists_nat_ge (α : ℝ)
  exact ⟨n, fun m hm ↦ by
    change (α : ℝ) ≤ (m : ℝ) + 1
    exact hn.trans (le_add_of_nonneg_right zero_le_one) |>.trans
      (add_le_add (Nat.cast_le.2 hm) le_rfl)⟩

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Along the canonical shifts, Yosida generators converge on every fixed
resolvent range. -/
theorem tendsto_yosidaGenerator_naturalShift_apply_operator
    (R : ContractiveResolvent E) (mu : PositiveShift) (y : E) :
    Tendsto (fun n ↦ R.yosidaGenerator (naturalShift n) (R.operator mu y))
      atTop (nhds ((mu : ℝ) • R.operator mu y - y)) := by
  exact (R.tendsto_yosidaGenerator_apply_operator mu y).comp tendsto_naturalShift_atTop

/-- Along the canonical shifts, Yosida generators are Cauchy on every fixed
resolvent range. -/
theorem cauchySeq_yosidaGenerator_naturalShift_apply_operator
    (R : ContractiveResolvent E) (mu : PositiveShift) (y : E) :
    CauchySeq (fun n ↦ R.yosidaGenerator (naturalShift n) (R.operator mu y)) :=
  (R.tendsto_yosidaGenerator_naturalShift_apply_operator mu y).cauchySeq

section CompleteSpace

variable [CompleteSpace E]

/-- At a fixed time, the canonical Yosida exponentials are Cauchy on every
fixed resolvent range. -/
theorem p2m_embedded_af6716111d1ade2b
    (R : ContractiveResolvent E) (mu : PositiveShift) (t : NNReal) (y : E) :
    CauchySeq (fun n ↦ R.yosidaOperator (naturalShift n) t (R.operator mu y)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [R.yosidaOperator_zero, ContinuousLinearMap.id_apply] using
      (cauchySeq_const (R.operator mu y))
  · rw [Metric.cauchySeq_iff]
    intro eps heps
    have htpos : 0 < (t : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
      (R.cauchySeq_yosidaGenerator_naturalShift_apply_operator mu y)
      (eps / (t : ℝ)) (div_pos heps htpos)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hcontract (k : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
        ‖exp (s • R.yosidaGenerator (naturalShift k))‖ ≤ 1 := by
      simpa only [yosidaOperator] using!
        R.norm_yosidaOperator_le_one (naturalShift k) ⟨s, hs.1⟩
    have hestimate := _root_.MarkovProcess.Semigroup.p2m_embedded_cfdd32977de215ab
      (R.yosidaGenerator (naturalShift n))
      (R.yosidaGenerator (naturalShift m))
      (R.yosidaGenerator_commute (naturalShift n) (naturalShift m))
      (NNReal.coe_nonneg t) (hcontract n) (hcontract m) (R.operator mu y)
    rw [dist_eq_norm]
    change
      ‖exp ((t : ℝ) • R.yosidaGenerator (naturalShift m)) (R.operator mu y) -
          exp ((t : ℝ) • R.yosidaGenerator (naturalShift n)) (R.operator mu y)‖ < eps
    refine lt_of_le_of_lt hestimate ?_
    rw [sub_apply, ← dist_eq_norm]
    calc
      (t : ℝ) * dist
          (R.yosidaGenerator (naturalShift m) (R.operator mu y))
          (R.yosidaGenerator (naturalShift n) (R.operator mu y))
          < (t : ℝ) * (eps / (t : ℝ)) :=
        mul_lt_mul_of_pos_left (hN m hm n hn) htpos
      _ = eps := mul_div_cancel₀ eps htpos.ne'

/-- The canonical Yosida exponential sequence at a fixed time. -/
def yosidaOperatorSequence (R : ContractiveResolvent E) (t : NNReal) :
    ℕ → E →L[ℝ] E :=
  fun n ↦ R.yosidaOperator (naturalShift n) t

theorem norm_yosidaOperatorSequence_le_one (R : ContractiveResolvent E) (t : NNReal) (n : ℕ) :
    ‖R.yosidaOperatorSequence t n‖ ≤ 1 :=
  R.norm_yosidaOperator_le_one (naturalShift n) t

theorem cauchySeq_yosidaOperatorSequence_apply
    (R : ContractiveResolvent E) (t : NNReal) (x : E) :
    CauchySeq (fun n ↦ R.yosidaOperatorSequence t n x) := by
  let one : PositiveShift := ⟨1, by norm_num⟩
  exact _root_.MarkovProcess.p2m_embedded_e260493a9418404d
    (R.yosidaOperatorSequence t) (R.operator one)
    (R.norm_yosidaOperatorSequence_le_one t) (R.denseRange one)
    (R.p2m_embedded_af6716111d1ade2b one t) x

/-- The canonical strong limit of the Yosida exponential approximants. -/
def yosidaStrongLimit (R : ContractiveResolvent E) (t : NNReal) : E →L[ℝ] E :=
  strongOperatorLimit (R.yosidaOperatorSequence t)
    (R.norm_yosidaOperatorSequence_le_one t)
    (R.cauchySeq_yosidaOperatorSequence_apply t)

/-- The canonical Yosida exponential approximants converge strongly. -/
theorem tendsto_yosidaOperator_naturalShift_apply
    (R : ContractiveResolvent E) (t : NNReal) (x : E) :
    Tendsto (fun n ↦ R.yosidaOperator (naturalShift n) t x) atTop
      (nhds (R.yosidaStrongLimit t x)) := by
  exact tendsto_strongOperatorLimit_apply (R.yosidaOperatorSequence t)
    (R.norm_yosidaOperatorSequence_le_one t)
    (R.cauchySeq_yosidaOperatorSequence_apply t) x

/-- The canonical strong limit is a contraction. -/
theorem norm_yosidaStrongLimit_le_one (R : ContractiveResolvent E) (t : NNReal) :
    ‖R.yosidaStrongLimit t‖ ≤ 1 := by
  exact norm_strongOperatorLimit_le_one (R.yosidaOperatorSequence t)
    (R.norm_yosidaOperatorSequence_le_one t)
    (R.cauchySeq_yosidaOperatorSequence_apply t)

@[simp]
theorem yosidaStrongLimit_zero (R : ContractiveResolvent E) :
    R.yosidaStrongLimit 0 = ContinuousLinearMap.id ℝ E := by
  ext x
  exact tendsto_nhds_unique (R.tendsto_yosidaOperator_naturalShift_apply 0 x)
    (by simpa only [R.yosidaOperator_zero, ContinuousLinearMap.id_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ x) atTop (nhds x)))

/-- The canonical strong limits satisfy the semigroup law. -/
theorem yosidaStrongLimit_add (R : ContractiveResolvent E) (s t : NNReal) :
    R.yosidaStrongLimit (s + t) =
      (R.yosidaStrongLimit s).comp (R.yosidaStrongLimit t) := by
  ext x
  apply tendsto_nhds_unique (R.tendsto_yosidaOperator_naturalShift_apply (s + t) x)
  have hcomp := _root_.MarkovProcess.Semigroup.p2m_embedded_d9d8a86082858d3a
    (R.yosidaOperatorSequence s) (R.yosidaOperatorSequence t)
    (R.yosidaStrongLimit s) (R.yosidaStrongLimit t)
    (R.norm_yosidaOperatorSequence_le_one s)
    (R.tendsto_yosidaOperator_naturalShift_apply s)
    (R.tendsto_yosidaOperator_naturalShift_apply t) x
  simpa only [yosidaOperatorSequence, R.yosidaOperator_add,
    ContinuousLinearMap.comp_apply] using hcomp

end CompleteSpace

end ContractiveResolvent

end MarkovProcess.Semigroup


