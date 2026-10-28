-- Prove2me | Definitions.Def_MarkovProcess_Continuity_DyadicFloor
-- name    : MarkovProcess_Continuity_DyadicFloor
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:49:44.519093+00:00
-- url     : https://prove2.me/theorems/296abe47-eadf-4dfe-bd39-aa23c8d350f8
-- title:
--   MarkovProcess definitions: Continuity.DyadicFloor
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.DyadicFloor`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/DyadicFloor.lean#L1-L781

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-!
# Dyadic floor approximation and the unit-interval continuous modification

This file merges the following former modules, one section each:

* `DyadicFloorApproximation`: Left dyadic approximations of unit-interval times
* `DyadicFloorPair`: Comparing two dyadic floor approximations
* `DyadicFloorSampleCauchy`: Cauchy control of dyadic floor samples
* `DyadicFloorDenseTime`: Dyadic floor samples at dyadic times
* `DyadicFloorSampleLimit`: Limits of dyadic floor samples
* `DyadicFloorLimitControl`: Uniform control of dyadic floor-sample limits
* `DyadicFloorLimitPath`: The canonical unit-interval dyadic-floor limit path
* `DyadicFloorConvergenceInMeasure`: Convergence in measure of dyadic floor samples
* `DyadicFloorUnitModification`: A continuous modification on the unit interval
-/

namespace MarkovProcess

section DyadicFloorApproximation


noncomputable section

/-- The index of the left endpoint of the level-`n` dyadic cell containing `t ∈ [0, 1]`. -/
def unitDyadicFloorIndex (n : ℕ) (t : Set.Icc (0 : ℝ) 1) : Fin (2 ^ n + 1) :=
  ⟨⌊(2 ^ n : ℝ) * t.1⌋₊, by
    have hnonneg : 0 ≤ (2 ^ n : ℝ) * t.1 :=
      mul_nonneg (by positivity) t.2.1
    have hfloor_real : (⌊(2 ^ n : ℝ) * t.1⌋₊ : ℝ) ≤ (2 ^ n : ℝ) * t.1 :=
      Nat.floor_le hnonneg
    have hscaled_le : (2 ^ n : ℝ) * t.1 ≤ (2 ^ n : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left t.2.2 (by positivity)
    have hfloor_nat : ⌊(2 ^ n : ℝ) * t.1⌋₊ ≤ 2 ^ n := by
      exact_mod_cast hfloor_real.trans hscaled_le
    omega⟩

@[simp]
theorem unitDyadicFloorIndex_val (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (unitDyadicFloorIndex n t).val = ⌊(2 ^ n : ℝ) * t.1⌋₊ :=
  rfl

/-- The rational level-`n` left dyadic approximation of `t`. -/
def unitDyadicFloorValue (n : ℕ) (t : Set.Icc (0 : ℝ) 1) : NNRat :=
  unitDyadicGrid n (unitDyadicFloorIndex n t)









end

end DyadicFloorApproximation

section DyadicFloorPair

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section









end

end DyadicFloorPair

section DyadicFloorSampleCauchy

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







end DyadicFloorSampleCauchy

section DyadicFloorDenseTime


noncomputable section

/-- A point of the level-`n` unit dyadic grid, regarded as a real time in `[0, 1]`. -/
def unitDyadicGridTime (n : ℕ) (i : Fin (2 ^ n + 1)) : Set.Icc (0 : ℝ) 1 :=
  ⟨(unitDyadicGrid n i : ℝ), by
    constructor
    · positivity
    · unfold unitDyadicGrid
      push_cast
      apply (div_le_one (by positivity)).2
      exact_mod_cast Nat.le_of_lt_succ i.isLt⟩

@[simp]
theorem unitDyadicGridTime_val (n : ℕ) (i : Fin (2 ^ n + 1)) :
    (unitDyadicGridTime n i).1 = (unitDyadicGrid n i : ℝ) :=
  rfl

/-- At every refinement of a dyadic grid, the left floor index of an old grid point is
the correspondingly refined integer index. -/
theorem unitDyadicFloorIndex_gridTime_add (n r : ℕ) (i : Fin (2 ^ n + 1)) :
    (unitDyadicFloorIndex (n + r) (unitDyadicGridTime n i)).val = i.val * 2 ^ r := by
  simp only [unitDyadicFloorIndex_val, unitDyadicGridTime_val, unitDyadicGrid]
  push_cast
  have harg :
      (2 ^ (n + r) : ℝ) * ((i.val : ℝ) / (2 ^ n : ℝ)) =
        (i.val * 2 ^ r : ℕ) := by
    rw [pow_add]
    push_cast
    field_simp
  rw [harg, Nat.floor_natCast]

/-- Every refinement-level left dyadic approximation of a dyadic grid point is exactly
that grid point. -/
theorem unitDyadicFloorValue_gridTime_add (n r : ℕ) (i : Fin (2 ^ n + 1)) :
    unitDyadicFloorValue (n + r) (unitDyadicGridTime n i) = unitDyadicGrid n i := by
  unfold unitDyadicFloorValue unitDyadicGrid
  simp only [unitDyadicFloorIndex_gridTime_add]
  push_cast
  rw [pow_add]
  field_simp

/-- From the level where a dyadic time first appears onward, all its dyadic floor
approximations equal that time. -/
theorem unitDyadicFloorValue_gridTime_of_le
    {n m : ℕ} (hnm : n ≤ m) (i : Fin (2 ^ n + 1)) :
    unitDyadicFloorValue m (unitDyadicGridTime n i) = unitDyadicGrid n i := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact unitDyadicFloorValue_gridTime_add n r i

/-- Sampling any dense-time family along dyadic floor approximations at a dyadic time is
eventually exactly the original dense-time sample. -/
theorem eventually_sample_unitDyadicFloorValue_gridTime
    {E Ω : Type*} (X : NNRat → Ω → E) (n : ℕ) (i : Fin (2 ^ n + 1)) (ω : Ω) :
    ∀ᶠ m in Filter.atTop,
      X (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω = X (unitDyadicGrid n i) ω := by
  rw [Filter.eventually_atTop]
  exact ⟨n, fun m hnm ↦ congrArg (fun q ↦ X q ω)
    (unitDyadicFloorValue_gridTime_of_le hnm i)⟩

/-- Any topological limit of the dyadic floor samples at a dyadic time is the original
dense-time sample at that time. -/
theorem eq_sample_of_tendsto_unitDyadicFloorValue_gridTime
    {E Ω : Type*} [TopologicalSpace E] [T2Space E]
    (X : NNRat → Ω → E) (n : ℕ) (i : Fin (2 ^ n + 1)) (ω : Ω) (y : E)
    (hlim : Filter.Tendsto
      (fun m ↦ X (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω)
      Filter.atTop (nhds y)) :
    y = X (unitDyadicGrid n i) ω := by
  have horiginal : Filter.Tendsto
      (fun m ↦ X (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω)
      Filter.atTop (nhds (X (unitDyadicGrid n i) ω)) :=
    tendsto_const_nhds.congr'
      ((eventually_sample_unitDyadicFloorValue_gridTime X n i ω).mono
        fun _ hm ↦ hm.symm)
  exact tendsto_nhds_unique hlim horiginal

end

end DyadicFloorDenseTime

section DyadicFloorSampleLimit

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]



end DyadicFloorSampleLimit

section DyadicFloorLimitControl

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- The deterministic modulus obtained from two ancestor tails and one same-level increment. -/
def dyadicFloorLimitModulus (γ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  dyadicIncrementThreshold γ (n + 1) *
      (1 - dyadicIncrementThresholdRatio γ)⁻¹ +
    dyadicIncrementThreshold γ n +
    dyadicIncrementThreshold γ (n + 1) *
      (1 - dyadicIncrementThresholdRatio γ)⁻¹







end

end DyadicFloorLimitControl

section DyadicFloorLimitPath

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoMetricSpace E] [CompleteSpace E]

/-- The canonical Mathlib limit of the left dyadic samples on the unit interval. -/
def unitDyadicFloorLimit (X : NNRat → Ω → E) (ω : Ω)
    (t : Set.Icc (0 : ℝ) 1) : E :=
  letI : Nonempty E := ⟨X 0 ω⟩
  limUnder atTop (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω)

/-- A Cauchy sequence of left dyadic samples converges to its canonical dyadic-floor limit. -/
theorem tendsto_unitDyadicFloorLimit_of_cauchySeq
    {X : NNRat → Ω → E} {ω : Ω} {t : Set.Icc (0 : ℝ) 1}
    (h : CauchySeq (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω)) :
    Tendsto (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) atTop
      (nhds (unitDyadicFloorLimit X ω t)) := by
  simpa only [unitDyadicFloorLimit] using h.tendsto_limUnder







end

end DyadicFloorLimitPath

section DyadicFloorConvergenceInMeasure

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]

/-- A nonnegative rational bounded by one, embedded in the real unit interval. -/
def unitIccOfNNRat (t : NNRat) (ht : t ≤ 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(t : ℝ), by positivity, by exact_mod_cast ht⟩











end DyadicFloorConvergenceInMeasure

section DyadicFloorUnitModification

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]









end

end DyadicFloorUnitModification

end MarkovProcess


