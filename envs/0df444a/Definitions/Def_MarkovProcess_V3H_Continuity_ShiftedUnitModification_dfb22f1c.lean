-- Prove2me | Definitions.Def_MarkovProcess_V3H_Continuity_ShiftedUnitModification_dfb22f1c
-- name    : MarkovProcess_V3H_Continuity_ShiftedUnitModification_dfb22f1c
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:36:23.378571+00:00
-- url     : https://prove2.me/theorems/2414fbc7-340b-4e81-a3b6-6955db10d72f
-- title:
--   MarkovProcess: MarkovProcess_V3H_Continuity_ShiftedUnitModification_dfb22f1c
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovTimeShift_b20f4218
import Definitions.Def_MarkovProcess_V3H_Time_FiniteGridIncrement_7a49f6ac
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous modifications on shifted unit intervals

This file applies the unit-interval totalization to a nonnegative-rational time shift.  It also
identifies the endpoints of the underlying canonical limit exactly, for every sample, using the
eventual constancy of dyadic approximations at dyadic grid times.

No global path is glued here, and no path-space measurability, law, or Hunt-process property is
asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The total continuous unit path obtained from the process translated by `k`.  Its local time
parameter represents the original interval `[k, k + 1]`. -/
def continuousShiftedUnitDyadicFloorLimit
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) : Set.Icc (0 : ℝ) 1 → E :=
  continuousUnitDyadicFloorLimit (timeShift k X) ω





omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- At every dyadic grid time, the shifted canonical limit is exactly the corresponding sample
of the original process.  This is a pointwise identity for every `ω`, not an almost-sure one. -/
theorem shiftedUnitDyadicFloorLimit_gridTime_eq_sample
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω)
    (n : ℕ) (i : Fin (2 ^ n + 1)) :
    shiftedUnitDyadicFloorLimit k X ω (unitDyadicGridTime n i) =
      X (k + unitDyadicGrid n i) ω := by
  have hevent :=
    eventually_sample_unitDyadicFloorValue_gridTime (timeShift k X) n i ω
  have htendsto : Tendsto
      (fun m ↦ timeShift k X
        (unitDyadicFloorValue m (unitDyadicGridTime n i)) ω)
      atTop (nhds (timeShift k X (unitDyadicGrid n i) ω)) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ hm ↦ hm.symm)
  have hcanonical := tendsto_unitDyadicFloorLimit_of_cauchySeq htendsto.cauchySeq
  exact eq_sample_of_tendsto_unitDyadicFloorValue_gridTime
    (timeShift k X) n i ω (shiftedUnitDyadicFloorLimit k X ω (unitDyadicGridTime n i))
    (by simpa only [shiftedUnitDyadicFloorLimit] using hcanonical)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The local zero endpoint of a shifted canonical unit path is exactly the sample at `k`. -/
theorem shiftedUnitDyadicFloorLimit_zero
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    shiftedUnitDyadicFloorLimit k X ω (0 : Set.Icc (0 : ℝ) 1) = X k ω := by
  let i : Fin (2 ^ 0 + 1) := ⟨0, by norm_num⟩
  have htime : unitDyadicGridTime 0 i = (0 : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    norm_num [unitDyadicGridTime, unitDyadicGrid, i]
  rw [← htime]
  simpa only [unitDyadicGrid, i, Nat.cast_zero, zero_div, add_zero] using
    shiftedUnitDyadicFloorLimit_gridTime_eq_sample k X ω 0 i

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The local one endpoint of a shifted canonical unit path is exactly the sample at `k + 1`. -/
theorem shiftedUnitDyadicFloorLimit_one
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    shiftedUnitDyadicFloorLimit k X ω (1 : Set.Icc (0 : ℝ) 1) = X (k + 1) ω := by
  let i : Fin (2 ^ 0 + 1) := ⟨1, by norm_num⟩
  have htime : unitDyadicGridTime 0 i = (1 : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    norm_num [unitDyadicGridTime, unitDyadicGrid, i]
  rw [← htime]
  simpa only [unitDyadicGrid, i, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, pow_zero,
    div_one] using shiftedUnitDyadicFloorLimit_gridTime_eq_sample k X ω 0 i

end

end MarkovProcess


