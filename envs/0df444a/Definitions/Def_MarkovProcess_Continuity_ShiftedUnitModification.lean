-- Prove2me | Definitions.Def_MarkovProcess_Continuity_ShiftedUnitModification
-- name    : MarkovProcess_Continuity_ShiftedUnitModification
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:57:45.014883+00:00
-- url     : https://prove2.me/theorems/8c2e2467-7a97-4330-8389-310a05df0e81
-- title:
--   MarkovProcess definitions: Continuity.ShiftedUnitModification
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.ShiftedUnitModification`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/ShiftedUnitModification.lean#L1-L104

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

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


