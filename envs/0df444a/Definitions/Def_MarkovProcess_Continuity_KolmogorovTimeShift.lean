-- Prove2me | Definitions.Def_MarkovProcess_Continuity_KolmogorovTimeShift
-- name    : MarkovProcess_Continuity_KolmogorovTimeShift
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:52:23.788438+00:00
-- url     : https://prove2.me/theorems/04935a69-356b-42a3-a584-a5fe7abd5bb8
-- title:
--   MarkovProcess definitions: Continuity.KolmogorovTimeShift
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Continuity.KolmogorovTimeShift`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Continuity/KolmogorovTimeShift.lean#L1-L100

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-!
# Nonnegative-rational time shifts

This file translates a dense-time process by a nonnegative rational time.  Translation is an
isometry of `NNRat`, so the Kolmogorov increment condition is preserved with exactly the same
exponents and constant.  The final definitions and identities identify the unit-interval
dyadic samples and canonical limit for the shifted process with samples of the original process
on the interval starting at the shift.

No global path is glued here, and no measurability of the canonical limit or modification-law
assertion is made.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

variable {Ω E : Type*}

/-- Translate a dense-time process by a nonnegative rational time. -/
def timeShift (k : NNRat) (X : NNRat → Ω → E) : NNRat → Ω → E :=
  fun q ω ↦ X (k + q) ω









noncomputable section

variable [PseudoMetricSpace E]

/-- The canonical unit-interval dyadic-floor limit of the process translated by `k`.  Its time
parameter represents the original interval `[k, k + 1]`. -/
def shiftedUnitDyadicFloorLimit (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    Set.Icc (0 : ℝ) 1 → E :=
  unitDyadicFloorLimit (timeShift k X) ω



variable [CompleteSpace E]



end

end MarkovProcess


