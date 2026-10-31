-- Prove2me | Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
-- name    : MarkovProcess_V3H_Path_Shift_e538a06a
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:55.670198+00:00
-- url     : https://prove2.me/theorems/14a7ba8b-381d-4dd1-9490-2fde45f23640
-- title:
--   MarkovProcess: MarkovProcess_V3H_Path_Shift_e538a06a
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic shifts of continuous paths

This file defines translation by a fixed nonnegative time on canonical continuous-path space.
The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
records the corresponding deterministic relation between the canonical filtrations.

No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
-/

open MeasureTheory

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

/-- Translation of nonnegative time by `S`, as a continuous self-map of `NNReal`. -/
def timeTranslation (S : NNReal) : C(NNReal, NNReal) where
  toFun t := S + t
  continuous_toFun := continuous_const.add continuous_id

@[simp]
theorem p2m_embedded_4a199ddaaeecdca4 (S t : NNReal) : timeTranslation S t = S + t := rfl

/-- Shift a continuous path forward by the deterministic time `S`. -/
def shift (S : NNReal) (omega : ContinuousPath alpha) : ContinuousPath alpha :=
  omega.comp (timeTranslation S)

@[simp]
theorem shift_apply (S t : NNReal) (omega : ContinuousPath alpha) :
    shift S omega t = omega (S + t) := rfl

@[simp]
theorem p2m_embedded_5111c7f77e8ef02f (omega : ContinuousPath alpha) : shift 0 omega = omega := by
  ext t
  simp only [shift_apply, zero_add]



/-- The family of time translations is continuous for the compact-open topology. -/
theorem continuous_timeTranslation : Continuous (timeTranslation : NNReal → C(NNReal, NNReal)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_fst.add continuous_snd

/-- Deterministic path shifting is jointly continuous in the shift time and the path. -/
theorem continuous_shift :
    Continuous (fun p : NNReal × ContinuousPath alpha ↦ shift p.1 p.2) := by
  exact ContinuousMap.continuous_comp'.comp
    ((continuous_timeTranslation.comp continuous_fst).prodMk continuous_snd)

/-- Shifting by a fixed deterministic time is continuous. -/
theorem continuous_shift_fixed (S : NNReal) :
    Continuous (shift S : ContinuousPath alpha → ContinuousPath alpha) :=
  continuous_shift.comp (continuous_const.prodMk continuous_id)

/-- Shifting by a fixed deterministic time is Borel measurable. -/
theorem measurable_shift_fixed (S : NNReal) :
    Measurable[borel (ContinuousPath alpha), borel (ContinuousPath alpha)]
      (shift S : ContinuousPath alpha → ContinuousPath alpha) :=
  (continuous_shift_fixed S).borel_measurable



end ContinuousPath
end MarkovProcess


