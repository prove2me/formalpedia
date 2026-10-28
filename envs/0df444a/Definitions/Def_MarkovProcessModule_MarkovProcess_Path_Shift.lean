-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Shift
-- name    : MarkovProcessModule_MarkovProcess_Path_Shift
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:33:34.110712+00:00
-- url     : https://prove2.me/theorems/616abea8-d0ff-4156-ba06-a0201bd23ac4
-- title:
--   MarkovProcess.Path.Shift
-- statement:
--   # Deterministic shifts of continuous paths
--
--   This file defines translation by a fixed nonnegative time on canonical continuous-path space.
--   The shift is jointly continuous in the shift time and path for the compact-open topology.  It also
--   records the corresponding deterministic relation between the canonical filtrations.
--
--   No random-time shift, Markov property, strong Markov property, or Hunt-process assertion is made.
--
--   Complete pinned Lean module MarkovProcess.Path.Shift by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Path/Shift.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Path_Basic

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
theorem timeTranslation_apply (S t : NNReal) : timeTranslation S t = S + t := rfl

/-- Shift a continuous path forward by the deterministic time `S`. -/
def shift (S : NNReal) (omega : ContinuousPath alpha) : ContinuousPath alpha :=
  omega.comp (timeTranslation S)

@[simp]
theorem shift_apply (S t : NNReal) (omega : ContinuousPath alpha) :
    shift S omega t = omega (S + t) := rfl

@[simp]
theorem shift_zero (omega : ContinuousPath alpha) : shift 0 omega = omega := by
  ext t
  simp only [shift_apply, zero_add]

theorem shift_add (S T : NNReal) (omega : ContinuousPath alpha) :
    shift T (shift S omega) = shift (S + T) omega := by
  ext t
  simp only [shift_apply, add_assoc]

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

/-- A shifted event observable by shifted time `t` is observable by original time `S + t`. -/
theorem measurable_shift_canonicalFiltration [MeasurableSpace alpha] [BorelSpace alpha]
    (S t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) (S + t),
      canonicalFiltration (alpha := alpha) t]
      (shift S : ContinuousPath alpha → ContinuousPath alpha) := by
  apply Measurable.of_comap_le
  rw [canonicalFiltration, MeasurableSpace.comap_iSup]
  rw [iSup_le_iff]
  intro u
  rw [MeasurableSpace.comap_comp]
  have hfun : coordinateProcess (alpha := alpha) u ∘ shift S =
      coordinateProcess (alpha := alpha) (S + u) := by
    funext omega
    exact shift_apply S u omega
  rw [hfun]
  exact le_iSup_of_le
    (⟨S + u.1, by simpa only [add_comm] using! add_le_add_left u.2 S⟩ :
      Set.Iic (S + t)) le_rfl

end ContinuousPath
end MarkovProcess


