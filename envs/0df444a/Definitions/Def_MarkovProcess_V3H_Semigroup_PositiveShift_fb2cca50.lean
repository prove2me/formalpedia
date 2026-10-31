-- Prove2me | Definitions.Def_MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
-- name    : MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:16:31.644994+00:00
-- url     : https://prove2.me/theorems/37f0ee0b-325d-4af3-9e3f-28e97612de91
-- title:
--   MarkovProcess: MarkovProcess_V3H_Semigroup_PositiveShift_fb2cca50
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Mathlib.Analysis.SpecificLimits.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Limits along positive real parameters

This module provides elementary filter limits for positive real resolvent
parameters and a filter-generic criterion that turns a vanishing square bound
into convergence to zero.
-/

namespace MarkovProcess.Semigroup

open Filter Set Topology

/-- Positive real parameters, ordered by their underlying real values. -/
abbrev PositiveShift := Set.Ioi (0 : ℝ)



/-- The inverse of a positive parameter tends to zero as the parameter tends to infinity. -/
theorem tendsto_positiveShift_inv_atTop_zero :
    Tendsto (fun α : PositiveShift ↦ (α : ℝ)⁻¹) atTop (nhds 0) := by
  exact (tendsto_comp_val_Ioi_atTop (a := (0 : ℝ))).2 tendsto_inv_atTop_zero

/-- A fixed real constant times the inverse parameter tends to zero. -/
theorem tendsto_const_mul_positiveShift_inv_atTop_zero (C : ℝ) :
    Tendsto (fun α : PositiveShift ↦ C * (α : ℝ)⁻¹) atTop (nhds 0) := by
  simpa only [mul_zero] using
    (tendsto_const_nhds (x := C)).mul tendsto_positiveShift_inv_atTop_zero



end MarkovProcess.Semigroup


