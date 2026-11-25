-- Prove2me | Definitions.Def_SourceProof_8715d5ca16e616ee0eee368f
-- name    : SourceProof_8715d5ca16e616ee0eee368f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:50:56.402022+00:00
-- url     : https://prove2.me/theorems/22567ff4-441d-54cf-ab51-15129da12475
-- title:
--   StochLean source theorem: StochLean.summable_abs_contDiff_second_order_jump_remainders

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_03d80293d3aa59b22d10d9aa
import Definitions.Def_SourceProof_62c74d4c6782b2a3e76047aa
import Definitions.Def_SourceProof_ca07ea6fa0932d45a475bf39
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Absolute C2 jump-remainder summability from square-summable jumps

Finite variation of the original path is not required. Compact cadlag
bounds and the actual quadratic Taylor quotient dominate each remainder
by a constant times its squared jump.
-/

@[expose] public section

open Set Function ProbabilityTheory
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8715d5ca16e616ee0eee368f {x : ℝ≥0 → ℝ}
    (hx : IsCadlagPath x) {T : ℝ≥0}
    (hs : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Summable (fun s : Ioc 0 T ↦
      |f (x s) - f (leftLim x s) - deriv f (leftLim x s) * (x s - leftLim x s) -
        deriv (deriv f) (leftLim x s) / 2 * (x s - leftLim x s) ^ 2|) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have h := _root_.Prove2MeSourceProof.h_ca07ea6fa0932d45a475bf39 hx hs
    (Φ := fun a b ↦ StochLean.quadraticTaylorSlope f a b - deriv (deriv f) a / 2)
    ((_root_.Prove2MeSourceProof.h_03d80293d3aa59b22d10d9aa hf).sub
      ((hd.continuous_deriv_one.comp continuous_fst).div_const 2))
  simpa only [sub_mul, _root_.Prove2MeSourceProof.h_62c74d4c6782b2a3e76047aa] using h
end StochLean


