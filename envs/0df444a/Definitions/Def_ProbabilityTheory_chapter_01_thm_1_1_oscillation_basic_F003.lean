-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F003
-- name    : ProbabilityTheory_chapter_01_thm_1_1_oscillation_basic_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T15:25:18.582671+00:00
-- url     : https://prove2.me/theorems/314ab920-791b-4a7c-a1d5-034ce1c395bc
-- title:
--   Chapter 1, thm_1_1_oscillation_basic: supporting Lean bundle F003
-- statement:
--   Supporting Lean declarations for Chapter 1, source module `thm_1_1_oscillation_basic`: `alpha_local_increment_mono_of_radius_le`. The mathematical interpretation of this bundle needs review.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_1_oscillation_basic.lean

import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute

lemma alpha_local_increment_mono_of_radius_le {α : ℝ → ℝ}
    (hα_mono : Monotone α) {c r R : ℝ}
    (hrR : r ≤ R) :
    α (c + r) - α (c - r) ≤ α (c + R) - α (c - R) := by
  have hleft : c - R ≤ c - r := by linarith
  have hright : c + r ≤ c + R := by linarith
  have hα_left : α (c - R) ≤ α (c - r) := hα_mono hleft
  have hα_right : α (c + r) ≤ α (c + R) := hα_mono hright
  linarith
end Thm11SourceRoute


