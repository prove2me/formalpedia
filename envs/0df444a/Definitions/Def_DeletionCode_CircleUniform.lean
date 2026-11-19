-- Prove2me | Definitions.Def_DeletionCode_CircleUniform
-- name    : DeletionCode_CircleUniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T05:04:32.689571+00:00
-- url     : https://prove2.me/theorems/509ab054-93a7-4e2b-80ef-b3866d8668c1
-- title:
--   Circle Uniform
-- statement:
--   Definitions and structural lemmas for Circle Uniform, from Eyal En Gad's pinned Deletion codes: binary insertion/deletion bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit true
namespace DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal
def smallArc (Q : ℕ) : Set UnitAddCircle := {z | ‖z‖ < 1 / (Q : ℝ)}
noncomputable def realUnit : Measure ℝ := volume.restrict (Set.Ico 0 1)
instance realUnit_probability : IsProbabilityMeasure realUnit where
  measure_univ := by simp [realUnit]
noncomputable def realWeights (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ : I => realUnit)
instance realWeights_probability (I : Type*) [Fintype I] :
    IsProbabilityMeasure (realWeights I) := by
  unfold realWeights
  infer_instance
def toCircle {I : Type*} (weights : I → ℝ) : I → UnitAddCircle :=
  fun i => (weights i : UnitAddCircle)
end DeletionCode.CircleUniform


