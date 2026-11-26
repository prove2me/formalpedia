-- Prove2me | solution 1 for Auto.aux_CuboidNorm.measurableSet_latticeAxisCuboid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:41:28.778711+00:00
-- url     : https://prove2.me/submissions/bf0105f3-4970-46c6-9bac-d10646d9e5ac

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_cuboid

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ} (ε δ : ℝ)
    (i : Fin n) (k : ZVector n) :
    MeasurableSet (latticeAxisCuboid ε δ i k) :=
  measurableSet_cuboid _ _
end Auto.aux_CuboidNorm
