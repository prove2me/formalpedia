-- Prove2me | solution 1 for Auto.aux_CuboidNorm.measurableSet_cuboid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:28.295349+00:00
-- url     : https://prove2.me/submissions/412d1714-a245-4e63-8133-302d6537f8cf

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ} (l u : RVector n) :
    MeasurableSet (cuboid l u) := by
  unfold cuboid
  exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico
end Auto.aux_CuboidNorm
