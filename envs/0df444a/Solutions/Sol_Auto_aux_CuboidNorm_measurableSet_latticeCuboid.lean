-- Prove2me | solution 1 for Auto.aux_CuboidNorm.measurableSet_latticeCuboid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:46.040253+00:00
-- url     : https://prove2.me/submissions/4fe2495a-f45a-4c8e-ac19-2e0634298c53

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
theorem _root_.solution {n : ℕ} (ε : ℝ)
    (k : ZVector n) :
    MeasurableSet (latticeCuboid ε k) :=
  measurableSet_cuboid _ _
end Auto.aux_CuboidNorm
