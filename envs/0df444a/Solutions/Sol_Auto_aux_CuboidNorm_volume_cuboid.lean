-- Prove2me | solution 1 for Auto.aux_CuboidNorm.volume_cuboid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:40:34.864046+00:00
-- url     : https://prove2.me/submissions/393317fd-802e-43d6-bc66-e598f6d360bd

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
    volume (cuboid l u) = ∏ j, ENNReal.ofReal (u j - l j) :=
  Real.volume_pi_Ico
end Auto.aux_CuboidNorm
