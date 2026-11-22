-- Prove2me | solution 1 for Auto.carlesonWeight_eq_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:48:43.761817+00:00
-- url     : https://prove2.me/submissions/3bf08483-4db8-4058-9991-f43fc1c80b81

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonW_eq_of_abs_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {t : ℝ} (ht : |t| ≤ 2) : carlesonWeight t = carlesonMass :=
  integral_congr_ae (ae_of_all _ (carlesonW_eq_of_abs_le ht))
end Auto
