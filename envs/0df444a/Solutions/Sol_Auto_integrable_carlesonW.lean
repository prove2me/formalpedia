-- Prove2me | solution 1 for Auto.integrable_carlesonW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:44:43.10208+00:00
-- url     : https://prove2.me/submissions/527b5e09-2a91-447d-83a4-c9b1b9f08a05

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_continuous_carlesonW
public import Theorems.Thm_Auto_carlesonW_nonneg
public import Theorems.Thm_Auto_carlesonW_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (t : ℝ) : Integrable (carlesonW t) := by
  refine carlesonBump₀.integrable.mono'
    (continuous_carlesonW.comp (Continuous.prodMk_right t)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (carlesonW_nonneg t u)]
  exact carlesonW_le t u
end Auto
