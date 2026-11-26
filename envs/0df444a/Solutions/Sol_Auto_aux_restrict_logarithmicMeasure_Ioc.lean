-- Prove2me | solution 1 for Auto.aux_restrict_logarithmicMeasure_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:24.113853+00:00
-- url     : https://prove2.me/submissions/33f9f1e4-e323-47c4-bb5f-94a4a07d3d4e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {α β x y : ℝ}
    (hsub : Set.Ioc x y ⊆ Set.Icc α β) :
    (aux_logarithmicMeasure α β).restrict (Set.Ioc x y) =
      (volume.restrict (Set.Ioc x y)).withDensity fun t ↦ ENNReal.ofReal t⁻¹ := by
  rw [aux_logarithmicMeasure, restrict_withDensity measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub]
end Auto
