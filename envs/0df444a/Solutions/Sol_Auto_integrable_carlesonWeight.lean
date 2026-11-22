-- Prove2me | solution 1 for Auto.integrable_carlesonWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:48:03.63256+00:00
-- url     : https://prove2.me/submissions/e150744c-db9b-4406-a9d6-d5705537c49d

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_integrable_of_norm_le_of_vanish
public import Theorems.Thm_Auto_carlesonWeight_nonneg
public import Theorems.Thm_Auto_carlesonWeight_le_mass
public import Theorems.Thm_Auto_carlesonWeight_eq_zero
public import Theorems.Thm_Auto_measurable_carlesonWeight

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution : Integrable carlesonWeight :=
  integrable_of_norm_le_of_vanish (A := 11) measurable_carlesonWeight.aestronglyMeasurable
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (carlesonWeight_nonneg t)]
      exact carlesonWeight_le_mass t)
    (fun t ht => carlesonWeight_eq_zero ht.le)
end Auto
