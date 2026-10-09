-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartTensorCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoChartTensorCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:49:01.700755+00:00
-- url     : https://prove2.me/theorems/efea1005-bc1f-4b91-b5f1-7fec459ae111
-- title:
--   FLT.Assumptions.MazurProof.N13TwoChartTensorCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoChartTensorCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoChartTensorCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartPicardRealization_p0

set_option autoImplicit false




/-!
Uncompiled candidate for FLT-C13-B03-PLANr1. All Lean checks: NOT RUN.
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
These are tensor/restriction identities, not the missing B03 specialization theorem.
-/

namespace MazurProof.N13.TwoChartTensorCompatibility

noncomputable section

open N13TwoChartPicardRealization

/-- Extending the affine invertible ideal commutes with tensor product. -/
theorem genericIdealUnit_tensor (L M : Line) :
    genericIdealUnit (N13TwoChartLineTensor.tensor L M) =
      genericIdealUnit L * genericIdealUnit M := by
  apply Units.ext
  rw [Units.val_mul, coe_genericIdealUnit, coe_genericIdealUnit,
    coe_genericIdealUnit, N13TwoChartLineTensor.tensor_affineIdeal,
    Ideal.map_mul, FractionalIdeal.coeIdeal_mul]

/-- The separately supplied orientation integers must add under tensor. -/
theorem genericRaw_tensor (L M : Line) (k l : ℤ) :
    genericRaw (N13TwoChartLineTensor.tensor L M) (k + l) =
      genericRaw L k * genericRaw M l := by
  apply Prod.ext
  · exact genericIdealUnit_tensor L M
  · rfl

/-- This generic-fibre identity does not assert coherence of either marking
with the infinity-chart lattice. -/
theorem genericClass_tensor (L M : Line) (k l : ℤ) :
    genericClass (N13TwoChartLineTensor.tensor L M) (k + l) =
      genericClass L k + genericClass M l := by
  unfold genericClass
  rw [genericRaw_tensor, map_mul]
  rfl

/-- Correct generic classes give a generic degree-four balancing equality.
Lifting this equality to an integral principal comparison on both charts
is a separate, presently missing theorem. -/
theorem genericClass_tensor_balance
    {G : Type*} [AddGroup G] (f : G →+ GenericPic)
    (c : G → Data) (hc : ∀ P, (c P).toGenericPic = f P)
    (P Q : G) :
    genericClass
        (N13TwoChartLineTensor.tensor (c P).charts (c Q).charts)
        ((c P).infinityOrder + (c Q).infinityOrder) =
      genericClass
        (N13TwoChartLineTensor.tensor (c (P + Q)).charts (c 0).charts)
        ((c (P + Q)).infinityOrder + (c 0).infinityOrder) := by
  rw [genericClass_tensor, genericClass_tensor]
  change (c P).toGenericPic + (c Q).toGenericPic =
    (c (P + Q)).toGenericPic + (c 0).toGenericPic
  rw [hc P, hc Q, hc (P + Q), hc 0, map_add, map_zero, add_zero]

/-- Both special charts, not merely the affine chart, respect tensor. -/
theorem restrict_tensor (L M : Line) :
    N13TwoChartSpecialRestriction.restrict
        (N13TwoChartLineTensor.tensor L M) =
      N13SpecialDivisorCharts.tensor
        (N13TwoChartSpecialRestriction.restrict L)
        (N13TwoChartSpecialRestriction.restrict M) := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal L M
  · exact N13TwoChartSpecialRestriction.restrict_tensor_infinityIdeal L M

/-- A realization determines the complete reduced pair of chart ideals. -/
theorem restrict_data (D : Data) :
    N13TwoChartSpecialRestriction.restrict D.charts =
      N13SpecialDivisorCharts.ofDivisor D.specialDivisor := by
  exact N13TwoChartSpecialRestriction.ChartPair.ext
    D.special_affine D.special_infinity

/-- Tensoring two degree-two realizations gives the chart ideals of their
literal degree-four sum. It does not produce another `Data`. -/
theorem restrict_tensor_data (D E : Data) :
    N13TwoChartSpecialRestriction.restrict
        (N13TwoChartLineTensor.tensor D.charts E.charts) =
      N13SpecialDivisorCharts.tensor
        (N13SpecialDivisorCharts.ofDivisor D.specialDivisor)
        (N13SpecialDivisorCharts.ofDivisor E.specialDivisor) := by
  rw [restrict_tensor, restrict_data, restrict_data]

end

end MazurProof.N13.TwoChartTensorCompatibility


