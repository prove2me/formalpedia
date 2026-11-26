-- Prove2me | solution 1 for Auto.aux_integral_comp_continuousLinearEquiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:09.196487+00:00
-- url     : https://prove2.me/submissions/dea61efe-1f16-4870-9262-0f6f6b220cc2

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    (e : E ≃L[ℝ] F) {g : F → ℝ} (hg : Continuous g) :
    (∫ x, g (e x)) =
      (Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume : ℝ) *
        ∫ y, g y := by
  let : Measure.IsAddHaarMeasure (Measure.map (e : E → F) volume) :=
    e.isAddHaarMeasure_map volume
  have hscalar : Measure.map (e : E → F) volume =
      Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume • volume :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map (e : E → F) volume) volume
  calc
    (∫ x, g (e x)) = ∫ y, g y ∂Measure.map (e : E → F) volume :=
      (integral_map e.continuous.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂(Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume •
        volume) :=
      congrArg (fun μ : Measure F => ∫ y, g y ∂μ) hscalar
    _ = (Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume : ℝ) *
        ∫ y, g y := by
      rw [integral_smul_nnreal_measure]
      rfl
end Auto
