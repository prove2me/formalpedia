-- Prove2me | solution 1 for Auto.aux_integrable_comp_continuousLinearEquiv_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:26.224068+00:00
-- url     : https://prove2.me/submissions/26ee49e0-cd46-4231-9458-01fc7d91930f

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
theorem _root_.solution {E F K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [ProperSpace F]
    [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
    [NormedAddCommGroup K] {g : F → K} (hg : Integrable g) (e : E ≃L[ℝ] F) :
    Integrable (g ∘ e) := by
  let : Measure.IsAddHaarMeasure (Measure.map (e : E → F) volume) :=
    e.isAddHaarMeasure_map volume
  have hscalar : Measure.map (e : E → F) volume =
      Measure.addHaarScalarFactor (Measure.map (e : E → F) volume) volume • volume :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map (e : E → F) volume) volume
  have hmap : Integrable g (Measure.map (e : E → F) volume) := by
    rw [hscalar]
    exact hg.smul_measure_nnreal
  exact hmap.comp_measurable e.continuous.measurable
end Auto
