-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_comp_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:46.972607+00:00
-- url     : https://prove2.me/submissions/9ade6fdd-0644-467c-886f-93ece332cb68

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
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup K]
    (e : E ≃ₗᵢ[ℝ] F) {f : F → K} (x : E) :
    wienerEnvelope (f ∘ e) 1 x = wienerEnvelope f 1 (e x) := by
  unfold wienerEnvelope
  congr 1
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨e z, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    simp only [Function.comp_apply, e.map_add]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨e.symm w, ?_, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    · simp only [Function.comp_apply, e.map_add, e.apply_symm_apply]
end Auto
