-- Prove2me | solution 1 for Auto.MemW0.aux_comp_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:34.383109+00:00
-- url     : https://prove2.me/submissions/1745a21c-43cd-4810-aa8a-79b99ba60180

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_wienerEnvelope_comp_linearIsometryEquiv

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {E F K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] [NormedAddCommGroup K]
    {f : F → K} (hf : MemW0 f) (e : E ≃ₗᵢ[ℝ] F) :
    MemW0 (f ∘ e) := by
  refine ⟨hf.1.comp e.continuous, ?_⟩
  have hcomp : Integrable (wienerEnvelope f 1 ∘ e) :=
    (e.measurePreserving).integrable_comp_emb e.toHomeomorph.measurableEmbedding |>.mpr hf.2
  convert hcomp using 1
  ext x
  exact aux_wienerEnvelope_comp_linearIsometryEquiv e x
end MemW0
end Auto
