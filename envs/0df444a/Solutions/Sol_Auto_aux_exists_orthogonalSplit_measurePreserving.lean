-- Prove2me | solution 1 for Auto.aux_exists_orthogonalSplit_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:37.289162+00:00
-- url     : https://prove2.me/submissions/02b7ed68-909e-4562-81ef-5d9c5b6634de

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
theorem _root_.solution {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (s : Submodule ℝ V) :
    ∃ e : V ≃L[ℝ] s × sᗮ, MeasurePreserving e := by
  let e₁ : V ≃ₗᵢ[ℝ] WithLp 2 (s × sᗮ) := s.orthogonalDecomposition
  let e₂ : WithLp 2 (s × sᗮ) ≃L[ℝ] s × sᗮ :=
    WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ
  refine ⟨e₁.toContinuousLinearEquiv.trans e₂, ?_⟩
  have h₁ : MeasurePreserving e₁ := e₁.measurePreserving
  have h₂ : MeasurePreserving e₂ := WithLp.volume_preserving_ofLp s sᗮ
  change MeasurePreserving (e₂ ∘ e₁)
  exact h₂.comp h₁
end Auto
