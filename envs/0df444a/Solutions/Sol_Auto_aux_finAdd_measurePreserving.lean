-- Prove2me | solution 1 for Auto.aux_finAdd_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:31.184188+00:00
-- url     : https://prove2.me/submissions/3a559547-ab32-489d-8517-307bf3f385cd

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
theorem _root_.solution (n m : ℕ) :
    MeasurePreserving (EuclideanSpace.finAddEquivProd :
      EuclideanSpace ℝ (Fin (n + m)) →
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) := by
  let e₁ : EuclideanSpace ℝ (Fin (n + m)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n ⊕ Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm
  let e₂ : EuclideanSpace ℝ (Fin n ⊕ Fin m) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ)
  let e₃ : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    WithLp.prodContinuousLinearEquiv 2 ℝ _ _
  have h₁ : MeasurePreserving e₁ := e₁.measurePreserving
  have h₂ : MeasurePreserving e₂ := e₂.measurePreserving
  have h₃ : MeasurePreserving e₃ := WithLp.volume_preserving_ofLp _ _
  change MeasurePreserving (e₃ ∘ e₂ ∘ e₁)
  exact h₃.comp (h₂.comp h₁)
end Auto
