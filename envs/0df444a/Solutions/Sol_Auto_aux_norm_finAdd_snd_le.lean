-- Prove2me | solution 1 for Auto.aux_norm_finAdd_snd_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:48.253455+00:00
-- url     : https://prove2.me/submissions/b0e54c7e-5589-4936-84d4-737b3d2cba18

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
theorem _root_.solution {n m : ℕ} (w : EuclideanSpace ℝ (Fin (n + m))) :
    ‖(EuclideanSpace.finAddEquivProd w).2‖ ≤ ‖w‖ := by
  let e₁ : EuclideanSpace ℝ (Fin (n + m)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin n ⊕ Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm
  let e₂ : EuclideanSpace ℝ (Fin n ⊕ Fin m) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ)
  let e₃ : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    WithLp.prodContinuousLinearEquiv 2 ℝ _ _
  change ‖((e₂ (e₁ w)).ofLp).2‖ ≤ ‖w‖
  change ‖(e₂ (e₁ w)).snd‖ ≤ ‖w‖
  calc
    ‖(e₂ (e₁ w)).snd‖ ≤ ‖e₂ (e₁ w)‖ :=
      WithLp.norm_snd_le (EuclideanSpace ℝ (Fin n)) (e₂ (e₁ w))
    _ = ‖e₁ w‖ := e₂.norm_map _
    _ = ‖w‖ := e₁.norm_map _
end Auto
