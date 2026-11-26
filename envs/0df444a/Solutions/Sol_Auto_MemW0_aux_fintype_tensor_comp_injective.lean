-- Prove2me | solution 1 for Auto.MemW0.aux_fintype_tensor_comp_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:14.987835+00:00
-- url     : https://prove2.me/submissions/fec8a60b-89bb-4e91-b0db-d38f3e1b7e2e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearEquiv_between_of_integrable_radius
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
public import Theorems.Thm_Auto_MemW0_aux_comp_injective_continuousLinearMap_prod
public import Theorems.Thm_Auto_MemW0_fintype_tensor

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {𝕜 : Type*} [NormedField 𝕜]
    {f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → 𝕜} (hf : ∀ i, MemW0 (f i))
    (π : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hπ : Function.Injective (ContinuousLinearMap.pi π)) :
    MemW0 (fun uv : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) ↦
      ∏ i, f i (π i uv)) := by
  classical
  let eIdx : Fin (Fintype.card (Σ i, Fin (d i))) ≃ Σ i, Fin (d i) :=
    (Fintype.equivFin (Σ i, Fin (d i))).symm
  let e₁ : EuclideanSpace ℝ (Fin (Fintype.card (Σ i, Fin (d i)))) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Σ i, Fin (d i)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ eIdx
  let e₂ : EuclideanSpace ℝ (Σ i, Fin (d i)) ≃ₗᵢ[ℝ]
      WithLp 2 (∀ i, EuclideanSpace ℝ (Fin (d i))) :=
    LinearIsometryEquiv.piLpCurry ℝ 2 (fun i => fun _ : Fin (d i) => ℝ)
  let e₃ : WithLp 2 (∀ i, EuclideanSpace ℝ (Fin (d i))) ≃L[ℝ]
      (∀ i, EuclideanSpace ℝ (Fin (d i))) :=
    (WithLp.linearEquiv 2 ℝ _).toContinuousLinearEquiv
  let e : EuclideanSpace ℝ (Fin (Fintype.card (Σ i, Fin (d i)))) ≃L[ℝ]
      (∀ i, EuclideanSpace ℝ (Fin (d i))) :=
    e₁.toContinuousLinearEquiv.trans (e₂.toContinuousLinearEquiv.trans e₃)
  let H : (∀ i, EuclideanSpace ℝ (Fin (d i))) → 𝕜 := fun x ↦ ∏ i, f i (x i)
  have hH : MemW0 H := MemW0.fintype_tensor hf
  have hF : MemW0 (H ∘ e) := by
    apply hH.aux_comp_continuousLinearEquiv_between_of_integrable_radius e
    exact aux_integrable_wienerEnvelope_of_integrable' hH.1 zero_lt_one (norm_nonneg _) hH.2
  let A : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (Σ i, Fin (d i)))) :=
    e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi π)
  have hA : Function.Injective A := e.symm.injective.comp hπ
  have hFA := hF.aux_comp_injective_continuousLinearMap_prod A hA
  simpa [H, A, Function.comp_def] using hFA
end MemW0
end Auto
