-- Prove2me | solution 1 for Auto.exists_brascamp_lieb_memW0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:40.589809+00:00
-- url     : https://prove2.me/submissions/c3535a6f-04e6-41e0-937a-5017229833e4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearEquiv_between_of_integrable_radius
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
public import Theorems.Thm_Auto_aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound
public import Theorems.Thm_Auto_exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound
public import Theorems.Thm_Auto_MemW0_fintype_tensor
public import Theorems.Thm_Auto_fintype_tensor_wienerNorm_le
public import Theorems.Thm_Auto_aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution
    {ι : Type*} [Fintype ι] {m l : ℕ} {d : ι → ℕ}
    {K : Type*} [NormedField K] [NormedSpace ℝ K]
    (π : ∀ i, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (d i)))
    (hker : ⨅ i, LinearMap.ker (π i).toLinearMap = ⊥) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ∀ i, EuclideanSpace ℝ (Fin (d i)) → K,
      (∀ i, MemW0 (f i)) →
      (∀ u : EuclideanSpace ℝ (Fin m),
        MemW0 (fun v : EuclideanSpace ℝ (Fin l) => ∏ i, f i (π i (u, v)))) ∧
      MemW0 (fun u : EuclideanSpace ℝ (Fin m) =>
        ∫ v, ∏ i, f i (π i (u, v))) ∧
      (∫ u, wienerEnvelope
        (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, ∏ i, f i (π i (u, v))) 1 u) ≤
        C * ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by
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
  let A : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (Σ i, Fin (d i)))) :=
    e.symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi π)
  have hπ : Function.Injective (ContinuousLinearMap.pi π) :=
    aux_continuousLinearMap_pi_injective_of_iInf_ker_eq_bot π hker
  have hA : Function.Injective A := e.symm.injective.comp hπ
  obtain ⟨C₁, C₂, hC₁_pos, hC₂_pos, hA_bound⟩ :=
    exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound (K := K) A hA
  obtain ⟨Ce, hCe_pos, hCe⟩ :=
    aux_exists_wienerEnvelope_comp_continuousLinearEquiv_bound (K := K) e
  refine ⟨C₂ * Ce, mul_pos hC₂_pos hCe_pos, ?_⟩
  intro f hf
  let H : (∀ i, EuclideanSpace ℝ (Fin (d i))) → K := fun x => ∏ i, f i (x i)
  let F : EuclideanSpace ℝ (Fin (Fintype.card (Σ i, Fin (d i)))) → K := H ∘ e
  let P : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → K :=
    fun uv => ∏ i, f i (π i uv)
  have hH : MemW0 H := MemW0.fintype_tensor hf
  have hF : MemW0 F := by
    apply hH.aux_comp_continuousLinearEquiv_between_of_integrable_radius e
    exact aux_integrable_wienerEnvelope_of_integrable' hH.1 zero_lt_one
      (norm_nonneg e.toContinuousLinearMap) hH.2
  have hfun : (fun uv => F (A uv)) = P := by
    funext uv
    change H (e (e.symm ((ContinuousLinearMap.pi π) uv))) = _
    rw [e.apply_symm_apply]
    rfl
  obtain ⟨hSlices, hG, hGbound⟩ := hA_bound F hF
  have hFbound : (∫ z, wienerEnvelope F 1 z) ≤
      Ce * ∫ x, wienerEnvelope H 1 x := by
    simpa [F] using hCe H hH
  have hHbound : (∫ x, wienerEnvelope H 1 x) ≤
      ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by
    simpa [H] using fintype_tensor_wienerNorm_le hf
  have hGfun : (fun u : EuclideanSpace ℝ (Fin m) => ∫ v, F (A (u, v))) =
      fun u => ∫ v, P (u, v) := by
    funext u
    congr with v
    exact congrFun hfun (u, v)
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hs := hSlices u
    have hslice_eq : (fun v : EuclideanSpace ℝ (Fin l) => F (A (u, v))) =
        fun v => P (u, v) := by
      funext v
      exact congrFun hfun (u, v)
    rw [hslice_eq] at hs
    simpa only [P] using hs.1
  · rw [hGfun] at hG
    simpa only [P] using hG
  · calc
      (∫ u, wienerEnvelope (fun u : EuclideanSpace ℝ (Fin m) =>
          ∫ v, ∏ i, f i (π i (u, v))) 1 u) =
          ∫ u, wienerEnvelope (fun u : EuclideanSpace ℝ (Fin m) =>
            ∫ v, F (A (u, v))) 1 u := by rw [hGfun]
      _ ≤ C₂ * ∫ z, wienerEnvelope F 1 z := hGbound
      _ ≤ C₂ * (Ce * ∫ x, wienerEnvelope H 1 x) :=
        mul_le_mul_of_nonneg_left hFbound hC₂_pos.le
      _ ≤ C₂ * (Ce * ∏ i, ∫ x, wienerEnvelope (f i) 1 x) := by
        gcongr
      _ = (C₂ * Ce) * ∏ i, ∫ x, wienerEnvelope (f i) 1 x := by ring
end Auto
