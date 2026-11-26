-- Prove2me | solution 1 for Auto.MemW0.aux_comp_injective_continuousLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:48:40.220672+00:00
-- url     : https://prove2.me/submissions/1a88b04a-85a5-4d92-85ed-11d41da38340

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearMap_of_measurePreserving
public import Theorems.Thm_Auto_MemW0_aux_comp_continuousLinearEquiv_between_of_integrable_radius
public import Theorems.Thm_Auto_aux_orthogonalDecomposition_range_apply
public import Theorems.Thm_P2M_Auto_aux_integrable_wienerEnvelope_of_integrable__1e1fced5a7d3
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice_snd_of_addHaar

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {k n : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin n) → 𝕜} (hf : MemW0 f)
    (π : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    MemW0 (f ∘ π) := by
  let s : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := π.range
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] s × sᗮ :=
    s.orthogonalDecomposition.toContinuousLinearEquiv.trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ)
  let F : s × sᗮ → 𝕜 := f ∘ e.symm
  have hF : MemW0 F := by
    have he : MeasurePreserving e := by
      let e₁ : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] WithLp 2 (s × sᗮ) :=
        s.orthogonalDecomposition
      let e₂ : WithLp 2 (s × sᗮ) ≃L[ℝ] s × sᗮ :=
        WithLp.prodContinuousLinearEquiv 2 ℝ s sᗮ
      change MeasurePreserving (e₂ ∘ e₁)
      exact (WithLp.volume_preserving_ofLp s sᗮ).comp e₁.measurePreserving
    have he_symm : MeasurePreserving e.symm :=
      MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv he
    apply hf.aux_comp_continuousLinearMap_of_measurePreserving e.symm.toContinuousLinearMap he_symm
    exact aux_integrable_wienerEnvelope_of_integrable hf.1 zero_lt_one
      (norm_nonneg e.symm.toContinuousLinearMap) hf.2
  have hS : MemW0 (fun q : s ↦ F (q, 0)) :=
    hF.aux_memW0_slice_snd_of_addHaar 0
  let q : EuclideanSpace ℝ (Fin k) ≃L[ℝ] s :=
    π.equivRange hπ π.range.closed_of_finiteDimensional
  have hq : MemW0 (fun x : EuclideanSpace ℝ (Fin k) ↦ F (q x, 0)) := by
    apply hS.aux_comp_continuousLinearEquiv_between_of_integrable_radius q
    exact aux_integrable_wienerEnvelope_of_integrable' hS.1 zero_lt_one
      (norm_nonneg q.toContinuousLinearMap) hS.2
  have hfun : (fun x : EuclideanSpace ℝ (Fin k) ↦ F (q x, 0)) = f ∘ π := by
    funext x
    have hcoord : e (π x) = (q x, 0) := by
      rw [aux_orthogonalDecomposition_range_apply π x]
      apply Prod.ext
      · change π.rangeRestrict x = (π.equivRange hπ π.range.closed_of_finiteDimensional) x
        exact congrFun (π.coe_equivRange hπ π.range.closed_of_finiteDimensional).symm x
      · rfl
    change f (e.symm (q x, 0)) = f (π x)
    rw [← hcoord, e.symm_apply_apply]
  rwa [hfun] at hq
end MemW0
end Auto
