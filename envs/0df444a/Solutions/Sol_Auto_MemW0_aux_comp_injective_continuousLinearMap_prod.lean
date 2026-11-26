-- Prove2me | solution 1 for Auto.MemW0.aux_comp_injective_continuousLinearMap_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:37.356616+00:00
-- url     : https://prove2.me/submissions/1607c353-df5c-4bde-bc2e-0deb406f496e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_comp_injective_continuousLinearMap
public import Theorems.Thm_Auto_aux_memW0_comp_finAddEquivProd_symm

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution
    {m l n : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} (hf : MemW0 f)
    (π : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) →L[ℝ]
      EuclideanSpace ℝ (Fin n))
    (hπ : Function.Injective π) :
    MemW0 (fun uv => f (π uv)) := by
  let e : EuclideanSpace ℝ (Fin (m + l)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) :=
    EuclideanSpace.finAddEquivProd
  let A : EuclideanSpace ℝ (Fin (m + l)) →L[ℝ]
      EuclideanSpace ℝ (Fin n) := π.comp e.toContinuousLinearMap
  have hAinj : Function.Injective A := hπ.comp e.injective
  have hA : MemW0 (f ∘ A) := hf.aux_comp_injective_continuousLinearMap A hAinj
  have hP := aux_memW0_comp_finAddEquivProd_symm hA
  simpa [A, e, Function.comp_def] using hP
end MemW0
end Auto
