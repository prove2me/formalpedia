-- Prove2me | solution 1 for Auto.aux_memW0_comp_finAddEquivProd_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:27.299943+00:00
-- url     : https://prove2.me/submissions/85ff3dff-6a59-4b2b-91ae-105b058e699d

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerEnvelope_nonneg
public import Theorems.Thm_Auto_aux_wienerEnvelope_comp_continuousLinearMap_le
public import Theorems.Thm_Auto_aux_integrable_wienerEnvelope_of_integrable
public import Theorems.Thm_Auto_aux_finAdd_measurePreserving

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {n m : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] {f : EuclideanSpace ℝ (Fin (n + m)) → 𝕜}
    (hf : MemW0 f) :
    MemW0 (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      f (EuclideanSpace.finAddEquivProd.symm p)) := by
  let E := EuclideanSpace ℝ (Fin (n + m))
  let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
  let e : E ≃L[ℝ] P := EuclideanSpace.finAddEquivProd
  let g : P →L[ℝ] E := e.symm.toContinuousLinearMap
  let F : P → 𝕜 := fun p => f (g p)
  have hF : Continuous F := hf.1.comp g.continuous
  change MemW0 F
  refine ⟨hF, ?_⟩
  have hrad : Integrable (wienerEnvelope f ‖g‖) :=
    aux_integrable_wienerEnvelope_of_integrable hf.1 zero_lt_one (norm_nonneg _) hf.2
  have hgmp : MeasurePreserving g := by
    dsimp [g, e]
    exact MeasurePreserving.symm
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).toHomeomorph.toMeasurableEquiv
      (aux_finAdd_measurePreserving n m)
  have hcomp : Integrable (wienerEnvelope f ‖g‖ ∘ g) :=
    hgmp.integrable_comp_of_integrable hrad
  refine hcomp.mono_nonneg (continuous_wienerEnvelope hF 1).aestronglyMeasurable
    (ae_of_all _ fun p => aux_wienerEnvelope_nonneg hF zero_le_one p)
    (ae_of_all _ fun p => ?_)
  exact aux_wienerEnvelope_comp_continuousLinearMap_le g hf.1 p
end Auto
