-- Prove2me | solution 1 for Auto.Integrable.aux_comp_add_right_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:08.030135+00:00
-- url     : https://prove2.me/submissions/c8d66dd0-a87e-4c31-8097-6579932c1af3

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
namespace Integrable
theorem _root_.solution {m l : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : Integrable f) (z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l)) :
    Integrable (fun x ↦ f (x + z)) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  have htrans : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin l) ↦ x + z) (volume.prod volume) (volume.prod volume) := by
    convert MeasurePreserving.prod
      (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin m))) z.1)
      (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin l))) z.2) using 1
    ext x <;> rfl
  simpa only [Function.comp_def] using htrans.integrable_comp_of_integrable hf
end Integrable
end Auto
