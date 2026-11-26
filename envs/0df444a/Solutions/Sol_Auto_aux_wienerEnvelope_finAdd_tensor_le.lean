-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_finAdd_tensor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:00.596074+00:00
-- url     : https://prove2.me/submissions/ac008573-6426-4a56-9859-b59007db9d6a

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_norm_le_wienerEnvelope_of_mem_closedBall
public import Theorems.Thm_Auto_aux_norm_finAdd_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : Continuous f) (hg : Continuous g) (z : EuclideanSpace ℝ (Fin (n + m))) :
    wienerEnvelope (fun w : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd w).1 * g (EuclideanSpace.finAddEquivProd w).2) 1 z ≤
      wienerEnvelope (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) ↦
        f p.1 * g p.2) 1 (EuclideanSpace.finAddEquivProd z) := by
  let e : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let H : EuclideanSpace ℝ (Fin (n + m)) → 𝕜 := fun w ↦ f (e w).1 * g (e w).2
  let P : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → 𝕜 := fun p ↦ f p.1 * g p.2
  have hP : Continuous P := (hf.comp continuous_fst).mul (hg.comp continuous_snd)
  change wienerEnvelope H 1 z ≤ wienerEnvelope P 1 (e z)
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨w, hw, rfl⟩
  change ‖H (z + w)‖ ≤ _
  have hw' : e w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, e] using (aux_norm_finAdd_le w).trans
      (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)
  have headd : e (z + w) = e z + e w := by
    exact (EuclideanSpace.finAddEquivProd :
      EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)).map_add z w
  rw [show H (z + w) = P (e (z + w)) by rfl, headd]
  apply aux_norm_le_wienerEnvelope_of_mem_closedBall hP
  simpa [Metric.mem_closedBall, dist_eq_norm] using hw'
end Auto
