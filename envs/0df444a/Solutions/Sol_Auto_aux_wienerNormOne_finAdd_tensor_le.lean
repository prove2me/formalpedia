-- Prove2me | solution 1 for Auto.aux_wienerNormOne_finAdd_tensor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:28.262736+00:00
-- url     : https://prove2.me/submissions/1319d3f1-0003-4be1-968a-34a1e0c070ea

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_continuous_wienerEnvelope
public import Theorems.Thm_Auto_aux_wienerNormOne_mul_prod_le
public import Theorems.Thm_Auto_aux_finAdd_measurePreserving
public import Theorems.Thm_Auto_aux_wienerEnvelope_finAdd_tensor_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : Continuous f) (hg : Continuous g) :
    wienerNormOne (fun z : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd z).1 * g (EuclideanSpace.finAddEquivProd z).2) ≤
      wienerNormOne f * wienerNormOne g := by
  let e : EuclideanSpace ℝ (Fin (n + m)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let H : EuclideanSpace ℝ (Fin (n + m)) → 𝕜 := fun z ↦ f (e z).1 * g (e z).2
  let P : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → 𝕜 := fun p ↦ f p.1 * g p.2
  have hP : Continuous P := (hf.comp continuous_fst).mul (hg.comp continuous_snd)
  change wienerNormOne H ≤ wienerNormOne f * wienerNormOne g
  calc
    wienerNormOne H ≤ wienerNormOne P := by
      unfold wienerNormOne wienerNorm
      calc
        (∫⁻ z, ENNReal.ofReal (wienerEnvelope H 1 z)) ≤
            ∫⁻ z, ENNReal.ofReal (wienerEnvelope P 1 (e z)) := by
          apply lintegral_mono
          intro z
          exact ENNReal.ofReal_le_ofReal (aux_wienerEnvelope_finAdd_tensor_le hf hg z)
        _ = ∫⁻ p, ENNReal.ofReal (wienerEnvelope P 1 p) :=
          (aux_finAdd_measurePreserving n m).lintegral_comp
            (ENNReal.continuous_ofReal.measurable.comp (continuous_wienerEnvelope hP 1).measurable)
    _ ≤ wienerNormOne f * wienerNormOne g := aux_wienerNormOne_mul_prod_le hf hg
end Auto
