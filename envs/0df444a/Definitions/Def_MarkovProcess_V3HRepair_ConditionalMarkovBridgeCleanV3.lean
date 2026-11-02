-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ConditionalMarkovBridgeCleanV3
-- name    : MarkovProcess_V3HRepair_ConditionalMarkovBridgeCleanV3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:02:52.129191+00:00
-- url     : https://prove2.me/theorems/547f84d9-742f-4ba3-a3a5-2cfcad901267
-- title:
--   Verified MarkovProcess source repair: ConditionalMarkovBridgeCleanV3
-- statement:
--   The conditional Markov property is expressed as an almost-everywhere conditional-expectation kernel-integral identity using measurable restriction and restart maps.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.ConditionalMarkovBridgeCleanV3 source SHA-256 88320724d2297cae9d0042f05efb9cfdf2efa6c5f639b1edf3db1a0a485d2fc3. Only repaired-module import paths were converted to their new published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3HRepair_ConditionalExpectationBridgeCleanV1

open MeasureTheory
namespace MarkovProcess.ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
@[simp] theorem coordinateProcess_apply (t : NNReal) (omega : ContinuousPath alpha) :
    coordinateProcess t omega = omega t := rfl
/-- The time-`t` coordinate is measurable for the canonical filtration at time `t`. -/
theorem measurable_coordinateProcess_canonicalFiltration
    [MeasurableSpace alpha] [BorelSpace alpha] (t : NNReal) :
    Measurable[canonicalFiltration (alpha := alpha) t]
      (coordinateProcess (alpha := alpha) t) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t) le_rfl

end MarkovProcess.ContinuousPath
open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- An event-restricted whole-future restart identity gives the deterministic-time conditional
Markov formula for every bounded strongly measurable functional of the shifted path. -/
theorem condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (S : NNReal)
    (hRestart : ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift S omega)|canonicalFiltration (alpha := alpha) S] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega S) := by
  let kappa : Kernel (ContinuousPath alpha) (ContinuousPath alpha) :=
    Kernel.comap Q (coordinateProcess (alpha := alpha) S)
      (measurable_coordinateProcess S)
  let : IsMarkovKernel kappa := by
    dsimp only [kappa]
    infer_instance
  have hFm : StronglyMeasurable[canonicalFiltration (alpha := alpha) S]
      (fun omega ↦ ∫ eta, F eta ∂kappa omega) := by
    have hBase : StronglyMeasurable[canonicalFiltration (alpha := alpha) S]
        (fun omega ↦ ∫ eta, F eta ∂Q (omega S)) :=
      hF.integral_kernel.comp_measurable
        (measurable_coordinateProcess_canonicalFiltration S)
    simpa only [kappa, Kernel.comap_apply, coordinateProcess_apply] using hBase
  have h := condExp_comp_ae_eq_integral_kernel_of_restrict_map
    (Q x) kappa (shift S) (measurable_shift_fixed S)
    ((canonicalFiltration (alpha := alpha)).le S)
    (by simpa only [kappa] using hRestart) F hF hFm C hFC
  simpa only [kappa, Kernel.comap_apply, coordinateProcess_apply] using h

end
end ContinuousPath
end MarkovProcess

#print axioms MarkovProcess.ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map


