-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_ConditionalExpectationBridgeCleanV1
-- name    : MarkovProcess_V3HRepair_ConditionalExpectationBridgeCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T09:45:00.171541+00:00
-- url     : https://prove2.me/theorems/ffbf882f-1c15-4af8-9a49-21d183ee5c9d
-- title:
--   Verified MarkovProcess source repair: ConditionalExpectationBridgeCleanV1
-- statement:
--   A conditional-expectation identity expresses integrals of a measurable future kernel after restricting the observed coordinates.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; source-faithful adapted axiom-clean proof module V3HRepaired.ConditionalExpectationBridgeCleanV1, archived SHA-256 48d8fd7fb45223a00b5a44d1aca8ee00c6d364904c1dae6dd8c2ca24cff6e18b.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MarkovProcess

noncomputable section

variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- If the law of `Y` after restriction to every conditioning event is obtained by mixing
`kappa`, then integrating any bounded strongly measurable observable against `kappa` gives the
corresponding conditional expectation. -/
theorem condExp_comp_ae_eq_integral_kernel_of_restrict_map
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta) [IsMarkovKernel kappa]
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict A).map Y = kappa ∘ₘ (mu.restrict A))
    (F : beta → E) (hF : StronglyMeasurable F)
    (hFm : StronglyMeasurable[m] (fun omega ↦ ∫ y, F y ∂kappa omega))
    (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    mu[fun omega ↦ F (Y omega)|m] =ᵐ[mu]
      fun omega ↦ ∫ y, F y ∂kappa omega := by
  have hfMeas : AEStronglyMeasurable (fun omega ↦ F (Y omega)) mu :=
    (hF.comp_measurable hY).aestronglyMeasurable
  have hfInt : Integrable (fun omega ↦ F (Y omega)) mu :=
    Integrable.of_bound hfMeas C (ae_of_all _ fun omega ↦ hFC (Y omega))
  have hgMeas : AEStronglyMeasurable[m]
      (fun omega ↦ ∫ y, F y ∂kappa omega) mu :=
    hFm.aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq
    (m := m) (m₀ := mOmega) (μ := mu) hm hfInt ?_ ?_ hgMeas).symm
  · intro A _hA _hmuA
    exact Integrable.of_bound
      (hF.integral_kernel.aestronglyMeasurable.restrict)
      C (ae_of_all _ fun omega ↦ by
        simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
          norm_integral_le_of_norm_le_const
            (μ := kappa omega) (ae_of_all _ hFC))
  · intro A hA _hmuA
    have hFA : Integrable F ((mu.restrict A).map Y) := by
      rw [integrable_map_measure hF.aestronglyMeasurable hY.aemeasurable]
      exact hfInt.restrict
    have hFAComp : Integrable F (kappa ∘ₘ (mu.restrict A)) := by
      rw [← hJoint A hA]
      exact hFA
    rw [Measure.comp_eq_comp_const_apply] at hFAComp
    have hIntegralComp := Kernel.integral_comp hFAComp
    calc
      ∫ omega in A, (∫ y, F y ∂kappa omega) ∂mu =
          ∫ omega, (∫ y, F y ∂kappa omega) ∂(mu.restrict A) := rfl
      _ = ∫ y, F y ∂(kappa ∘ₘ (mu.restrict A)) :=
        by simpa only [Kernel.const_apply] using! hIntegralComp.symm
      _ = ∫ y, F y ∂((mu.restrict A).map Y) := by rw [hJoint A hA]
      _ = ∫ omega, F (Y omega) ∂(mu.restrict A) := by
        rw [integral_map hY.aemeasurable hF.aestronglyMeasurable]
      _ = ∫ omega in A, F (Y omega) ∂mu := rfl

end
end MarkovProcess

#print axioms MarkovProcess.condExp_comp_ae_eq_integral_kernel_of_restrict_map


