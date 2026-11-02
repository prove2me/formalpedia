-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_KilledResolventExactCleanV1
-- name    : MarkovProcess_V3HRepair_KilledResolventExactCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:16:08.417926+00:00
-- url     : https://prove2.me/theorems/636eb0fd-17b5-4132-9988-97d5544dcd14
-- title:
--   Verified MarkovProcess source repair: KilledResolventExactCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess KilledResolventExactCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.KilledResolventExactCleanV1 source SHA-256 a160bdef1b42c2893cba3728514a60986139dcc4a8730533a35119daa3838cff. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets 2e5e10b9-786a-42e1-9090-c31006d4a270; these add no mathematical assumptions.

import Mathlib
import Definitions.Def_MarkovProcess_V3HRepair_KilledResolventRootProofCleanV5
import Definitions.Def_MarkovProcess_V3HRepair_ResolventProofs
import Definitions.Def_MarkovProcess_V3HRepair_ResolventUniquenessCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacJointMeasurableCleanV3
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacKilledDominationCleanV2
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacRealResolventCoreCleanV2
import Definitions.Def_MarkovProcess_V3HRepair_FeynmanKacFellerResolventCleanV10

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

noncomputable section
variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {q : alpha → ℝ} (hq : Measurable q)
    (hqU : ∀ y ∈ U, q y = 0) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (Y : ℝ → (alpha → ℝ) → alpha → ℝ)
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hY_perturbation : ∀ {lam : ℝ}, C < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = P.kernelResolventReal lam f -
        P.kernelResolventReal lam (fun y ↦ q y * Y lam f y))
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam (fun y ↦ ENNReal.ofReal (f y)) x ≤
      ENNReal.ofReal (Y lam f x) := by
  exact _root_.solution P hP hFeller hK hU hq hqU hq0 hqC Y hY_meas hY_bound hY_resolvent hY_perturbation hf hf0 hfD hlam x

#print axioms MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily

noncomputable def MarkovProcess.V3HRepairProof_2e5e10b9786a42e19090c31006d4a270 :=
  @MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.killedResolvent_le_of_perturbed_resolventFamily


