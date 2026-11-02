-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_KilledResolventRootProofCleanV5
-- name    : MarkovProcess_V3HRepair_KilledResolventRootProofCleanV5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T11:35:49.781654+00:00
-- url     : https://prove2.me/theorems/2d3ee1ae-e3e4-42a7-8bbc-5d97d1f492d1
-- title:
--   Verified MarkovProcess source repair: KilledResolventRootProofCleanV5
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess KilledResolventRootProofCleanV5 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.KilledResolventRootProofCleanV5 source SHA-256 2d0b0eaf036ef6cea6ea95c443807d3dbe38c4bbb03d3abb259a91e39c160d3c. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names.

import Mathlib
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

theorem solution
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
  have hEq : IsConservative.feynmanKacResolventReal P hP q lam f = Y lam f := by
    apply MarkovProcess.perturbed_eq_of_resolventFamilies
      (fun mu ↦ P.kernelResolventReal mu)
      (fun mu ↦ IsConservative.feynmanKacResolventReal P hP q mu) Y
    · intro mu _hCmu hmu g k hgm hgk hgmBound hgkBound
      obtain ⟨E, hgE⟩ := hgmBound
      obtain ⟨F, hkF⟩ := hgkBound
      exact P.kernelResolventReal_add hmu hgm hgk hgE hkF
    · intro mu _hCmu hmu g hg E hgE
      exact P.norm_kernelResolventReal_le hmu hgE
    · exact hq
    · exact hq0
    · exact hqC
    · intro mu hmu g k hgm hgk hgmBound hgkBound
      obtain ⟨E, hgE⟩ := hgmBound
      obtain ⟨F, hkF⟩ := hgkBound
      exact IsConservative.feynmanKacResolventReal_add P hP hq hq0 hmu hgm hgk hgE hkF
    · intro mu _hmu g hg _hgb
      exact IsConservative.measurable_feynmanKacResolventReal P hP hq mu hg
    · exact hY_meas
    · intro mu hmu g _hg E hgE
      exact IsConservative.norm_feynmanKacResolventReal_le P hP hq0 hmu hgE
    · exact hY_bound
    · intro mu nu hmu hnu g hg hgb
      obtain ⟨E, hgE⟩ := hgb
      exact hFeller.feynmanKacResolventReal_resolvent_identity
        P hP hK hq hq0 hqC hmu hnu hg hgE
    · exact hY_resolvent
    · intro mu _hCmu hmu g hg hgb
      obtain ⟨E, hgE⟩ := hgb
      exact hFeller.feynmanKacResolventReal_perturbation
        P hP hK hq hq0 hqC hmu hg hgE
    · intro mu hCmu _hmu
      exact hY_perturbation hCmu
    · exact hlam
    · exact hf
    · exact hfD
  calc
    IsConservative.killedResolvent P hP U hU lam
        (fun y ↦ ENNReal.ofReal (f y)) x ≤
        IsConservative.feynmanKacResolvent P hP q lam
          (fun y ↦ ENNReal.ofReal (f y)) x :=
      IsConservative.killedResolvent_le_feynmanKacResolvent
        P hP hq hU hqU lam hf.ennreal_ofReal x
    _ = ENNReal.ofReal (IsConservative.feynmanKacResolventReal P hP q lam f x) :=
      (IsConservative.ofReal_feynmanKacResolventReal_eq_feynmanKacResolvent
        P hP hq hq0 hlam hf hf0 hfD x).symm
    _ = ENNReal.ofReal (Y lam f x) := by rw [hEq]

#print axioms solution


