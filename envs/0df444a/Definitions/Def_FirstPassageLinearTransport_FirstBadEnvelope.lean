-- Prove2me | Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
-- name    : FirstPassageLinearTransport_FirstBadEnvelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:05:20.778929+00:00
-- url     : https://prove2.me/theorems/d9422232-29b8-59d9-ba0c-39488201e00c
-- title:
--   First Bad Envelope
-- statement:
--   Definitions and structural lemmas for First Bad Envelope, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
def landingBand (q : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ (q - 1)) (2 ^ q)
noncomputable def landingBad (q : ℕ) (t : ℝ) : Finset ℕ := by
  classical
  exact (landingBand q).filter fun y => y ∉ initialWindowGood t
noncomputable def firstBadLandingEnvelope
    (M L U H : ℕ) (r : ℚ) (t : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc L U).biUnion fun q =>
    lossFilteredTransportedSources M (2 ^ q) H (landingBad q t)
      (((q + 2 : ℕ) : ℚ) / r)
def HasGeneratedFirstBadLanding
    (r : ℚ) (t : ℝ) (n L U H : ℕ) : Prop :=
  ∃ h q : ℕ, L ≤ q ∧ q ≤ U ∧ 1 ≤ h ∧ h ≤ H ∧
    CertifiedRankChain r n h q ∧ orbit h n ∈ landingBad q t
noncomputable def generatedFirstBadSources
    (M L U H : ℕ) (r : ℚ) (t : ℝ) : Finset ℕ := by
  classical
  exact (dyadicShell M).filter fun n =>
    HasGeneratedFirstBadLanding r t n L U H
end
end FirstPassageLinearTransport


