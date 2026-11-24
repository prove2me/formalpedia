-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:52.633857+00:00
-- url     : https://prove2.me/theorems/3b4e4335-c02a-47c0-b2c6-2a80398c0404
-- title:
--   Cont Diff And Fderiv Tsum Fourier Of Rapid
-- statement:
--   Definitions and structural lemmas for Cont Diff And Fderiv Tsum Fourier Of Rapid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
namespace GlobalTheory
namespace RapidFourier
noncomputable def linForm {n : ℕ} (ν : Fin n → ℤ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ k, (ν k : ℝ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k
noncomputable def wave (a : ℂ) (t : ℝ) : ℂ := a * cexp (2 * π * I * t)
end RapidFourier
end GlobalTheory


