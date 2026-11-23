-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:26.247744+00:00
-- url     : https://prove2.me/theorems/ea2128e7-1808-4063-8a7f-2e3191d108ec
-- title:
--   Tendsto Real Eisenstein Sub Pole
-- statement:
--   Definitions and structural lemmas for Tendsto Real Eisenstein Sub Pole, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoRealEisensteinSubPole.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
namespace GlobalTheory.KroneckerLimit
noncomputable def rowSum (a Y s : ℝ) : ℝ := ∑' n : ℤ, ((a + n) ^ 2 + Y ^ 2) ^ (-s)
noncomputable def rowError (x y : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  rowSum ((m + 1) * x) ((m + 1) * y) s - betaConst s * ((m + 1) * y) ^ (1 - 2 * s)
end GlobalTheory.KroneckerLimit
namespace GlobalTheory
open KroneckerLimit
end GlobalTheory


