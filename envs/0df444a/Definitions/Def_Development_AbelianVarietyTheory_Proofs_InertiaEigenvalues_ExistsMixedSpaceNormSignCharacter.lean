-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:01.25281+00:00
-- url     : https://prove2.me/theorems/66befb66-49a4-4f7f-bc64-a95001d901ee
-- title:
--   Exists Mixed Space Norm Sign Character
-- statement:
--   Definitions and structural lemmas for Exists Mixed Space Norm Sign Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMixedSpaceNormSignCharacter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
namespace GlobalTheory.NormSign
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
noncomputable def snorm (x : mixedSpace K) : ℝ :=
  (∏ w, x.1 w) * ∏ w, ‖x.2 w‖ ^ 2
noncomputable def sgn (ε : ℂ) (t : ℝ) : ℂ := if 0 < t then 1 else if t < 0 then ε else 0
end GlobalTheory.NormSign


