-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:34.654794+00:00
-- url     : https://prove2.me/theorems/e7c2f2a1-6570-4423-983e-2e9088ed5482
-- title:
--   Hermitian Block Has Invariants Of Lift Match
-- statement:
--   Definitions and structural lemmas for Hermitian Block Has Invariants Of Lift Match, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftMatch.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
namespace GlobalTheory.JR.Step
section MapLemmas
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')
end MapLemmas
section Blocks
variable {r : ℕ} {k : Type} [CommRing k]
end Blocks
end GlobalTheory.JR.Step


