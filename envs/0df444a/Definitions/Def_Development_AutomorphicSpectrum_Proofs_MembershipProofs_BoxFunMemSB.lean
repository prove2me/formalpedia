-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoxFunMemSB
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_BoxFunMemSB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:49.482603+00:00
-- url     : https://prove2.me/theorems/2bb198da-e666-45ac-bcc3-c897d9fa0284
-- title:
--   Box Fun Mem SB
-- statement:
--   Definitions and structural lemmas for Box Fun Mem SB, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/BoxFunMemSB.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.VacDbl
section
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
end
end GlobalTheory.CompanionTheory.VacDbl


