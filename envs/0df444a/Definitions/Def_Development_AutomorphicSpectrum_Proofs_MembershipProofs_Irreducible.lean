-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:30.66872+00:00
-- url     : https://prove2.me/theorems/3f180f3e-7749-4f3f-b689-17598bed9bc7
-- title:
--   Irreducible
-- statement:
--   Definitions and structural lemmas for Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/Irreducible.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FinHeis.Irred
open GlobalTheory.CompanionTheory.FinHeis
variable {X M : Type} [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (S : Sys X M)
end GlobalTheory.CompanionTheory.FinHeis.Irred


