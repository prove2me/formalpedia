-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_IsArtinianRingKummerAdjoinRootQuotientRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:38.895712+00:00
-- url     : https://prove2.me/theorems/3742b156-3f80-46e3-851d-60a6b75cd65d
-- title:
--   Is Artinian Ring Kummer Adjoin Root Quotient Root
-- statement:
--   Definitions and structural lemmas for Is Artinian Ring Kummer Adjoin Root Quotient Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/IsArtinianRingKummerAdjoinRootQuotientRoot.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_LaEqSqrtSmulLam
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_HasElemDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.CompanionTheory.SplitRow.IdxV
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def ball (c : k) : AddSubgroup k := (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulRight c)
variable {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]
end GlobalTheory.CompanionTheory.SplitRow.IdxV


