-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CharacterAugmentationSubspaceQuotientActionTop
-- name    : Development_AutomorphicSpectrum_Proofs_MembershipProofs_CharacterAugmentationSubspaceQuotientActionTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:16.822507+00:00
-- url     : https://prove2.me/theorems/07a1a92a-e056-4632-a229-649fbb39338b
-- title:
--   Character Augmentation Subspace Quotient Action Top
-- statement:
--   Definitions and structural lemmas for Character Augmentation Subspace Quotient Action Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.CompanionTheory.WittOrbit
section
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}
end
end GlobalTheory.CompanionTheory.WittOrbit


