-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__NormalCompletionSt_1c1e7efdcd667420
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__NormalCompletionSt_1c1e7efdcd667420
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:38.182489+00:00
-- url     : https://prove2.me/theorems/bce18276-7fdb-43df-8cc3-fd671d911f5b
-- title:
--   Normal Completion St
-- statement:
--   Definitions and structural lemmas for Normal Completion St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/NormalCompletionSt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace GlobalTheory.Published
def NormalCompletionSt : Prop :=
  ∀ (V B : Type) [CommRing V] [IsDedekindDomain V] [CharZero V] [CommRing B] [IsLocalRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra V B] [Algebra.EssFiniteType V B],
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal B) B)
end GlobalTheory.Published


