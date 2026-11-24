-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:44.040782+00:00
-- url     : https://prove2.me/theorems/7d234195-a3b7-4138-9058-cddc867dd37c
-- title:
--   St Generic Freeness
-- statement:
--   Definitions and structural lemmas for St Generic Freeness, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFreeness.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
universe u v w
def GenericFreeness.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M],
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)
end GroundTheory.Heights₂.Heights


