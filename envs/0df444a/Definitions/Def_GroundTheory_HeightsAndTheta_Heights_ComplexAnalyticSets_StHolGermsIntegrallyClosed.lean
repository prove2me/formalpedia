-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:00.90937+00:00
-- url     : https://prove2.me/theorems/ef7850ea-b0f3-4812-bbea-788f0feccb82
-- title:
--   St Hol Germs Integrally Closed
-- statement:
--   Definitions and structural lemmas for St Hol Germs Integrally Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolGermsIntegrallyClosed.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
def HolGermsIntegrallyClosed.Statement : Prop :=
  ∀ (d : ℕ) (y : Fin d → ℂ), IsDomain (holGerms y) ∧ IsIntegrallyClosed (holGerms y)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


