-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsUFD
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsUFD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:03.733709+00:00
-- url     : https://prove2.me/theorems/92cba2a8-d317-4c4e-bd16-2b55b03af2eb
-- title:
--   St Hol Germs UFD
-- statement:
--   Definitions and structural lemmas for St Hol Germs UFD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolGermsUFD.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
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
open Topology Filter
noncomputable section
def HolGermsUFD.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), UniqueFactorizationMonoid (holGerms w)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


