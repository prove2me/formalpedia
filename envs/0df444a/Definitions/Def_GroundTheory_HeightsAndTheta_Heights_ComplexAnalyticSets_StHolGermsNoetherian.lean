-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsNoetherian
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsNoetherian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:54.854902+00:00
-- url     : https://prove2.me/theorems/e0ff1f76-aaab-4064-8b0d-54cb2c2703c3
-- title:
--   St Hol Germs Noetherian
-- statement:
--   Definitions and structural lemmas for St Hol Germs Noetherian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StHolGermsNoetherian.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
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
def HolGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


