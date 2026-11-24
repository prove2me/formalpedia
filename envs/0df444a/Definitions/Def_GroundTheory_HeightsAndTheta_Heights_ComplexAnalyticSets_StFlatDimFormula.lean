-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatDimFormula
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatDimFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:07.108664+00:00
-- url     : https://prove2.me/theorems/d554e5ed-f1a5-470c-b2c3-caf47cceb783
-- title:
--   St Flat Dim Formula
-- statement:
--   Definitions and structural lemmas for St Flat Dim Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFlatDimFormula.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing
def FlatDimFormula.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


