-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRankDeficientFibreInfinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:37.248664+00:00
-- url     : https://prove2.me/theorems/811d6ddb-29b7-485a-89a5-c18a556bae2c
-- title:
--   St Rank Deficient Fibre Infinite
-- statement:
--   Definitions and structural lemmas for St Rank Deficient Fibre Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRankDeficientFibreInfinite.lean

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
open Topology Metric
def RankDeficientFibreInfinite.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ),
    IsOpen U → U.Nonempty → DifferentiableOn ℂ f U →
    (∀ v ∈ U, ¬ Function.Injective (fderiv ℂ f v)) →
      ∃ y : Fin m → ℂ, {t | t ∈ U ∧ f t = y}.Infinite
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


