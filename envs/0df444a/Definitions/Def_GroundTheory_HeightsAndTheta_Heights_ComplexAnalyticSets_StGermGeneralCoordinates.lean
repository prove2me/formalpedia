-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:58.402916+00:00
-- url     : https://prove2.me/theorems/cfa8e852-4f95-46ca-b3bf-cd2ef44c3957
-- title:
--   St Germ General Coordinates
-- statement:
--   Definitions and structural lemmas for St Germ General Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGermGeneralCoordinates.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
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
def GeneralLinearCoordinates.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (f : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → ¬ (∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0) →
    ∃ (A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ)) (d : ℕ),
      analyticOrderAt (fun t => f (A (pointWithLast 0 t))) 0 = d
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


