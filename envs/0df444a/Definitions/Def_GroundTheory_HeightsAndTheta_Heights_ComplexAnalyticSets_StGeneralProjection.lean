-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGeneralProjection
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGeneralProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:33.511684+00:00
-- url     : https://prove2.me/theorems/5595145a-ba73-4a73-99e4-f75b724e3047
-- title:
--   St General Projection
-- statement:
--   Definitions and structural lemmas for St General Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGeneralProjection.lean

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
open Matrix
noncomputable section
def GeneralProjection.Statement : Prop :=
  ∀ (n d m : ℕ) (L : Fin m → (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)), (∀ b, Function.Injective (L b)) →
    ∃ π : Matrix (Fin d) (Fin n) ℂ, ∀ b, Function.Injective fun v => π *ᵥ L b v
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


