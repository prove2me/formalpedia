-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:22.634804+00:00
-- url     : https://prove2.me/theorems/256b0d90-6ea0-4b8f-a42d-332847fba70f
-- title:
--   Statements Iso Glue Two
-- statement:
--   Definitions and structural lemmas for Statements Iso Glue Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsIsoGlueTwo.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlueTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry
noncomputable section
def IsoGlueTwo.Statement : Prop :=
  ∀ (Y : Scheme.{0}) (P₁ P₂ P P₁₂ : Y.Opens) (h₁ : P₁ ≤ P) (h₂ : P₂ ≤ P), P ≤ P₁ ⊔ P₂ →
    ∀ (k₁ : P₁₂ ≤ P₁) (k₂ : P₁₂ ≤ P₂), P₁ ⊓ P₂ ≤ P₁₂ →
    ∀ (A B : (P : Scheme.{0}).Modules)
      (φ₁ : (Scheme.Modules.pullback (Y.homOfLE h₁)).obj A ≅ (Scheme.Modules.pullback (Y.homOfLE h₁)).obj B)
      (φ₂ : (Scheme.Modules.pullback (Y.homOfLE h₂)).obj A ≅ (Scheme.Modules.pullback (Y.homOfLE h₂)).obj B),
    pullbackIsoAlong (Y.homOfLE_homOfLE k₁ h₁) φ₁ = pullbackIsoAlong (Y.homOfLE_homOfLE k₂ h₂) φ₂ →
    ∃ φ : A ≅ B, (Scheme.Modules.pullback (Y.homOfLE h₁)).mapIso φ = φ₁ ∧
      (Scheme.Modules.pullback (Y.homOfLE h₂)).mapIso φ = φ₂
end
end GroundTheory.Heights₂.Heights.Model


