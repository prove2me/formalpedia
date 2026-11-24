-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlueTwo
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlueTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:53.781241+00:00
-- url     : https://prove2.me/theorems/91cacac2-18a8-48b1-94af-fff73dd5897f
-- title:
--   Statements Glue Two
-- statement:
--   Definitions and structural lemmas for Statements Glue Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGlueTwo.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
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
def GlueTwo.Statement : Prop :=
  ∀ (X : Scheme.{0}) (O₁ O₂ O O₁₂ : X.Opens) (h₁ : O₁ ≤ O) (h₂ : O₂ ≤ O), O ≤ O₁ ⊔ O₂ →
    ∀ (k₁ : O₁₂ ≤ O₁) (k₂ : O₁₂ ≤ O₂), O₁ ⊓ O₂ ≤ O₁₂ →
    ∀ (F₁ : (O₁ : Scheme.{0}).Modules) (F₂ : (O₂ : Scheme.{0}).Modules)
      (ψ : (Scheme.Modules.pullback (X.homOfLE k₁)).obj F₁ ≅
        (Scheme.Modules.pullback (X.homOfLE k₂)).obj F₂),
    ∃ (F : (O : Scheme.{0}).Modules) (e₁ : (Scheme.Modules.pullback (X.homOfLE h₁)).obj F ≅ F₁)
      (e₂ : (Scheme.Modules.pullback (X.homOfLE h₂)).obj F ≅ F₂),
      pullbackCompIso (X.homOfLE_homOfLE k₂ h₂) e₂ =
        pullbackCompIso (X.homOfLE_homOfLE k₁ h₁) e₁ ≪≫ ψ
end
end GroundTheory.Heights₂.Heights.Model


