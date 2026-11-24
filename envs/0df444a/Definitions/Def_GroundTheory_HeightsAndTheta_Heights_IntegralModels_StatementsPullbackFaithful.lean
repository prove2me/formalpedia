-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:04.103399+00:00
-- url     : https://prove2.me/theorems/5f2f20db-13eb-4ee8-9169-80eb3ed0f742
-- title:
--   Statements Pullback Faithful
-- statement:
--   Definitions and structural lemmas for Statements Pullback Faithful, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsPullbackFaithful.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
universe u
def PullbackFaithful.Statement : Prop :=
  ∀ (T U : Scheme.{u}) (g : T ⟶ U), (∀ W : U.Opens, Function.Injective (g.app W)) →
    ∀ (A B : U.Modules), IsVectorBundle B → ∀ ψ₁ ψ₂ : A ⟶ B,
      (Scheme.Modules.pullback g).map ψ₁ = (Scheme.Modules.pullback g).map ψ₂ → ψ₁ = ψ₂
end
end GroundTheory.Heights₂.Heights.Model


