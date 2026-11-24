-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:03.3931+00:00
-- url     : https://prove2.me/theorems/4995f125-9789-4d39-95ce-2276f5ec98fb
-- title:
--   Rat Local Affine
-- statement:
--   Definitions and structural lemmas for Rat Local Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/RatLocalAffine.lean

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
def RatLocalAffine.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [Flat f] (U : X.Opens), IsAffineOpen U →
    Function.Injective ((baseChangeMap f ℚ).app U) ∧
      ∀ b : Γ(baseChange f ℚ, baseChangeMap f ℚ ⁻¹ᵁ U),
        ∃ N : ℕ, 0 < N ∧ ∃ a : Γ(X, U), (baseChangeMap f ℚ).app U a = N • b
end
end GroundTheory.Heights₂.Heights.Model


