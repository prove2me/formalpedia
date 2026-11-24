-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsZLocDenominators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:09.345876+00:00
-- url     : https://prove2.me/theorems/82cebb1c-9a48-4ada-9666-2ea740cf81c5
-- title:
--   Statements ZLoc Denominators
-- statement:
--   Definitions and structural lemmas for Statements ZLoc Denominators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsZLocDenominators.lean

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
def ZLocDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (U : X.Opens), IsAffineOpen U →
    ∀ b : Γ(baseChange f (ZLoc p), baseChangeMap f (ZLoc p) ⁻¹ᵁ U),
      ∃ N : ℕ, 0 < N ∧ ¬ (p : ℕ) ∣ N ∧ ∃ c : Γ(X, U), (baseChangeMap f (ZLoc p)).app U c = N • b
end
end GroundTheory.Heights₂.Heights.Model


