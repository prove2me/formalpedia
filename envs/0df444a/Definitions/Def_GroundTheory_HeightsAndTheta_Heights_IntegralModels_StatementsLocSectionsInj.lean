-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:20.357352+00:00
-- url     : https://prove2.me/theorems/299a16e4-4bdf-46f9-86ca-cec0f4dbe89f
-- title:
--   Statements Loc Sections Inj
-- statement:
--   Definitions and structural lemmas for Statements Loc Sections Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsLocSectionsInj.lean

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
def LocSectionsInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes),
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ k : ℤ, ¬ ((p : ℕ) : ℤ) ∣ k → (m : ℤ) ∣ k →
      ∀ W : X.Opens, W ≤ invOpen f k →
        Function.Injective ((baseChangeMap f (ZLoc p)).app W)
end
end GroundTheory.Heights₂.Heights.Model


