-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullInjLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:07.613795+00:00
-- url     : https://prove2.me/theorems/f6fe7b13-a49a-4ac7-9c89-439ec08f20c8
-- title:
--   Statements Pull Inj Loc
-- statement:
--   Definitions and structural lemmas for Statements Pull Inj Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsPullInjLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
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
def PullInjLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (G : (U : Scheme.{0}).Modules), IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ V : (U : Scheme.{0}).Opens, V ≤ invOpen (U.ι ≫ f) n →
        Function.Injective (pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) G V)
end
end GroundTheory.Heights₂.Heights.Model


