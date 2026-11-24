-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericPullInj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:04.788947+00:00
-- url     : https://prove2.me/theorems/f481423d-f8ee-4b49-b5a2-c4e2ffdbad0f
-- title:
--   Statements Generic Pull Inj
-- statement:
--   Definitions and structural lemmas for Statements Generic Pull Inj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGenericPullInj.lean

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
def GenericPullInj.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n →
      ∀ V : (invOpen f a : Scheme.{0}).Opens, V ≤ invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n) →
        Function.Injective
          (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V)
end
end GroundTheory.Heights₂.Heights.Model


