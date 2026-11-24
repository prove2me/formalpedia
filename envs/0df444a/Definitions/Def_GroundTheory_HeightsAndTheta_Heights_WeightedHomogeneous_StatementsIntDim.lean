-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:04.41044+00:00
-- url     : https://prove2.me/theorems/5bef5629-64ef-4d21-b1ec-fe4f78bc3769
-- title:
--   Statements Int Dim
-- statement:
--   Definitions and structural lemmas for Statements Int Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/StatementsIntDim.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
noncomputable section
def IntDomainDim.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra ℤ A] [IsDomain A] [Algebra.FiniteType ℤ A],
    Function.Injective (algebraMap ℤ A) →
      ringKrullDim A = (((Algebra.trdeg ℤ A).toENat + 1 : ℕ∞) : WithBot ℕ∞)
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights


