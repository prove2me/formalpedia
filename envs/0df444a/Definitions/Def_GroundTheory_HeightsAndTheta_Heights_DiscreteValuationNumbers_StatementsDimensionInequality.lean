-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequality
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDimensionInequality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:22.762622+00:00
-- url     : https://prove2.me/theorems/390a43f4-d979-4b0a-84c1-54db4263b0df
-- title:
--   Statements Dimension Inequality
-- statement:
--   Definitions and structural lemmas for Statements Dimension Inequality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsDimensionInequality.lean

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
universe u v
def DimensionInequality.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B], Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B
end GroundTheory.Heights₂.Heights.NumbersDVR


