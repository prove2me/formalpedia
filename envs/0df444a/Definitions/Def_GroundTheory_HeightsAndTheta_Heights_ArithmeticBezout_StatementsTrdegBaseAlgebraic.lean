-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:38.141485+00:00
-- url     : https://prove2.me/theorems/5039dc95-83a9-4269-907d-b9e1a1e23e91
-- title:
--   Statements Trdeg Base Algebraic
-- statement:
--   Definitions and structural lemmas for Statements Trdeg Base Algebraic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsTrdegBaseAlgebraic.lean

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
namespace GroundTheory.Heights₂.Heights
noncomputable section
def TrdegBaseAlgebraic.Statement : Prop :=
  ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra K Ω] [Algebra F Ω]
    [IsScalarTower F K Ω], Algebra.IsAlgebraic F K → ∀ (ι : Type) (z : ι → Ω),
      Algebra.trdeg K (Algebra.adjoin K (Set.range z)) ≤ Algebra.trdeg F (Algebra.adjoin F (Set.range z))
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


