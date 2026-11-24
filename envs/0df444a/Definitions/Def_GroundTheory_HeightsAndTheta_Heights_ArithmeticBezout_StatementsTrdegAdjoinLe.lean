-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegAdjoinLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:17.326972+00:00
-- url     : https://prove2.me/theorems/3c2967fb-8831-485c-a429-48b2ca51bbdb
-- title:
--   Statements Trdeg Adjoin Le
-- statement:
--   Definitions and structural lemmas for Statements Trdeg Adjoin Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsTrdegAdjoinLe.lean

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
def TrdegAdjoinLe.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (s : Set Ω) (ι : Type) [Fintype ι] (t : ι → Ω)
    (ι' : Type) (w : ι' → Ω), (∀ i, IsAlgebraic (Algebra.adjoin K (s ∪ Set.range t)) (w i)) →
      Algebra.trdeg K (Algebra.adjoin K (Set.range w)) ≤
        Algebra.trdeg K (Algebra.adjoin K s) + Fintype.card ι
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


