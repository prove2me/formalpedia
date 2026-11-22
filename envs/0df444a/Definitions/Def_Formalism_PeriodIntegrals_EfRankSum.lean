-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_EfRankSum
-- name    : Formalism_PeriodIntegrals_EfRankSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:42:37.83634+00:00
-- url     : https://prove2.me/theorems/870bc1fb-2385-48ad-b37e-411417cc6be7
-- title:
--   Ef Rank Sum
-- statement:
--   Definitions and structural lemmas for Ef Rank Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/EfRankSum.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open Formalism.MainNotions.Gaps.EtaleWeightGaps
def EfRankSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    Finite (Pts O A) ∧ (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank K A
end PI


