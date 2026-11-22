-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
-- name    : Formalism_PeriodIntegrals_BallQuotLen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:19.218677+00:00
-- url     : https://prove2.me/theorems/bc5e0802-a9de-4325-8148-4600026fd0b9
-- title:
--   Ball Quot Len
-- statement:
--   Definitions and structural lemmas for Ball Quot Len, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/BallQuotLen.lean

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
def BallQuotLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    ∀ (V : Type) [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V] [Module O V]
      [IsScalarTower O A V] (e : V), IsGen A e → ∀ (c : Pts O A → ℤ) (m : Pts O A → ℕ),
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ᶠ ζ : Pts O A, m ζ * fdeg ζ : ℕ) : ℕ∞)
end PI


