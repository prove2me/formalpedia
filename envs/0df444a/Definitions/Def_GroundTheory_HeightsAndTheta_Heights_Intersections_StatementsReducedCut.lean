-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:23.602265+00:00
-- url     : https://prove2.me/theorems/320ae1e7-20d0-447f-8d1f-6bd11c8b0145
-- title:
--   Statements Reduced Cut
-- statement:
--   Definitions and structural lemmas for Statements Reduced Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsReducedCut.lean

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
namespace GroundTheory.Heights₂.Heights.Inter
def ReducedCutLength.Statement : Prop :=
  ∀ (T : Type) [CommRing T] [IsNoetherianRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime],
    I.IsRadical → (∀ p ∈ I.minimalPrimes, x ∉ p) → Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes →
    Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (I ⊔ Ideal.span {x}))) =
      ∑ᶠ p ∈ I.minimalPrimes, Module.length (Localization.AtPrime Q)
        (LocalizedModule Q.primeCompl (T ⧸ (p ⊔ Ideal.span {x})))
end GroundTheory.Heights₂.Heights.Inter


