-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_MiracleFlat
-- name    : Formalism_PeriodIntegrals_MiracleFlat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:51.73982+00:00
-- url     : https://prove2.me/theorems/998f904c-dcd6-4c76-b3eb-f08fd6feacc7
-- title:
--   Miracle Flat
-- statement:
--   Definitions and structural lemmas for Miracle Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/MiracleFlat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PI
def MiracleFlat : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsRegularLocalRing A]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] [IsLocalHom (algebraMap A B)],
    (∃ rs : List B, RingTheory.Sequence.IsRegular B rs ∧
      (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal B) ∧
      (rs.length : WithBot ℕ∞) = ringKrullDim B) →
    ringKrullDim B = ringKrullDim A +
      ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) →
    Module.Flat A B
end PI


