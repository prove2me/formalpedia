-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:40.035986+00:00
-- url     : https://prove2.me/theorems/76c7d692-aea9-4786-a1e1-ad9be37705ba
-- title:
--   St Auslander Buchsbaum Proj Dim Upper
-- statement:
--   Definitions and structural lemmas for St Auslander Buchsbaum Proj Dim Upper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StAuslanderBuchsbaumProjDimUpper.lean

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
open IsLocalRing CategoryTheory RingTheory.Sequence
universe u
def AuslanderBuchsbaumProjDimUpper.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (n d : ℕ) (ms : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) n →
    (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
    (∀ r ∈ ms, r ∈ maximalIdeal R) → IsWeaklyRegular M ms →
      HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length)
end GroundTheory.Heights₂.Heights


