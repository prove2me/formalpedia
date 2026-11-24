-- Prove2me | Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
-- name    : GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:26.410419+00:00
-- url     : https://prove2.me/theorems/41baaebf-6e4a-495f-ba25-934aca4f817f
-- title:
--   Exists Max Minor Ne Zero Of Linear Independent Alt
-- statement:
--   Definitions and structural lemmas for Exists Max Minor Ne Zero Of Linear Independent Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/ExistsMaxMinorNeZeroOfLinearIndependentAlt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Variant₂.N1
def KSubset (n k : ℕ) : Type := { s : Finset (Fin n) // s.card = k }
def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n :=
  (s.1).orderEmbOfFin s.2
def maxMinor {R : Type*} [CommRing R] {n k : ℕ} (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : R :=
  (B.submatrix (⇑s.emb) id).det
end GroundTheory.Variant₂.N1


