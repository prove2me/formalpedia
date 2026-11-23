-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:41.254409+00:00
-- url     : https://prove2.me/theorems/7e7ddf6c-308a-48ba-bd58-c764736acbd5
-- title:
--   Dvd Of Forall Sub Mul Mem
-- statement:
--   Definitions and structural lemmas for Dvd Of Forall Sub Mul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.CoeffSubring
section Basis
variable {k : Type} [Field k] {p : ℕ} {B : Set k}
end Basis
variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)
def level (n : ℕ) : Subring S :=
  Subring.closure (Set.range (fun x : S => x ^ p ^ n) ∪ L ∪ (maximalIdeal S ^ (n + 1) : Ideal S))
variable {p L}
end GlobalTheory.CoeffSubring


