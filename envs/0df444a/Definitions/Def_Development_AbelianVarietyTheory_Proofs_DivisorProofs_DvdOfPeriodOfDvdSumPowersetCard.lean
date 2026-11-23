-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:14.544374+00:00
-- url     : https://prove2.me/theorems/56b25127-44a6-4d2e-856d-1eadf1ecddbe
-- title:
--   Dvd Of Period Of Dvd Sum Powerset Card
-- statement:
--   Definitions and structural lemmas for Dvd Of Period Of Dvd Sum Powerset Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
namespace GlobalTheory
namespace PeriodDvd
def killed (d : ℕ) [NeZero d] (s : ℕ) : Finset (ZMod d) :=
  Finset.univ.filter fun x => s • x = 0
end PeriodDvd
end GlobalTheory


