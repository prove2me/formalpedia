-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:14:22.409043+00:00
-- url     : https://prove2.me/theorems/31f35473-74cb-4af7-98fd-d898e7174727
-- title:
--   Mem Span LPow SIff
-- statement:
--   Definitions and structural lemmas for Mem Span LPow SIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
namespace GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
end GlobalTheory.BK
namespace GlobalTheory.BK
end GlobalTheory.BK


