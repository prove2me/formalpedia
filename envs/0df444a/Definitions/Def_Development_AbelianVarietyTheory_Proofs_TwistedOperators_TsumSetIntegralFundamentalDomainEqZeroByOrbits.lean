-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:01.676816+00:00
-- url     : https://prove2.me/theorems/4c897747-aa41-4f44-8a91-5f699981958f
-- title:
--   Tsum Set Integral Fundamental Domain Eq Zero By Orbits
-- statement:
--   Definitions and structural lemmas for Tsum Set Integral Fundamental Domain Eq Zero By Orbits, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace GlobalTheory
namespace OrbitUnfold
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
def pull (𝓕 : Set H) (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕
end OrbitUnfold
end GlobalTheory


