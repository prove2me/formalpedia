-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
-- name    : GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:25.327807+00:00
-- url     : https://prove2.me/theorems/d6208ce5-581a-47bd-b111-aa00a40a4644
-- title:
--   Valuation Transport
-- statement:
--   Definitions and structural lemmas for Valuation Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RestrictedRamification/ValuationTransport.lean

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
namespace GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
section Conjugate
variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]
def smulPlace (σ : G) (w : HeightOneSpectrum B) : HeightOneSpectrum B where
  asIdeal := σ • w.asIdeal
  isPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B σ)
  ne_bot := by
    intro h
    apply w.ne_bot
    rw [← inv_smul_smul σ w.asIdeal, h]
    exact Ideal.map_bot
end Conjugate
section NumberField
variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]
end NumberField
section Unramified
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
end Unramified
end GroundTheory.ProfCoh


