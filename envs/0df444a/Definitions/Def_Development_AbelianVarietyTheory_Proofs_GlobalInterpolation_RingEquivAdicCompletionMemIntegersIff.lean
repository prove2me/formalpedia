-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RingEquivAdicCompletionMemIntegersIff
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RingEquivAdicCompletionMemIntegersIff
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:47.363191+00:00
-- url     : https://prove2.me/theorems/04930757-54dd-5e4b-843a-f7d849b02d3c
-- title:
--   Ring Equiv Adic Completion Mem Integers Iff
-- statement:
--   Definitions and structural lemmas for Ring Equiv Adic Completion Mem Integers Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RingEquivAdicCompletionMemIntegersIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial
namespace GlobalTheory.CompletionAut
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end GlobalTheory.CompletionAut
namespace GlobalTheory
end GlobalTheory


