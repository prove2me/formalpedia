-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_HeckeDoubleCosetAdicCompletionInvMulIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:04.635712+00:00
-- url     : https://prove2.me/theorems/41f96af7-4e49-4c0f-a63e-f7fa0c06bb4c
-- title:
--   Hecke Double Coset Adic Completion Inv Mul Integral
-- statement:
--   Definitions and structural lemmas for Hecke Double Coset Adic Completion Inv Mul Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/HeckeDoubleCosetAdicCompletionInvMulIntegral.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace GlobalTheory.HeckeLocInt
open Matrix
variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
end GlobalTheory.HeckeLocInt
namespace GlobalTheory
end GlobalTheory


