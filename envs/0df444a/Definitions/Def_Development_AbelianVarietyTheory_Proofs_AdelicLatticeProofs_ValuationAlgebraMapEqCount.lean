-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:28.738918+00:00
-- url     : https://prove2.me/theorems/b442d2a2-4338-418d-a67b-f0b8b7ad10ee
-- title:
--   Valuation Algebra Map Eq Count
-- statement:
--   Definitions and structural lemmas for Valuation Algebra Map Eq Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ValuationAlgebraMapEqCount.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
namespace GlobalTheory.AdicValuationCountFactors
variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
end GlobalTheory.AdicValuationCountFactors


