-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscr
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscr
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:23.516497+00:00
-- url     : https://prove2.me/theorems/8cf77d65-6e81-42ee-a380-3bc0d3925380
-- title:
--   Different Ideal Pow Finrank Eq Span Discr
-- statement:
--   Definitions and structural lemmas for Different Ideal Pow Finrank Eq Span Discr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentIdealPowFinrankEqSpanDiscr.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.GalDiff
open scoped Pointwise
variable (E : Type) [Field E] [NumberField E]
end GlobalTheory.GalDiff


