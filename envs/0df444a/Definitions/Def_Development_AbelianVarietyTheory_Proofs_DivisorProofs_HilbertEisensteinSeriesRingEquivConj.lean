-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesRingEquivConj
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesRingEquivConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:53.903361+00:00
-- url     : https://prove2.me/theorems/5d6af4ab-8138-475c-9699-7c3dd3fb1fa1
-- title:
--   Hilbert Eisenstein Series Ring Equiv Conj
-- statement:
--   Definitions and structural lemmas for Hilbert Eisenstein Series Ring Equiv Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesRingEquivConj.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinFourierCoeffRingEquivConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaFactorPowTwoMul
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
namespace GlobalTheory.HilbFam
end GlobalTheory.HilbFam


