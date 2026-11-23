-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinFourierCoeffRingEquivConj
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinFourierCoeffRingEquivConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:48.814678+00:00
-- url     : https://prove2.me/theorems/c590d19c-ab6d-4487-91d1-2bfe2af80fbb
-- title:
--   Hilbert Eisenstein Fourier Coeff Ring Equiv Conj
-- statement:
--   Definitions and structural lemmas for Hilbert Eisenstein Fourier Coeff Ring Equiv Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinFourierCoeffRingEquivConj.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominatorStatement
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


