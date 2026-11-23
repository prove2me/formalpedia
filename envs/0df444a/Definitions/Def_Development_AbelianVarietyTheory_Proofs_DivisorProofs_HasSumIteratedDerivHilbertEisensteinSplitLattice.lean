-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedDerivHilbertEisensteinSplitLattice
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedDerivHilbertEisensteinSplitLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:45.102487+00:00
-- url     : https://prove2.me/theorems/46f2de08-6b99-4b8d-ae52-fd09afabccbf
-- title:
--   Has Sum Iterated Deriv Hilbert Eisenstein Split Lattice
-- statement:
--   Definitions and structural lemmas for Has Sum Iterated Deriv Hilbert Eisenstein Split Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIteratedDerivHilbertEisensteinSplitLattice.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialVStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSummableBoundHilbertEisensteinTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinMovedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement
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


