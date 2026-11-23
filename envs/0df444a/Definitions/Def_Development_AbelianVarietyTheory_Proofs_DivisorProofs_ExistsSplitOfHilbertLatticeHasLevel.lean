-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevel
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:19.960982+00:00
-- url     : https://prove2.me/theorems/ca670499-3315-49ea-bba1-92e1f22a5f68
-- title:
--   Exists Split Of Hilbert Lattice Has Level
-- statement:
--   Definitions and structural lemmas for Exists Split Of Hilbert Lattice Has Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSplitOfHilbertLatticeHasLevel.lean

import Mathlib
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
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.HilbFam


