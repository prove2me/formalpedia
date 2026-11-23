-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevelStatement
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevelStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:35.666078+00:00
-- url     : https://prove2.me/theorems/d0c287da-3812-47ce-99a4-b59d1c29634c
-- title:
--   Exists Split Of Hilbert Lattice Has Level Statement
-- statement:
--   Definitions and structural lemmas for Exists Split Of Hilbert Lattice Has Level Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSplitOfHilbertLatticeHasLevelStatement.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevel
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


