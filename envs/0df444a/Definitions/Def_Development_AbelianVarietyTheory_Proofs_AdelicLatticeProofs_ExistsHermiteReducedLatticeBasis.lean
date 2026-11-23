-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsHermiteReducedLatticeBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:57.773767+00:00
-- url     : https://prove2.me/theorems/11d5b796-8acf-442e-959f-060631c7fc4e
-- title:
--   Exists Hermite Reduced Lattice Basis
-- statement:
--   Definitions and structural lemmas for Exists Hermite Reduced Lattice Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsHermiteReducedLatticeBasis.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IwasawaDecompositionRealMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DetLeadingMinorGramIwasawaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramLeadingMinorLowerBoundIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_GramMinorSwapAdjacentColumnsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
namespace GlobalTheory.ClassFin.HermiteReduction
noncomputable def gramMinor {N : ℕ} (x : Matrix (Fin N) (Fin N) ℝ) (j : Fin (N + 1)) : ℝ :=
  ((xᵀ * x).submatrix (Fin.castLE (Nat.lt_succ_iff.mp j.2)) (Fin.castLE (Nat.lt_succ_iff.mp j.2))).det
end GlobalTheory.ClassFin.HermiteReduction


