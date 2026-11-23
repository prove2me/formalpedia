-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinShiftedLatticeFourier
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinShiftedLatticeFourier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:01.364572+00:00
-- url     : https://prove2.me/theorems/2f7f281d-ed55-493e-9d4e-ba6ab7c19236
-- title:
--   Has Sum Hilbert Eisenstein Shifted Lattice Fourier
-- statement:
--   Definitions and structural lemmas for Has Sum Hilbert Eisenstein Shifted Lattice Fourier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinShiftedLatticeFourier.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChangeStatement
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam
noncomputable def shearSub {F : Type} [Field F] (x : F) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v 0, v 1 - v 0 * x]
  invFun v := ![v 0, v 1 + v 0 * x]
  map_add' v w := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp
end GlobalTheory.HilbFam


