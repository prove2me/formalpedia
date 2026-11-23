-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverField
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:55.1456+00:00
-- url     : https://prove2.me/theorems/03b8bdab-be91-471a-bc92-b66e63b67ce9
-- title:
--   Hermitian Form Diagonalizes Over Field
-- statement:
--   Definitions and structural lemmas for Hermitian Form Diagonalizes Over Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianFormDiagonalizesOverField.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SplitAnisotropic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DiagHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.AlgDiag
theorem blockOne_mul {K : Type} [CommRing K] {M : ℕ} (a b : K) (A B : Matrix (Fin M) (Fin M) K) :
    blockOne a A * blockOne b B = blockOne (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blockOne, Matrix.mul_apply, Fin.sum_univ_succ]
theorem blockOne_one {K : Type} [CommRing K] {M : ℕ} :
    blockOne (1 : K) (1 : Matrix (Fin M) (Fin M) K) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [blockOne, Matrix.one_apply]
  exact fun h => absurd h.symm (Fin.succ_ne_zero _)
def blockGL {K : Type} [CommRing K] {M : ℕ} (h : GL (Fin M) K) : GL (Fin (M + 1)) K where
  val := blockOne 1 (h : Matrix (Fin M) (Fin M) K)
  inv := blockOne 1 ((h⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K)
  val_inv := by rw [blockOne_mul, Units.mul_inv, mul_one, blockOne_one]
  inv_val := by rw [blockOne_mul, Units.inv_mul, mul_one, blockOne_one]
end GlobalTheory.CompanionTheory.SW.AlgDiag


