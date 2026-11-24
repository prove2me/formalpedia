-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:09.3859+00:00
-- url     : https://prove2.me/theorems/34de9f88-a8c5-4267-892c-a9b345ea08ce
-- title:
--   Jacobi Trudi
-- statement:
--   Definitions and structural lemmas for Jacobi Trudi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
section Complete
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
end Complete
section Series
variable {R : Type*} [CommRing R]
def geomSeries (a : R) : PowerSeries R := PowerSeries.mk fun n => a ^ n
end Series
section Generating
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
def omitProduct (j : σ) : PowerSeries (MvPolynomial σ ℚ) :=
  ∏ i ∈ univ.erase j, (1 - PowerSeries.C (X i) * PowerSeries.X)
end Generating
section Bialternant
variable {m : ℕ}
def omitProductCoeffMatrix (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℚ) :=
  Matrix.of fun c j => PowerSeries.coeff (m - 1 - (c : ℕ)) (omitProduct j)
def hMatrix (α : Fin m → ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℚ) :=
  Matrix.of fun i c => completeSymmetric (Fin m) ((α i : ℤ) - ((m - 1 - (c : ℕ) : ℕ) : ℤ))
end Bialternant
section Padding
variable (σ : Type*) [Fintype σ] [DecidableEq σ]
def padPartition {r : ℕ} (n : ℕ) (lam : Fin r → ℕ) : Fin n → ℕ :=
  fun i => if h : (i : ℕ) < r then lam ⟨i, h⟩ else 0
end Padding
section Symmetric
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
end Symmetric
end
end GroundTheory.Heights₂.Heights.RestTerms.Schur


