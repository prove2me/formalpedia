-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:12.713607+00:00
-- url     : https://prove2.me/theorems/972c9ec6-dee9-4666-8847-ac503e9eb315
-- title:
--   Is Unimodular Block Upper Triangular Symmetric Levels
-- statement:
--   Definitions and structural lemmas for Is Unimodular Block Upper Triangular Symmetric Levels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsUnimodularBlockUpperTriangularSymmetricLevels.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
namespace GlobalTheory.LevelUnimod
section General
open scoped Pointwise NNReal ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
end General
section Mat
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
def levDiag (lev : ι → ℕ) (t : kˣ) : GL ι k where
  val := diagonal fun r => (t : k) ^ lev r
  inv := diagonal fun r => ((t⁻¹ : kˣ) : k) ^ lev r
  val_inv := by simp [diagonal_mul_diagonal, ← mul_pow]
  inv_val := by simp [diagonal_mul_diagonal, ← mul_pow]
def flipInv (σ : ι ≃ ι) (g : GL ι k) : GL ι k where
  val := (g⁻¹ : GL ι k).valᵀ.submatrix σ σ
  inv := g.valᵀ.submatrix σ σ
  val_inv := by rw [submatrix_mul_equiv, ← transpose_mul, Units.mul_inv, transpose_one, submatrix_one_equiv]
  inv_val := by rw [submatrix_mul_equiv, ← transpose_mul, Units.inv_mul, transpose_one, submatrix_one_equiv]
def flipAut (σ : ι ≃ ι) (hσ : ∀ r, σ (σ r) = r) : GL ι k ≃* GL ι k where
  toFun := flipInv σ
  invFun := flipInv σ
  left_inv g := by
    ext r s
    exact congrArg₂ g.val (hσ r) (hσ s)
  right_inv g := by
    ext r s
    exact congrArg₂ g.val (hσ r) (hσ s)
  map_mul' g h := by
    ext1
    change ((g * h)⁻¹ : GL ι k).valᵀ.submatrix σ σ =
      (g⁻¹ : GL ι k).valᵀ.submatrix σ σ * (h⁻¹ : GL ι k).valᵀ.submatrix σ σ
    rw [submatrix_mul_equiv, ← transpose_mul, _root_.mul_inv_rev, Units.val_mul]
end Mat
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
end Local
end GlobalTheory.LevelUnimod


