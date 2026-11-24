-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:17.147848+00:00
-- url     : https://prove2.me/theorems/2b9fce1b-407e-4c50-a2fe-97bc8babb7e3
-- title:
--   Exists Shifted Lt Class Min
-- statement:
--   Definitions and structural lemmas for Exists Shifted Lt Class Min, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Theorems.Thm_GlobalTheory_IsSiegel_mk
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_GlobalTheory_rpow_half_sq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
section Class
variable {X : Type*} [AddCommGroup X]
def classMin (Q : QuadraticMap ℤ X ℝ) (N : ℤ) (z : QuotSMulTop N X) : ℝ :=
  sInf ((fun x => Q x / N) '' {x | Submodule.Quotient.mk x = z})
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}
end Class
section Main
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ} {N : ℤ} {d : ℕ}
end Main
section Matrix
open ReciprocityTheory.ReducedBases (SameClass IsMinInClass IsUniqueMinInClass)
example : ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (ν : (Fin 1 → ℤ) →+ ℝ), A.PosDef ∧ ν ≠ 0 ∧
    (∀ μ, 0 ≤ ReciprocityTheory.ReducedBases.Q A μ + ν μ) ∧
    1 + 2 * (1 : ℕ) * (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) < (4 : ℤ) := by
  refine ⟨Matrix.diagonal fun _ => 2,
    (Int.castAddHom ℝ).comp (Pi.evalAddMonoidHom (fun _ => ℤ) 0),
    Matrix.PosDef.diagonal fun _ => two_pos, fun h => ?_, fun μ => ?_, ?_⟩
  · simpa using DFunLike.congr_fun h 1
  · have h1 : 0 ≤ μ 0 ^ 2 + μ 0 := by nlinarith [Int.le_self_sq (-μ 0)]
    have h2 : (0 : ℝ) ≤ (μ 0 : ℝ) ^ 2 + μ 0 := by exact_mod_cast h1
    simp [ReciprocityTheory.ReducedBases.Q, ReciprocityTheory.ReducedBases.polar, ReciprocityTheory.ReducedBases.toReal, dotProduct, Matrix.mulVec]
    linarith
  · have h1 := rpow_half_sq 1
    have h2 : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) < 3 / 2 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h1]; norm_num)
    push_cast at h2 ⊢
    linarith
end Matrix
end GlobalTheory.ClassMin
end


