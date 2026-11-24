-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:23.774323+00:00
-- url     : https://prove2.me/theorems/2e60ad48-cd95-46d0-839d-a75bfc7df8a2
-- title:
--   Shear GLTranspose Mul
-- statement:
--   Definitions and structural lemmas for Shear GLTranspose Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]
def shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k :=
  fromRows Y.toRows₁ (Y.toRows₂ + c * Y.toRows₁)
def dil (t : k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k := fromRows Y.toRows₁ (t • Y.toRows₂)
def stack (Y₁ : Matrix R D k) (C : Matrix T R k) : Matrix (R ⊕ T) D k := fromRows Y₁ (C * Y₁)
def shearGL (c : Matrix T R k) : GL (R ⊕ T) k :=
  ⟨fromBlocks 1 cᵀ 0 1, fromBlocks 1 (-cᵀ) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩
def dilGL (t : kˣ) : GL (R ⊕ T) k :=
  ⟨diagonal (Sum.elim 1 fun _ => (t : k)), diagonal (Sum.elim 1 fun _ => ((t⁻¹ : kˣ) : k)), by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp⟩
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.RankChart
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel
end GlobalTheory.RankChart


