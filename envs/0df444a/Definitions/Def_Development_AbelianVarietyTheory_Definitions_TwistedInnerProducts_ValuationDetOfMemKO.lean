-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:48.768715+00:00
-- url     : https://prove2.me/theorems/fabed2af-47f8-4a1c-bea9-2c2d7dd042c5
-- title:
--   Valuation Det Of Mem KO
-- statement:
--   Definitions and structural lemmas for Valuation Det Of Mem KO, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
def IntM {m n : Type*} (M : Matrix m n k) : Prop := ∀ i j, M i j ∈ 𝒪[k]
def MaxM {m n : Type*} (M : Matrix m n k) : Prop := ∀ i j, valuation k (M i j) < 1
section Arith
variable {l m n : Type*}
end Arith
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
def blockGL {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
    (g : GL a k) (B : Matrix a t k) (D : GL t k) : GL (a ⊕ t) k :=
  ⟨fromBlocks g.val B 0 D.val, fromBlocks (g⁻¹).val (-((g⁻¹).val * B * (D⁻¹).val)) 0 (D⁻¹).val,
    by simp [fromBlocks_multiply, ← Matrix.mul_assoc], by simp [fromBlocks_multiply, Matrix.mul_assoc]⟩
section Block
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
end Block
end GlobalTheory.StepData


