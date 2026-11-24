-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:04.05881+00:00
-- url     : https://prove2.me/theorems/cf408009-7885-4cc0-89ac-3074007fd840
-- title:
--   Om AUnip Fourier Inv
-- statement:
--   Definitions and structural lemmas for Om AUnip Fourier Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
section NonZero
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
end NonZero
variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def unip (b : Matrix D₁ D₂ k) : GL (D₁ ⊕ D₂) k :=
  ⟨fromBlocks 1 b 0 1, fromBlocks 1 (-b) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
variable [MeasurableSpace k] [BorelSpace k]
end GlobalTheory.SplitFlip.Model


