-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:33.921015+00:00
-- url     : https://prove2.me/theorems/2427a5e5-0fad-43ba-9fa4-b95e74df5b26
-- title:
--   Hecke Weight Two Is Good Of Tsum
-- statement:
--   Definitions and structural lemmas for Hecke Weight Two Is Good Of Tsum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.HeckeTwo.SumGood
section General
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}
def GoodFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set V) (f : ι → V → E) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (f i) U) ∧
  ∀ L : Set V, IsCompact L → L ⊆ U → ∀ k : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ L, ‖iteratedFDeriv ℝ k (f i) z‖ ≤ u i
end General
section Wirtinger
variable {Φ : Type} [Fintype Φ] {ι : Type}
end Wirtinger
end GlobalTheory.HeckeTwo.SumGood


