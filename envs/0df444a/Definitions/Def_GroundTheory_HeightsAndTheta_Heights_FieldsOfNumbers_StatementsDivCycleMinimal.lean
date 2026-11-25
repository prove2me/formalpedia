-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:52.689293+00:00
-- url     : https://prove2.me/theorems/01199731-9e46-5018-a3a5-bf323a86f5b3
-- title:
--   Statements Div Cycle Minimal
-- statement:
--   Definitions and structural lemmas for Statements Div Cycle Minimal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDivCycleMinimal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
def DivCycleMinimal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), P.IsPrime →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ a : MRing ι F, a ∉ P →
    ∀ (W : Ideal (MRing ι F)) (hW : W.IsPrime), relDim W = (n : ℕ) → P ⊔ Ideal.span {a} ≤ W →
      haveI := hW
      W ∈ (P ⊔ Ideal.span {a}).minimalPrimes ∧ multAt (P ⊔ Ideal.span {a}) W ≠ ⊤
end
end GroundTheory.Heights₂.Heights.FieldNumbers


