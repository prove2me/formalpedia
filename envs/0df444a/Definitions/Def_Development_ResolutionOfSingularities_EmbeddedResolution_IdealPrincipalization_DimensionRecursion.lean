-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:12.258966+00:00
-- url     : https://prove2.me/theorems/56c2408a-15a7-412b-b92c-7726a953e61e
-- title:
--   Dimension Recursion
-- statement:
--   Definitions and structural lemmas for Dimension Recursion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DimensionRecursion.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
structure PrincipalizationRules where
  divisorRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) → ℕ → T.SequenceOfBlowups
  maxOrderRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups) → T.SequenceOfBlowups
  orderRed : ∀ T : MarkedIdealWithBoundary.{u},
    (∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc ≤ T.krullDimSucc → ℕ → S.SequenceOfBlowups) → T.SequenceOfBlowups
namespace PrincipalizationRules
def divisorFamily (B : PrincipalizationRules.{u}) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    PrincipalizationAssignment.{u} :=
  fun T => B.divisorRed T (fun S _ => L S) j
def orderFamily (B : PrincipalizationRules.{u}) (D : ℕ → PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => B.orderRed T (fun S _ j => D j S)
def maxOrderFamily (B : PrincipalizationRules.{u}) (A : PrincipalizationAssignment.{u}) :
    PrincipalizationAssignment.{u} :=
  fun T => B.maxOrderRed T (fun S _ => A S)
def nextLevel (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) : OrderReductionData.{u} where
  maxOrderRed := B.maxOrderFamily (B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j))
  orderRed := B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j)
def inputLevelData (B : PrincipalizationRules.{u}) : ℕ → OrderReductionData.{u}
  | 0 => trivialOrderReductionData.{u}
  | n + 1 => B.nextLevel (B.inputLevelData n)
def outputLevelData (B : PrincipalizationRules.{u}) (n : ℕ) : OrderReductionData.{u} := B.nextLevel (B.inputLevelData n)
def levelDivisorFamily (B : PrincipalizationRules.{u}) (n : ℕ) (j : ℕ) : PrincipalizationAssignment.{u} :=
  B.divisorFamily (B.inputLevelData n).maxOrderRed j
structure ReducesInductivelyOnDimension (B : PrincipalizationRules.{u}) : Prop where
  divisorSpec : ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (B.divisorFamily L j) L
  divisorShift : ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    IsBoundaryPositionInvariant (fun d => d ≤ n) (fun j => B.divisorFamily L j)
  maxOrderSpec : ∀ (n : ℕ) (A L : PrincipalizationAssignment.{u}),
    IsOrderReduction (fun d => d ≤ n) A L →
    IsMaxOrderReduction (fun d => d ≤ n) (B.maxOrderFamily A) A
  orderSpec : ∀ (n : ℕ) (D : ℕ → PrincipalizationAssignment.{u}) (L O : PrincipalizationAssignment.{u}),
    IsMaxOrderReduction (fun d => d < n) L O →
    (∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (D j) L) →
    IsBoundaryPositionInvariant (fun d => d ≤ n) D →
    IsOrderReduction (fun d => d ≤ n) (B.orderFamily D) L
end PrincipalizationRules
end FunctorialResolution.EmbeddedResolution


