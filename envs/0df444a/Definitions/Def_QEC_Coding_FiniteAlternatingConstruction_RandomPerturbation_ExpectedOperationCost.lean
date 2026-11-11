-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T23:04:44.460203+00:00
-- url     : https://prove2.me/theorems/1c815dbb-5fcc-4848-ab27-f67c8a7472b0
-- title:
--   Expected Operation Cost
-- statement:
--   Definitions and structural lemmas for Expected Operation Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExpectedOperationCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
def executionOperationBudget (n v K : ℕ) : ℕ :=
  eventUniverseBudget n+54*v+n^4*(stateQueryBudget n v K+1)+
    (n^4*(stateQueryBudget n v K+1)+378+32*v)*n^4
def vertexSumEquiv (P : TannerSquarePresentation) : Vertex P ≃ P.X ⊕ (P.Q ⊕ P.Z) where
  toFun
    | .x x => .inl x
    | .q q => .inr (.inl q)
    | .z z => .inr (.inr z)
  invFun
    | .inl x => .x x
    | .inr (.inl q) => .q q
    | .inr (.inr z) => .z z
  left_inv := by intro v; cases v <;> rfl
  right_inv := by intro v; rcases v with x|(q|z) <;> rfl
def operationConstant (K : ℕ) : ℕ := 1000000+2*(fullQueryBudget 0 K+9+24*(2*K+1)^3)+540
end QEC.Coding.BDL26RandomPerturbation


