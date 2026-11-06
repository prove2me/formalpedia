-- Prove2me | Definitions.Def_FixedWidthSteps_RouteDefs
-- name    : FixedWidthSteps_RouteDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T08:05:39.652724+00:00
-- url     : https://prove2.me/theorems/35d19942-a73f-4f9b-bd62-d93a33a2b233
-- title:
--   Route Defs
-- statement:
--   Definitions and structural lemmas for Route Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/RouteDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariablesFixedWidthStatement
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_RecursionToBound_Defs
set_option autoImplicit false
section
section
namespace FixedWidthSteps
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen MainTheoremForms TwoMachines PairsToBound FixedWidth
open Sat3 (CNF)
def ChainOfInequalities : Prop := ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ →
  1 / 2 * ρ ^ l ≤ e ρ x₀ l ∧ 1 / (2 : ℝ) ^ (l + 1) ≤ 1 / 2 * ρ ^ l ∧ 1 / lg (K x₀ l) ≤ 1 / (2 : ℝ) ^ (l + 1) ∧
  ∀ r : ℝ, 0.85 * ρ ^ l ≤ r → r ≤ ρ ^ l → e ρ x₀ l ≤ r ∧ r ≤ 2 * e ρ x₀ l
def RateOfThePairs : Prop := ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → e ρ x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / lg (K x₀ l) ^ AppRunningTime.alpha' ρ
def HypothesisHolds : Prop :=
  ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
    ∃ Q : (solverOf (GeneralPieces.Tied.recOf P val c)).Seq (e ρ x₀) C₀,
      (solverOf (GeneralPieces.Tied.recOf P val c)).Poly ∧
      (∀ l : ℕ, (solverOf (GeneralPieces.Tied.recOf P val c)).K (Q.idx l) = K x₀ l) ∧ Q.pick = Pick.pick (GeneralPieces.Tied.recOf P val c) x₀ ∧
      ∀ num : U × U → ℕ × ℕ, PolyT num → IsBetween ρ x₀ num → NumberBetween (solverOf (GeneralPieces.Tied.recOf P val c)) Q num
def ConditionsHoldEventually : Prop := ∀ k K₀ : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → K₀ ^ 17 ≤ n ∧ (k : ℝ) ^ 4 ≤ lg n
def ReadAsThree : Prop := ∀ (k n : ℕ) (φ : CNF n), k ≤ 3 → SatK.IsKCNF k φ → SatK.IsKCNF 3 φ
def SmallCasesAreWithinTheBound : Prop := ∀ (α : ℝ) (c k n₀ : ℕ), 0 ≤ α → ∃ C : ℕ, ∀ n : ℕ, 4 ≤ n → n < n₀ → 2 ^ (c * n) * n ^ (c * k) ≤ timeVariables α C n
def EveryChoiceCounts : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (α : ℝ) (a : ℕ), 0 < α → (∀ l : ℕ, e l ≤ a / lg (S.K (Q.idx l)) ^ α) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), ThmVariablesAFor S Q M C' → ∀ (Mb : TM2ComputableAux Bool Bool) (c : ℕ), TriesAllWithin Mb c →
      ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
        ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Chooses M Mb test pre id id id N q → ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, CountsFor α k N C
def HypothesisHoldsFrom : Prop := TheRecursionHasLevels → ChainOfInequalities → HypothesisHolds
def EveryChoiceCountsFrom : Prop :=
  ThmVariablesAInParticular → ConditionsHoldEventually → SmallCasesAreWithinTheBound → WidthOr3Stmt → EveryChoiceCounts
def SentenceFromTheSteps : Prop :=
  RecursionToBound.ThmVariablesAWithNumberBetween → HypothesisHolds → RateOfThePairs → EveryTwoMachinesCanBeChosenBetween → FrontEndAndTestExist → ExhaustiveMachineExists → EveryChoiceCounts → FixedWidth.CountsFromPieces
end FixedWidthSteps


