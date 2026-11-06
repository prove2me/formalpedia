-- Prove2me | Definitions.Def_CountedRoute_Defs
-- name    : CountedRoute_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T06:03:26.689203+00:00
-- url     : https://prove2.me/theorems/e2dd7514-0520-411b-9c4c-886531d77705
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/CountedRoute/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_CountedInstanceStatement
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
namespace CountedRoute
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms PairsToBound MainRoute NamesInOrder
open Sat3 (CNF)
section
variable (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) [QueryMachine.IsPolyQ E] (K₀ C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ) (n₁ : ℕ)
def fnN : List Bool × U → List Bool := RecursionToBound.count (solverOfMachine E num C₀) n₁ (pickOf kf K₀) (cutFraction num)
def padExpN : List Bool → ℕ := RecursionToBound.expo (solverOfMachine E num C₀) n₁ (pickOf kf K₀) (cutFraction num)
def fnM : List Bool × U → List Bool := AM (solverOfMachine E num C₀) (pickOf kf K₀)
def padExpM : List Bool → ℕ := eM (solverOfMachine E num C₀) (pickOf kf K₀)
def ChainOn : Prop :=
  (∀ M₂ : TM2ComputableAux Bool Bool, ChosenAsPrinted (fnN E K₀ C₀ kf num n₁) (padExpN E K₀ C₀ kf num n₁) K₀ M₂ → ∃ C₂ : ℕ, ThmVariablesBFor M₂ C₂) ∧
  (∀ (M₁ : TM2ComputableAux Bool Bool) (q₁ : ℕ), Computes M₁ (fnM E K₀ C₀ kf num) (padExpM E K₀ C₀ kf num) q₁ → ∃ C₁ : ℕ, MeetsBoundInMAlone M₁ C₁) ∧
  (∀ N : TM2ComputableAux Bool Bool, AssembledDirectly (fnN E K₀ C₀ kf num n₁) (padExpN E K₀ C₀ kf num n₁) (fnM E K₀ C₀ kf num) (padExpM E K₀ C₀ kf num) K₀ N → ∃ C : ℕ, CorMinFor N C ∧ MainTheoremFor N C) ∧
  ∃ N : TM2ComputableAux Bool Bool, BuiltDirectly (fnN E K₀ C₀ kf num n₁) (padExpN E K₀ C₀ kf num n₁) (fnM E K₀ C₀ kf num) (padExpM E K₀ C₀ kf num) K₀ N
end
def OnEveryMachineWithQueryAccess : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) [QueryMachine.IsPolyQ E], ThmVariables.Hypothesis K e C₀ kf num E →
    ∃ n₀ : ℕ, ∀ a : ℕ, (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (K l))) → ∀ n₁ : ℕ, n₀ ≤ n₁ → ChainOn E (K 0) C₀ kf num n₁
def OnTheCountedRecursion : Prop :=
  ∃ (c x₀ C₀ : ℕ) (D : PiecesCounted.Data) (Alg : Stepped ExplicitCost.PieceQuery ExplicitCost.Ans),
    PiecesCounted.IsPieces (1 / Real.sqrt 2) (c + 2) D Alg ∧ (∀ lam tr i, D.cap lam tr i ≤ 2 * lam) ∧ CountedInstance.AreThePiecesOfAppHalfPieces D ∧ 18 ≤ x₀ ∧ c + 7 ≤ 2 ^ x₀ ∧
    (∀ l : ℕ, _root_.Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ ((3 * x₀ + 6 : ℕ) : ℝ) / Real.sqrt (lg (_root_.Levels.Gen.K x₀ l))) ∧
    ThmVariables.Hypothesis (_root_.Levels.Gen.K x₀) (_root_.Levels.Gen.e (1 / Real.sqrt 2) x₀) C₀ (levelsUnder x₀) fractionHalf (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) ∧
    ∀ [QueryMachine.IsPolyQ (ExplicitCost.cliqueMachine (c + 2) x₀ Alg)], ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ →
      ChainOn (ExplicitCost.cliqueMachine (c + 2) x₀ Alg) (_root_.Levels.Gen.K x₀ 0) C₀ (levelsUnder x₀) fractionHalf n₁
def OnEveryMachineWithQueryAccessFrom : Prop := SolverOfMachineLevels → CutNumberFacts → BothBoundsOnEverySolver → OnEverySolver → OnEveryMachineWithQueryAccess
def OnTheCountedRecursionFrom : Prop := CountedInstance.TheRecursionMeetsTheHypothesis → OnEveryMachineWithQueryAccess → OnTheCountedRecursion
def ClosedStatementsFrom : Prop := OnTheCountedRecursion → MainTheoremAllOccur ∧ CorMinAllOccur ∧ ThmVariablesB ∧ NamesInOrder.BoundInMHolds
def MainTheoremHolds : Prop := MainTheoremAllOccur
def CorMinHolds : Prop := CorMinAllOccur
def BoundInMHolds : Prop := NamesInOrder.BoundInMHolds
def ThmVariablesBHolds : Prop := ThmVariablesB
end CountedRoute


