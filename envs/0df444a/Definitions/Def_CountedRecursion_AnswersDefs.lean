-- Prove2me | Definitions.Def_CountedRecursion_AnswersDefs
-- name    : CountedRecursion_AnswersDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:36:37.31446+00:00
-- url     : https://prove2.me/theorems/fde9d05d-ce26-4884-ab9c-cceaaa5cb6e6
-- title:
--   Answers Defs
-- statement:
--   Definitions and structural lemmas for Answers Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/AnswersDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_LevelsStatement
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace ExplicitCost
open Groundwork QueryMachines Printed
variable {Q A A' α β : Type}
abbrev PieceQuery : Type := List Unit × PiecesCounted.Question
abbrev Ans : Type := PiecesCounted.Answer
def asInt : Ans → ℤ
  | .inl v => v
  | .inr _ => 0
def asList : Ans → List ℤ
  | .inl _ => []
  | .inr l => l
def askInt [HasSize α] (h : α → Q) : QueryMachine Q Ans α ℤ := QueryMachine.mapOut (QueryMachine.query h) asInt
def askList [HasSize α] (h : α → Q) : QueryMachine Q Ans α (List ℤ) := QueryMachine.mapOut (QueryMachine.query h) asList
def readAs (r : A' → A) (M : QueryMachine Q A α β) : QueryMachine Q A' α β :=
  { M.toStepped with ask := M.ask, resume := fun s v => M.resume s (r v) }
def ReadAsRuns : Prop := ∀ (Q A A' α β : Type) (r : A' → A) (M : QueryMachine Q A α β) (O : Q → Option A) (O' : Q → Option A') (a : α) (own S : ℕ) (L : List Q) (b : β),
  (∀ x, (O' x).map r = O x) → M.Runs O a own L S b → (readAs r M).Runs O' a own L S b
def ReadAsPoly : Prop := ∀ (Q A A' α β : Type) [Enc Q] [Enc A] [Enc A'] [Enc α] [Enc β] (r : A' → A) (M : QueryMachine Q A α β), PolyT r → M.PolyTimeSteps → (readAs r M).PolyTimeSteps
def PricesScale : Prop := ∀ (Q A α β : Type) (M : QueryMachine Q A α β) (O : Q → Option A) (w w' : Q → ℕ) (a : α) (T S k : ℕ) (b : β), 1 ≤ k → (∀ x, w' x ≤ k * w x) →
  M.Within O w a T S b → M.Within O w' a (k * T) S b
def numbersStep (acc : List Unit × List Unit) : List Unit × List Unit := (unary (8 * acc.1.length), unary ((acc.1.length * acc.2.length) ^ 2))
def numbersM (x₀ : ℕ) : Stepped (List Unit) (List Unit × List Unit) :=
  Stepped.foldRange (fun l : List Unit => l.length) (Stepped.const ()) (fun acc _ (_ : Unit) => numbersStep acc) fun _ => (unary (2 ^ x₀), unary (2 ^ x₀))
def NumbersRun : Prop := ∃ C : ℕ, ∀ x₀ l : ℕ, (numbersM x₀).Runs (unary l) (2 * l) (C * Levels.Gen.g x₀ l) (unary (2 ^ (3 * l + x₀)), unary (Levels.Gen.K x₀ l))
def NumbersPoly : Prop := ∀ x₀ : ℕ, Nonempty (IsPolyT (numbersM x₀))
end ExplicitCost


