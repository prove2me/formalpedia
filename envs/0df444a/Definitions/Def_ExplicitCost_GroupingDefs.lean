-- Prove2me | Definitions.Def_ExplicitCost_GroupingDefs
-- name    : ExplicitCost_GroupingDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T05:41:17.657586+00:00
-- url     : https://prove2.me/theorems/01c58f59-1c68-4058-b370-2bda8c652558
-- title:
--   Grouping Defs
-- statement:
--   Definitions and structural lemmas for Grouping Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_AppRunningTimeStatement
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
abbrev GroupingInput : Type := (ℕ × ℕ) × DataInput
def inK (c : GroupingInput) : ℕ := c.2.1.1.length
def inG (c : GroupingInput) : ℕ := c.2.1.2.length
def inP (c : GroupingInput) : ℕ := askedData.P c.2
def inB (c : GroupingInput) : ℕ := askedData.B c.2
def inU (c : GroupingInput) : ℕ := Uc (inG c) askedData.under.toPaperNetwork c.2
def labelLength (c : GroupingInput) : ℕ := (c.1.2 * inU c + 2 * min c.1.1 c.1.2 * inG c * inP c + c.1.2 * inK c ^ 2 - 1) / (c.1.2 * inK c ^ 2)
def goodData (cx : GroupingInput × ℕ) : Bool :=
  ((List.range (inK cx.1)).all fun G => decide (inK cx.1 * (members (inK cx.1) (inG cx.1) cx.2 G).length ≤ 2 * inG cx.1)) &&
  (List.range (inK cx.1)).all fun G => (List.range (inK cx.1)).all fun G' =>
    G == G' || decide (lbLen (inK cx.1) (inG cx.1) askedData.under.toPaperNetwork cx.1.2 cx.2 G G' ≤ labelLength cx.1)
def searchData : Stepped GroupingInput (Option ℕ) := Exits.firstUntil (fun c => inK c ^ inG c) (Stepped.ofFun goodData) id
abbrev CliqueInput : Type := List Unit × List Unit × List Unit
abbrev CliqueCall : Type := ℕ × CliqueInput
def callOf (cx : GroupingInput × ℕ) : CliqueCall := (cx.2, (unary (inK cx.1), unary (labelLength cx.1), unary (bitsOut (inK cx.1) (inG cx.1) (inP cx.1) (inB cx.1))))
def groupingCall : QueryMachine CliqueCall ℤ GroupingInput ℤ := QueryMachine.optBind (QueryMachine.lift searchData) (QueryMachine.query callOf) zeroOf
def entryInput (y : (GroupingInput × ℕ) × TableQuery) : X0 DataInput := ((y.1.1.2, y.1.2), toLists (inK y.1.1) (labelLength y.1.1) y.2)
def answerCall {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) : QueryMachine NetQuery ℤ (GroupingInput × CliqueCall) ℤ :=
  QueryMachine.mapIn (fun y : GroupingInput × CliqueCall => ((y.1, y.2.1), arg y.2.2)) (E.subst (QueryMachine.mapIn entryInput entryData))
def groupingData {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) : QueryMachine NetQuery ℤ GroupingInput ℤ :=
  QueryMachine.mapIn (fun c : GroupingInput => (c, c)) (groupingCall.subst (answerCall E arg))
def groupingInput (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) : GroupingInput := ((a, b), dataInput K N P B)
def LabelLengthIsL : Prop := ∀ (a b K g : ℕ) (N : Net g) (P B : ℕ), 0 < b → a ≤ b → 0 < K → N.Is P B →
  labelLength (groupingInput a b K N P B) = AppRunningTime.Lof K g ((a : ℝ) / b) P N.U ∧ bitsOut K g P B = AppRunningTime.B'of K g P B
def SearchFinds : Prop := ∀ (a b K g : ℕ) (hK0 : 0 < K) (N : Net g) (P B : ℕ), 2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  ∃ x < K ^ g, (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x ∧
    (∀ γ : Fin K, K * #{v : Fin g | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧ ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((a : ℝ) / b) P N.U
def SearchCost : Prop := ∃ C : ℕ, ∀ (a b K g : ℕ) (N : Net g) (P B x : ℕ), 1 ≤ K → K ≤ g → N.Is P B →
  (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x →
    searchData.Runs (groupingInput a b K N P B) (C * K ^ g) ((g * (P + B) + size (a, b)) ^ C) (some x)
def ValueIsKept : Prop := Value.StValueEqualsZ
def SizesStmt : Prop := AppRunningTime.GroupingSizes
def GroupingWithCall : Prop := ∃ C : ℕ, ∀ (a b K g : ℕ) (hK0 : 0 < K) (N : Net g) (P B tc : ℕ), 2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  ∃ x < K ^ g, (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x ∧
    (∀ γ : Fin K, K * #{v : Fin g | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧ (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) ∧
    ∀ O : CliqueCall → Option ℤ, O (callOf (groupingInput a b K N P B, x)) = some (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value →
      groupingCall.Within O (fun _ => tc) (groupingInput a b K N P B) (C * K ^ g + tc) ((g * (P + B) + size (a, b)) ^ C) N.value
def SolvesCliques {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (inp : α) (K L B' 𝒯 SE : ℕ) : Prop :=
  ∀ W : ℕ → List Bool → ℤ, (∀ w < K, ∀ z ∈ words ((K - 1) * L), |W w z| < 2 ^ B') →
    E.Within (tables K L W) QueryMachine.unitCost inp 𝒯 SE (clique K L fun w => W w.val).value
def GroupingExplicit : Prop := ∃ C₁ : ℕ, ∀ (α : Type) (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α) (a b K g : ℕ) (N : Net g) (P B τ 𝒯 SE : ℕ),
  2 ≤ K → 2 ≤ g → 0 < a → a ≤ b → N.Is P B → 1 ≤ τ → AppRunningTime.Cases K g ((a : ℝ) / b) P N.c →
  SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE →
    ∃ T : ℕ, (groupingData E arg).Within (netOracle N) (fun _ => τ) (groupingInput a b K N P B) T (SE + (g * (P + B) + size (a, b)) ^ C₁) N.value ∧
      (T : ℝ) ≤ ((K : ℝ) ^ g + 𝒯 * (2 : ℝ) ^ (2 * (g : ℝ) * P / K) * τ) * ((g : ℝ) * (P + B)) ^ C₁
def GroupingPoly : Prop := groupingCall.PolyTimeSteps ∧
  ∀ (α : Type) [Enc α] (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α), E.PolyTimeSteps → PolyT arg → (groupingData E arg).PolyTimeSteps
def GroupingWithCallFrom : Prop := SearchFinds → SearchCost → SizesStmt → ValueIsKept → GroupingWithCall
def GroupingExplicitFrom : Prop := GroupingWithCall → LabelLengthIsL → EntryCostExplicit → SizesStmt → QueryMachines.StMono → QueryMachines.StSlowDown → QueryMachines.StSubstWithin → GroupingExplicit
end ExplicitCost


