-- Prove2me | Definitions.Def_PrintedStatement
-- name    : PrintedStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T21:28:24.237043+00:00
-- url     : https://prove2.me/theorems/6000c5c1-37a8-46ad-b735-3c8a79f3ac6f
-- title:
--   Printed Statement
-- statement:
--   Definitions and structural lemmas for Printed Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PrintedStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_EightSquareStatement
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Printed
open Groundwork Groundwork.Prog Finset Eight.SecNetworks QueryMachines
def unary (n : ℕ) : List Unit := List.replicate n ()
abbrev TableQuery : Type := ℕ × List Bool
def tables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : TableQuery → Option ℤ :=
  fun x => if x.1 < K ∧ x.2.length = (K - 1) * lam then some (W x.1 x.2) else none
def AchievedBy (M : QueryMachine TableQuery ℤ (List Unit × List Unit) ℤ) (Cc K : ℕ) (e : ℝ) : Prop :=
  ∀ (lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K, ∀ z ∈ words ((K - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T : ℕ, M.Within (tables K lam W) QueryMachine.unitCost (unary lam, unary B) T (Cc * (B + lam) ^ Cc) (clique K lam fun w => W w.val).value ∧
      (T : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc
def Achievable (K : ℕ) (e : ℝ) : Prop :=
  2 ≤ K ∧ 0 ≤ e ∧ ∃ (M : QueryMachine TableQuery ℤ (List Unit × List Unit) ℤ) (Cc : ℕ), M.PolyTimeSteps ∧ AchievedBy M Cc K e
def StMono : Prop := ∀ (K : ℕ) (e e₁ : ℝ), Achievable K e → e ≤ e₁ → Achievable K e₁
noncomputable def eStar : ℝ := sInf {e : ℝ | ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K e}
def StHalf : Prop := (∀ K : ℕ, 2 ≤ K → Achievable K (1 / 2)) ∧ eStar ≤ 1 / 2 ∧ 0 ≤ eStar
def StAnswerEachQuery : Prop := ∀ (M : QueryMachine TableQuery ℤ (List Unit × List Unit) ℤ) (Cc K : ℕ) (e : ℝ), AchievedBy M Cc K e →
  ∀ (lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K, ∀ z ∈ words ((K - 1) * lam), |W w z| < 2 ^ B) →
    (∃ (own : ℕ) (L : List TableQuery), M.Runs (tables K lam W) (unary lam, unary B) own L (Cc * (B + lam) ^ Cc) (clique K lam fun w => W w.val).value ∧
      (L.length : ℝ) ≤ Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc) ∧
    ∀ (C : Type) [HasSize C] (R : Stepped (C × TableQuery) ℤ) (c : C) (t S : ℕ), 1 ≤ t → (∀ w < K, ∀ z ∈ words ((K - 1) * lam), R.Runs (c, (w, z)) t S (W w z)) →
      ∃ T : ℕ, (M.plug R).Runs (c, (unary lam, unary B)) T (size c + Cc * (B + lam) ^ Cc + S + 1) (clique K lam fun w => W w.val).value ∧
        (T : ℝ) ≤ 3 * (Cc * (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc) * t
abbrev NetQuery : Type := WQ ⊕ (WQ ⊕ (PsiQ ⊕ FQ))
def netOracle {g : ℕ} (N : Net g) : NetQuery → Option ℤ
  | .inl x => if h : x.1 < g then (if x.2.length = N.len ⟨x.1, h⟩ then some (if x.2 ∈ N.S ⟨x.1, h⟩ then 1 else 0) else none) else none
  | .inr (.inl x) => if h : x.1 < g then (if x.2 ∈ N.S ⟨x.1, h⟩ then some (N.W ⟨x.1, h⟩ x.2) else none) else none
  | .inr (.inr (.inl x)) => if h : x.1.1 < g ∧ x.1.2 < g then
      (if x.1.1 ≠ x.1.2 ∧ x.2.1 ∈ N.S ⟨x.1.1, h.1⟩ ∧ x.2.2 ∈ N.S ⟨x.1.2, h.2⟩ then some (N.Ψ ⟨x.1.1, h.1⟩ ⟨x.1.2, h.2⟩ x.2.1 x.2.2) else none) else none
  | .inr (.inr (.inr x)) => if h : x.1.1 < g ∧ x.1.2 < g then
      (if x.1.1 ≠ x.1.2 ∧ x.2.1 ∈ N.S ⟨x.1.1, h.1⟩ ∧ x.2.2 ∈ words (N.c ⟨x.1.1, h.1⟩ ⟨x.1.2, h.2⟩) then some (N.f ⟨x.1.1, h.1⟩ ⟨x.1.2, h.2⟩ x.2.1 x.2.2) else none) else none
abbrev NetInput : Type := (List Unit × List Unit) × (List (List Unit) × List (List (List Unit)))
def netInput {g : ℕ} (N : Net g) (P B : ℕ) : NetInput :=
  ((unary P, unary B), (List.ofFn fun a => unary (N.len a), List.ofFn fun a => List.ofFn fun b => if a = b then [] else unary (N.c a b)))
def ComputesNetworks (NM : QueryMachine NetQuery ℤ NetInput ℤ) (C₁ g K : ℕ) (e : ℝ) : Prop :=
  ∀ (N : Net g) (P B τ : ℕ), N.Is P B → 1 ≤ τ →
    ∃ T : ℕ, NM.Within (netOracle N) (fun _ => τ) (netInput N P B) T (C₁ * (P + B) ^ C₁) N.value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁ * τ
def GroupingLemma : Prop := ∀ (K : ℕ) (e : ℝ), Achievable K e →
  ∃ (NM : QueryMachine NetQuery ℤ NetInput ℤ) (C₁ : ℕ), NM.PolyTimeSteps ∧ ComputesNetworks NM C₁ (3 * K ^ 8) K e
def LevelProposition : Prop := ∀ (K : ℕ) (e : ℝ), Achievable K e → Achievable ((3 * K ^ 8) ^ 2) ((Eight.rho + 2 / K) * e + 2 / K)
def EStarZero : Prop := eStar = 0
def StEveryEta : Prop := ∀ η : ℝ, 0 < η → ∀ K₀ : ℕ, ∃ K, K₀ ≤ K ∧ Achievable K η
end Printed


