-- Prove2me | Definitions.Def_KSatFreeCodeStatement
-- name    : KSatFreeCodeStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:53.134656+00:00
-- url     : https://prove2.me/theorems/b4454b6d-1867-466d-86ce-8cf6cf15d845
-- title:
--   KSat Free Code Statement
-- statement:
--   Definitions and structural lemmas for KSat Free Code Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/KSatFreeCodeStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
import Mathlib.Topology.Instances.ENNReal.Lemmas
set_option autoImplicit false
section
section
namespace SatFree
open Turing
open Sat3 (Lit CNF Satisfiable slot)
open scoped NNReal ENNReal
def encLit {n : ℕ} (l : Lit n) : List Bool := (List.range (Nat.log2 (2 * n) + 1)).map (slot (some l)).testBit
def encClause {n : ℕ} (C : List (Lit n)) : List Bool := true :: ((C.flatMap fun l => true :: encLit l) ++ [false])
def enc {n : ℕ} (φ : CNF n) : List Bool := List.replicate n true ++ false :: (φ.flatMap encClause ++ [false])
def DecidesTM (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), SatK.IsKCNF k φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((enc φ).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) (t n))
def InTime (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
noncomputable def s (k : ℕ) : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTime k δ), (δ : ℝ≥0∞)
noncomputable def sInfty : ℝ≥0∞ := ⨆ (k : ℕ) (_ : 3 ≤ k), s k
def ETH : Prop := ∀ k : ℕ, 3 ≤ k → 0 < s k
def SETH : Prop := sInfty = 1
def DecidesRandTM (p : ℝ) (k : ℕ) (M : TM2ComputableAux Bool Bool) (r t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), SatK.IsKCNF k φ →
    (∀ w : Fin (r n) → Bool, ∃ b : Bool,
      Nonempty (TM2OutputsInTime M.tm ((enc φ ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) (t n))) ∧
    ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
      (1 - p) * (2 : ℝ) ^ (r n) ≤ (Nat.card {w : Fin (r n) → Bool //
        Nonempty (TM2OutputsInTime M.tm ((enc φ ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) (t n))} : ℝ)
def InTimeRand (p : ℝ) (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c a : ℕ) (β : ℚ), 0 ≤ β ∧ (∀ i, Finite (M.tm.Γ i)) ∧
    DecidesRandTM p k M (fun n => ⌊(a : ℝ) * (2 : ℝ) ^ ((β : ℝ) * n)⌋₊) fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊
noncomputable def sRand (p : ℝ) (k : ℕ) : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTimeRand p k δ), (δ : ℝ≥0∞)
def CodeReadable : Prop :=
  (∀ (n n' : ℕ) (φ : CNF n) (ψ : CNF n') (u v : List Bool), enc φ ++ u = enc ψ ++ v → n = n') ∧
  ∀ (n : ℕ) (φ ψ : CNF n) (u v : List Bool), enc φ ++ u = enc ψ ++ v → φ = ψ ∧ u = v
def BruteForce : Prop := ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧ ∀ k : ℕ, ∃ c : ℕ, DecidesTM k M fun n => c * (n + 2) ^ c * 2 ^ n
def AtMostOne : Prop := (∀ k : ℕ, s k ≤ 1) ∧ sInfty ≤ 1
def SameMachine : Prop := ∀ (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ), DecidesTM (k + 1) M t → DecidesTM k M t
def Increasing : Prop := ∀ k : ℕ, s k ≤ s (k + 1)
def HenceForEverySequence : Prop := ∀ u : ℕ → ℝ≥0∞, (∀ k : ℕ, u k ≤ u (k + 1)) →
  Filter.Tendsto u Filter.atTop (nhds (⨆ (k : ℕ) (_ : 3 ≤ k), u k)) ∧ ((∀ k : ℕ, 3 ≤ k → 0 < u k) ↔ 0 < u 3)
def LimitAndEth : Prop := Filter.Tendsto s Filter.atTop (nhds sInfty) ∧ (ETH ↔ 0 < s 3)
def DeterministicIsRandomized : Prop := ∀ (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ), DecidesTM k M t → DecidesRandTM 0 k M (fun _ => 0) t
def RandomnessHelps : Prop := ∀ (p : ℝ), 0 ≤ p → ∀ k : ℕ, sRand p k ≤ s k
def AllZero : Prop := (∀ k : ℕ, 3 ≤ k → s k = 0) ∧ sInfty = 0 ∧ ¬ ETH ∧ ¬ SETH
def AllZeroRandomized : Prop := ∀ (p : ℝ), 0 ≤ p → ∀ k : ℕ, 3 ≤ k → sRand p k = 0
def SupOneGivesPositive : Prop := ∀ u : ℕ → ℝ≥0∞, (⨆ (k : ℕ) (_ : 3 ≤ k), u k) = 1 → ∃ k : ℕ, 3 ≤ k ∧ 0 < u k
def SethGivesSomeK : Prop := SETH → ∃ k : ℕ, 3 ≤ k ∧ 0 < s k
end SatFree


