-- Prove2me | Definitions.Def_Eight_Cor_NSETHDefs
-- name    : Eight_Cor_NSETHDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:31:32.228555+00:00
-- url     : https://prove2.me/theorems/125b8982-b561-45ee-beac-3e3a02e756f7
-- title:
--   NSETHDefs
-- statement:
--   Definitions and structural lemmas for NSETHDefs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETHDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatStatement
set_option autoImplicit false
section
section
namespace Eight
open Turing
abbrev DNF (n : ℕ) : Type := List (List (Sat3.Lit n))
def Tautology {n : ℕ} (ψ : DNF n) : Prop := ∀ a : Fin n → Bool, ∃ D ∈ ψ, ∀ l ∈ D, a l.1 = l.2
def IsKDNF (k : ℕ) {n : ℕ} (ψ : DNF n) : Prop := (∀ D ∈ ψ, D.length ≤ k) ∧ ψ.Nodup
def withWitness (w x : List Bool) : List Bool := List.replicate w.length true ++ false :: (w ++ x)
def RecognizesTautTM (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : DNF n), IsKDNF k ψ → (Tautology ψ ↔ ∃ w : List Bool,
    Nonempty (TM2OutputsInTime M.tm ((withWitness w (SatK.enc k ψ)).map M.inputAlphabet.invFun) (some ([true].map M.outputAlphabet.invFun)) (t n)))
def TautInNTimeTM (k : ℕ) (δ : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ RecognizesTautTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊
def NSETH_TM : Prop := ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 1 ≤ k ∧ ¬ TautInNTimeTM k (1 - ε)
end Eight


