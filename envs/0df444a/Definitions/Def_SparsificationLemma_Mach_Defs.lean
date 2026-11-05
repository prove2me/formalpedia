-- Prove2me | Definitions.Def_SparsificationLemma_Mach_Defs
-- name    : SparsificationLemma_Mach_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:14.788083+00:00
-- url     : https://prove2.me/theorems/fd4bceae-fd98-485f-9b12-82f1bdc4dc7e
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_ClauseBoundStatement
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace SparsificationLemma.Mach
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma.Geo Turing
def encIn (s k : ℕ) {n : ℕ} (φ : Sat3.CNF n) : List Bool := List.replicate s true ++ false :: SatM.enc k φ
def codeNat (v : ℕ) : List Bool := List.replicate v true ++ [false]
def codeLit (l : PLit) : List Bool := l.2 :: codeNat l.1
def codeCl (C : PCl) : List Bool := C.flatMap (fun l => true :: codeLit l) ++ [false]
def codeFml (ψ : PFml) : List Bool := ψ.flatMap (fun C => true :: codeCl C) ++ [false]
def code (L : List PFml) : List Bool := L.flatMap (fun ψ => true :: codeFml ψ) ++ [false]
def Prints : Prop := ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ (k n s : ℕ) (φ : Sat3.CNF n), 1 ≤ k → s0U k ≤ s → SatK.IsKCNF k φ → [] ∉ φ →
    Nonempty (TM2OutputsInTime M.tm ((encIn s k φ).map M.inputAlphabet.invFun)
      (some ((code (outTau k n (tauOf s) (Decode.toN φ))).map M.outputAlphabet.invFun))
      (C * ((encIn s k φ).length + 2 ^ k) ^ C * 2 ^ (C * (n / 2 ^ s))))
def precE (C k : ℕ) (ε : ℚ) : ℕ := max (s0U k) (Nat.clog 2 ⌈(C : ℚ) / ε⌉₊)
def SparsABCD : Prop := ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ (k n : ℕ) (ε : ℚ) (φ : Sat3.CNF n), 1 ≤ k → 0 < ε → ε ≤ 1 → SatK.IsKCNF k φ → [] ∉ φ →
    ∃ (Φ : List PFml) (T : ℕ),
      Nonempty (TM2OutputsInTime M.tm ((encIn (precE C k ε) k φ).map M.inputAlphabet.invFun) (some ((code Φ).map M.outputAlphabet.invFun)) T) ∧
      (∀ Ψ ∈ Φ, IsKCNF k n Ψ ∧ Ψ.Nodup) ∧
      (Φ.length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) ∧
      (∀ b, ExactlyOne b (Decode.toN φ) Φ) ∧
      (∀ Ψ ∈ Φ, ∀ v, (occN Ψ v : ℝ) ≤ ((C : ℝ) * (k : ℝ) / (ε : ℝ)) ^ (16 * k)) ∧
      (T : ℝ) ≤ (C : ℝ) * (((encIn (precE C k ε) k φ).length : ℝ) + 2 ^ k) ^ C * (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ))
def LemSparsification : Prop := ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ Mε s c : ℕ, 1 ≤ Mε ∧
    ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → [] ∉ φ →
      ∃ (Φ : List PFml) (T : ℕ),
        Nonempty (TM2OutputsInTime M.tm ((encIn s 3 φ).map M.inputAlphabet.invFun) (some ((code Φ).map M.outputAlphabet.invFun)) T) ∧
        (T : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * ((c : ℝ) * ((n : ℝ) + 1) ^ c) ∧
        (Φ.length : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) ∧
        (∀ Ψ ∈ Φ, IsKCNF 3 n Ψ ∧ Ψ.Nodup ∧ Ψ.length ≤ Mε * n) ∧
        (Sat3.Satisfiable φ ↔ ∃ Ψ ∈ Φ, ∃ b, Sat b Ψ)
end SparsificationLemma.Mach


