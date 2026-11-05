-- Prove2me | Definitions.Def_VariableBound_Printed_TiedDefs
-- name    : VariableBound_Printed_TiedDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:24:52.197547+00:00
-- url     : https://prove2.me/theorems/6b874f47-0fd3-44e8-b2f1-d2d8c39ca08d
-- title:
--   Tied Defs
-- statement:
--   Definitions and structural lemmas for Tied Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/TiedDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Paper_Decide
import Definitions.Def_ClauseBound_Inst_Half
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace VariableBound
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound.Decide
def TiedOut (A : List Bool × U → List Bool) (e : List Bool → ℕ) (post : List Bool → List Bool) (rn rm : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    (∀ x : List Bool, Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some ((post (A (x, pad (e x)))).map M.outputAlphabet.invFun)) (C * (x.length + 2 ^ e x + 1) ^ C))) ∧
    (∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
      Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map M.outputAlphabet.invFun)) (SatM.boundNK rn C k n))) ∧
    (∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
      Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map M.outputAlphabet.invFun)) (SatM.bound rm C k φ.length))) ∧
    ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → SatM.AllOccur φ →
      Nonempty (TM2OutputsInTime M.tm ((SatM.enc k φ).map M.inputAlphabet.invFun) (some ((post (SatK.binary n (SatK.numSat φ))).map M.outputAlphabet.invFun)) (SatM.boundBothK rn rm C k n φ.length))
def StEndS (R : ∀ (Idx : Type) [Enc Idx], Solver Idx → (U → U × Idx) → (U → U) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ), PolyT slU →
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (rn rm : ℕ → ℝ) (c₁ : ℕ), (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ rn n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * rn n) → FallBack rn →
  (∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ rm m) →
  (∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * rm m) → (∀ n, 0 ≤ rn n) → (∀ m, 0 ≤ rm m) → R Idx S Q.pick slU rn rm
end VariableBound


