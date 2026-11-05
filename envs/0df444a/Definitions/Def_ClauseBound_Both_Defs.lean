-- Prove2me | Definitions.Def_ClauseBound_Both_Defs
-- name    : ClauseBound_Both_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:15:47.210521+00:00
-- url     : https://prove2.me/theorems/23f5789a-03d9-4b6b-8638-8cca40d60352
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Both/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_FixedWidthVariableBoundStatement
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ClauseBound.Both
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)
end
def StTimeO : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ),
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (k : ℕ) (r : ℕ → ℝ) (c₁ : ℕ), 1 ≤ k → (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ r n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * r n) →
  ∃ c : ℕ, ∀ n₀ q : ℕ, ∃ D : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), SatK.IsKCNF k φ →
    q * ((SatK.enc k φ).length + 2 ^ eO S c n₀ k Q.pick slU (SatK.enc k φ) + 1) ^ q ≤ SatK.boundN r D n
def StTimeM : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (r : ℕ → ℝ) (c₁ : ℕ),
  (∀ m : ℕ, 1 ≤ m → 1 / (c₁ * Real.logb 2 ((m : ℝ) + 2) ^ c₁) ≤ r m) →
  (∀ m : ℕ, S.K (Q.idx 0) ^ 9 ≤ m → e (Q.pick (root9 m)).1.length ≤ c₁ * r m) →
  ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ φ.length → SatK.IsKCNF k φ → SatM.AllOccur φ →
    q * ((SatM.enc k φ).length + 2 ^ eM S Q.pick (SatM.enc k φ) + 1) ^ q ≤ SatM.bound r D k φ.length
end ClauseBound.Both


