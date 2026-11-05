-- Prove2me | Definitions.Def_VariableBound_Top_ArithDefs
-- name    : VariableBound_Top_ArithDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:22:41.437029+00:00
-- url     : https://prove2.me/theorems/50a32545-f44a-4942-8fc9-ed02a5eed3a9
-- title:
--   Arith Defs
-- statement:
--   Definitions and structural lemmas for Arith Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_ArithDefs
set_option autoImplicit false
section
section
namespace VariableBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net
def GD (C₀ : ℕ) : ℕ := 842 + 68 * C₀
def ccD (k C₀ : ℕ) : ℕ := 3 + 3 * GD C₀ + (19 + 140 * k + GD C₀) + GD C₀ + 18 + 1 + C₀ * (85 * C₀ + 16) + 18 * (4 + 17 * C₀) + (10 + 34 * C₀)
def BkD (C C₀ : ℕ) : ℕ := 2 * (102 * C₀ * aU C C₀) ^ 2
def AexpD (C₀ : ℕ) : ℕ := 140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 + 4
def StUbD : Prop := ∀ β k K n : ℕ, 1 ≤ β → 1 ≤ n → UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16
def StArgD : Prop := ∀ β k K n C₀ : ℕ, k ≤ β → β + 3 ≤ 2 ^ β → 2 ≤ K → K ^ 17 ≤ n → n < K ^ (17 * C₀) → 2 ^ β ≤ n + 1 →
  K * (lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) + bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n)) ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16)
def StLowerD : Prop := ∀ β k K n C₀ : ℕ, 1 ≤ β → k ≤ β → 2 ≤ K → K ^ 17 ≤ n → n < K ^ (17 * C₀) →
  K * (3 * K ^ 8 * K.size) ≤ 3 * (WofU β K * n) ∧
  K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GD C₀ * (WofU β K * n) ∧
  K * ((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))) ≤ (19 + 140 * k + GD C₀) * (WofU β K * n) ∧
  3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) ∧
  K * (18 * K ^ 16) ≤ 18 * (WofU β K * n) ∧
  K * K ^ 2 ≤ WofU β K * n ∧
  K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (WofU β K * n) ∧
  K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) ≤ 18 * (4 + 17 * C₀) * (WofU β K * n) ∧
  K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤ (10 + 34 * C₀) * (WofU β K * n)
def StNeedD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k n s A₁ : ℕ), 1 ≤ k → 2 ≤ S.K i → S.K i ^ 17 ≤ n → n < S.K i ^ (17 * C₀) →
  2 ^ betaU k s ≤ n + 1 → 0 < e → e ≤ 1 → 1 / (2 : ℝ) ^ s ≤ e → ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e →
  (∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
    e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) →
  (needD S k i n s : ℝ) ≤ ((140 * k * (35 * k) + ccD k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1)
def StPlanNeedD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (k n : ℕ) (i : Idx) (s : ℕ),
  s0U k ≤ s → 2 ^ betaU k s ≤ n + 1 → 29 * LD (2 ^ betaU k s) + 19 ≤ n → (planAtD S k n i s).getD n ≤ needD S k i n s
end VariableBound


