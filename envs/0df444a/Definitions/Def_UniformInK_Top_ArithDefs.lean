-- Prove2me | Definitions.Def_UniformInK_Top_ArithDefs
-- name    : UniformInK_Top_ArithDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:20:51.130091+00:00
-- url     : https://prove2.me/theorems/cb1d61c1-c5da-492e-b84d-7c740322af4b
-- title:
--   Arith Defs
-- statement:
--   Definitions and structural lemmas for Arith Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
set_option autoImplicit false
section
section
namespace UniformInK
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
def WofU (β K : ℕ) : ℕ := (β + 3) ^ 2 * 2 ^ β * K.size
def GU (C₀ : ℕ) : ℕ := 2660 * (1 + 17 * C₀)
def ccU (k C₀ : ℕ) : ℕ := 3 + 3 * GU C₀ + (55 + 354 * k + GU C₀) + GU C₀ + 54 + 1 + C₀ * (85 * C₀ + 16) + 27 * (4 + 17 * C₀) + (17 + 51 * C₀)
def aU (C C₀ : ℕ) : ℕ := 34 + 8 * C + 8 * C * C₀
def A1U (C₀ : ℕ) : ℕ := 1 + (2 * C₀ + 2).factorial * 2 ^ (2 * C₀ + 2)
def StNeedU : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k n s A₁ : ℕ), 1 ≤ k → 2 ≤ S.K i → S.K i ^ 17 ≤ n → n < S.K i ^ (17 * C₀) →
  2 ^ betaU k s ≤ n + 1 → 0 < e → e ≤ 1 → 1 / (2 : ℝ) ^ s ≤ e → ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e →
  (∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
    e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) →
  (needU S k i n s : ℝ) ≤ ((354 * k * (35 * k) + ccU k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1)
def StMasterU : Prop := ∀ (β K C₀ : ℕ) (e : ℝ), β + 3 ≤ 2 ^ β → 2 ≤ K → 1 / Real.logb 2 K ^ C₀ ≤ e → (2 ^ β) ^ 6 ≤ K →
  ((WofU β K : ℕ) : ℝ) ≤ (A1U C₀ : ℝ) * K * e
def StDLogU : Prop := ∀ (K n s C C₀ k : ℕ) (e : ℝ), 2 ≤ K → K ≤ n → 1 / Real.logb 2 K ^ C₀ ≤ e → (2 : ℝ) ^ s ≤ (2 / e) ^ C →
  2 ^ betaU k s ≤ (Nat.log 2 n + 1) ^ (aU C C₀ * k)
def StSixU : Prop := ∀ D c K n C₀ : ℕ, 1 ≤ c → 1 ≤ n → n < K ^ (17 * C₀) → D ≤ (Nat.log 2 n + 1) ^ c → 2 * (102 * C₀ * c) ^ 2 ≤ Nat.log 2 n → D ^ 6 ≤ K
def StBetaU : Prop := ∀ k s : ℕ, 1 ≤ k → k ≤ betaU k s ∧ betaU k s + 3 ≤ 2 ^ betaU k s ∧ betaU k s + 1 ≤ 35 * k * (s + 1)
end UniformInK


