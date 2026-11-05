-- Prove2me | Definitions.Def_SparsificationLemma_Geo_Defs
-- name    : SparsificationLemma_Geo_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:20:27.836929+00:00
-- url     : https://prove2.me/theorems/6e45567c-b2da-4223-b143-cd2ad484e046
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_UniformInK_Top_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace SparsificationLemma.Geo
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent
def StThrGeo : Prop := ∀ k τ : ℕ, 1 ≤ k → 8 * k ≤ τ → ThrC k τ (thetaU τ) (betaSU τ)
def StDegGeo : Prop := ∀ k τ : ℕ, 1 ≤ k → 8 ≤ τ → 2 * (∑ j ∈ range k, thetaU τ j) + 2 ≤ τ ^ (2 * k)
def outTau (k n τ : ℕ) (φ : PFml) : List PFml := outputs (thetaU τ) k (bsumU τ k * n) φ
def StThmTau : Prop := ∀ (k n τ : ℕ) (ε : ℝ) (φ : PFml), 1 ≤ k → 8 * k ≤ τ →
  ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ k : ℝ)) ≤ ε → IsKCNF k n φ →
  (∀ x ∈ tree (thetaU τ) k (bsumU τ k * n) φ, stepC (thetaU τ) k x = none) ∧
  (∀ Φ ∈ outTau k n τ φ, IsKCNF k n Φ ∧ Φ.Nodup) ∧
  ((outTau k n τ φ).length : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) ∧
  (∀ b, ExactlyOne b φ (outTau k n τ φ)) ∧
  ∀ Φ ∈ outTau k n τ φ, ∀ v, occN Φ v ≤ τ ^ (2 * k)
def tauE (k : ℕ) (ε : ℚ) : ℕ := ⌈(8 * (k : ℚ) / ε) ^ 3⌉₊
def StTauE : Prop := ∀ (k : ℕ) (ε : ℚ), 1 ≤ k → 0 < ε → ε ≤ 1 →
  8 * k ≤ tauE k ε ∧
  ((k : ℝ) / (tauE k ε : ℝ)) * Real.logb 2 (Real.exp 1 * (tauE k ε : ℝ) * (bsumU (tauE k ε) k : ℝ)) ≤ (ε : ℝ) ∧
  (tauE k ε : ℝ) ≤ (9 * (k : ℝ) / (ε : ℝ)) ^ 3
def StThmS : Prop := ∀ (k n s : ℕ) (φ : PFml), 1 ≤ k → s0U k ≤ s → IsKCNF k n φ →
  (∀ x ∈ tree (thetaU (tauOf s)) k (bsumU (tauOf s) k * n) φ, stepC (thetaU (tauOf s)) k x = none) ∧
  (∀ Φ ∈ outTau k n (tauOf s) φ, IsKCNF k n Φ ∧ Φ.Nodup) ∧
  ((outTau k n (tauOf s) φ).length : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 ^ s) ∧
  (outTau k n (tauOf s) φ).length ≤ 2 ^ (n / 2 ^ s + 1) ∧
  (∀ b, ExactlyOne b φ (outTau k n (tauOf s) φ)) ∧
  ∀ Φ ∈ outTau k n (tauOf s) φ, ∀ v, occN Φ v ≤ 2 ^ betaU k s
end SparsificationLemma.Geo


