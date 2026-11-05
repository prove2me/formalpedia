-- Prove2me | Definitions.Def_SparsificationLemma_Cal_Defs
-- name    : SparsificationLemma_Cal_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:52:06.379839+00:00
-- url     : https://prove2.me/theorems/bbb5d02f-7c07-4416-8445-9e633bf3264d
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Log
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace SparsificationLemma.Cal
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
def xC (k : ℕ) (ε : ℚ) : ℚ := 32 * ((k : ℚ) - 1) ^ 2 / ε
def logC (k : ℕ) (ε : ℚ) : ℕ := Nat.clog 2 ⌈xC k ε⌉₊
def alphaC (k : ℕ) (ε : ℚ) : ℕ := ⌈2 * ((k : ℚ) - 1) ^ 2 / ε * (logC k ε : ℚ)⌉₊
def betaC (α : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | c + 2 => ∑ h : Fin (c + 1), 4 * α * betaC α (c + 1 - h) * betaC α (h + 1)
def thetaC (α : ℕ) : ℕ → ℕ
  | 0 => 2
  | c + 1 => α * betaC α (c + 1)
def depthC (α k n : ℕ) : ℕ := (∑ c ∈ range k, betaC α c) * n
noncomputable def yC (k α : ℕ) : ℝ := 32 * ((k : ℝ) - 1) ^ 2 * Real.logb 2 (32 * (α : ℝ)) / (32 * (α : ℝ))
def sparsify (k n : ℕ) (ε : ℚ) (φ : PFml) : List PFml :=
  outputs (thetaC (alphaC k ε)) k (depthC (alphaC k ε) k n) (noTaut φ)
def StLogC : Prop := ∀ (k : ℕ) (ε : ℚ), 2 ≤ k → 0 < ε → ε ≤ 1 → ((logC k ε : ℕ) : ℤ) = ⌈Real.logb 2 ((xC k ε : ℚ) : ℝ)⌉
def StBetaRec : Prop := ∀ α c : ℕ, 2 ≤ c → betaC α c = ∑ h ∈ Ico 1 c, 4 * α * betaC α (c - h) * betaC α h
def StBetaCat : Prop := ∀ α c : ℕ, betaC α (c + 1) = 2 * (8 * α) ^ c * catalan c
def StCatLe : Prop := ∀ j : ℕ, catalan j ≤ 4 ^ j
def StBetaLe : Prop := ∀ α c : ℕ, betaC α (c + 1) ≤ 2 * (32 * α) ^ c
def FactIV : Prop := ∀ α k : ℕ, 1 ≤ α → 2 ≤ k → ∑ c ∈ Ico 1 k, betaC α c ≤ 4 * (32 * α) ^ (k - 2)
def StThrCal : Prop := ∀ α k : ℕ, 1 ≤ α → ThrC k α (thetaC α) (betaC α)
def StAlpha : Prop := ∀ (k : ℕ) (ε : ℚ), 3 ≤ k → 0 < ε → ε ≤ 1 →
  128 ≤ xC k ε ∧ 2 ≤ alphaC k ε ∧ k ^ 2 ≤ alphaC k ε ∧
  2 * ((xC k ε : ℚ) : ℝ) * Real.logb 2 ((xC k ε : ℚ) : ℝ) ≤ 32 * (alphaC k ε : ℝ) ∧
  32 * (alphaC k ε : ℚ) ≤ 2 * xC k ε * (logC k ε : ℚ) + 32
def StYLe : Prop := ∀ (k α : ℕ) (ε : ℝ), 2 ≤ k → 0 < ε → 128 ≤ 32 * ((k : ℝ) - 1) ^ 2 / ε →
  2 * (32 * ((k : ℝ) - 1) ^ 2 / ε) * Real.logb 2 (32 * ((k : ℝ) - 1) ^ 2 / ε) ≤ 32 * (α : ℝ) → yC k α ≤ ε
def StSqrt : Prop := ∀ x : ℝ, 128 ≤ x → Real.logb 2 x + 1 + 16 / x ≤ Real.sqrt x
def StAlphaLe : Prop := ∀ (k : ℕ) (ε : ℚ), 3 ≤ k → 0 < ε → ε ≤ 1 → 32 * (alphaC k ε : ℝ) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ 3
def StDegSum : Prop := ∀ α k : ℕ, 1 ≤ α → 2 ≤ k →
  ∑ j ∈ range k, thetaC α j = 2 + α * ∑ c ∈ Ico 1 k, betaC α c ∧
  ∑ j ∈ range k, thetaC α j ≤ 2 + 4 * α * (32 * α) ^ (k - 2) ∧ 8 * (2 + 4 * α * (32 * α) ^ (k - 2)) = 16 + (32 * α) ^ (k - 1)
def StDegLe : Prop := ∀ (k : ℕ) (ε : ℚ), 3 ≤ k → 0 < ε → ε ≤ 1 →
  ((2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) : ℕ) : ℝ) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * k)
def FactI : Prop := ∀ (α k n : ℕ) (ψ : PFml), 1 ≤ α → 1 ≤ k → IsKCNF k n ψ →
  ∀ x ∈ tree (thetaC α) k (depthC α k n) ψ, stepC (thetaC α) k x = none
def FactIIIy : Prop := ∀ (α k n : ℕ) (ψ : PFml), 1 ≤ α → 2 ≤ k → IsKCNF k n ψ →
  ((tree (thetaC α) k (depthC α k n) ψ).length : ℝ) ≤ (2 : ℝ) ^ (yC k α * (n : ℝ))
def SparsABC : Prop := ∀ (k n : ℕ) (ε : ℚ) (φ : PFml), 3 ≤ k → 0 < ε → ε ≤ 1 → IsKCNF k n φ →
  (∀ Φ ∈ sparsify k n ε φ, IsKCNF k n Φ ∧ Φ.Nodup) ∧
  ((sparsify k n ε φ).length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) ∧
  (∀ b, ExactlyOne b φ (sparsify k n ε φ)) ∧
  ∀ Φ ∈ sparsify k n ε φ, ∀ v, (occN Φ v : ℝ) ≤ 2 * (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * k) + 2
end SparsificationLemma.Cal


