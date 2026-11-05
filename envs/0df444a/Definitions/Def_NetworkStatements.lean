-- Prove2me | Definitions.Def_NetworkStatements
-- name    : NetworkStatements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:44.355925+00:00
-- url     : https://prove2.me/theorems/c121487e-8eab-48df-b5d5-e11e0a79d0ca
-- title:
--   Network Statements
-- statement:
--   Definitions and structural lemmas for Network Statements, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/NetworkStatements.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Rank
set_option autoImplicit false
section
section
namespace Groundwork
open Finset
abbrev Bits (n : ℕ) : Type := Fin n → Bool
abbrev Tensors (J : Type) (n : ℕ) : Type := J → (J → Bits n) → ℤ
def edgeIndices (J : Type) [Fintype J] [DecidableEq J] (n : ℕ) : Finset (J → J → Bits n) :=
  univ.filter fun x => (∀ a b, x a b = x b a) ∧ ∀ a, x a a = fun _ => false
def Z {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} (W : Tensors J n) : ℤ :=
  ∑ x ∈ edgeIndices J n, ∏ v, W v (x v)
def N (K n : ℕ) : ℕ := K.choose 2 * n
inductive Formula (V : Type) : Type
  | var (v : V)
  | const (c : ℤ)
  | add (a b : Formula V)
  | mul (a b : Formula V)
def Formula.eval {V : Type} (x : V → ℤ) : Formula V → ℤ
  | .var v => x v
  | .const c => c
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x
def Formula.size {V : Type} : Formula V → ℕ
  | .var _ => 1
  | .const _ => 1
  | .add a b => a.size + b.size
  | .mul a b => a.size + b.size
abbrev Entry (J : Type) (n : ℕ) : Type := J × (J → Bits n)
def Formula.ComputesZ {J : Type} [Fintype J] [DecidableEq J] {n : ℕ} (φ : Formula (Entry J n)) : Prop :=
  ∀ W : Tensors J n, φ.eval (fun p => W p.1 p.2) = Z W
def Within (K : ℕ) (e : ℝ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∃ φ : Formula (Entry (Fin K) n), φ.ComputesZ ∧
    (φ.size : ℝ) ≤ C * ((n : ℝ) + 1) ^ C * (2 : ℝ) ^ (e * (N K n : ℝ))
noncomputable def ρ : ℝ := Real.logb 2 12 / 4
def s (p q : Bool) : ℤ := if p = q then 0 else if p then -1 else 1
def X₁ (x y u v : Bool) : ℤ := if x = v ∧ y = u then 1 else 0
def I₁ (x y u v : Bool) : ℤ := if x = u ∧ y = v then 1 else 0
def cross {n : ℕ} (x y u v : Bits n) : ℤ := if x = v ∧ y = u then 1 else 0
def A (n i : ℕ) (x y u v : Bits n) : ℤ :=
  ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
    (∏ k ∈ S, -(s (x k) (y k) * s (u k) (v k))) * ∏ k ∈ Sᶜ, I₁ (x k) (y k) (u k) (v k)
abbrev Bell : Type := Bool × Bool
def singlets {n : ℕ} (β : Fin n → Bell) : ℕ := #{k | β k = (true, true)}
def others {n : ℕ} (β : Fin n → Bell) : ℕ := #{k | β k ≠ (false, false)}
def rowLabels (n i : ℕ) : Finset (Fin n → Bell) := univ.filter fun β => i ≤ singlets β
def colLabels (n i : ℕ) : Finset (Fin n → Bell) := univ.filter fun β => others β ≤ i
end Groundwork


