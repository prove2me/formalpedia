-- Prove2me | Definitions.Def_HatAffineGeneral_Discovery
-- name    : HatAffineGeneral_Discovery
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T09:06:24.250137+00:00
-- url     : https://prove2.me/theorems/110bc430-e3c9-4a11-8311-476f3a02938e
-- title:
--   Discovery
-- statement:
--   Definitions and structural lemmas for Discovery, from insammael (insammael/one-sided-affine-hat-guessing; see pinned Apache-2.0 LICENSE)'s pinned One-sided affine obstructions in complete bipartite hat guessing development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/Lean/HatAffineGeneral/Discovery.lean

import Mathlib
set_option autoImplicit true
open scoped BigOperators
namespace HatAffineGeneral
universe u v w
def Wins {K : Type u} {I : Type v} {J : Type w}
    (F : (J → K) → I → K)
    (G : (I → K) → J → K) : Prop :=
  ∀ x y,
    (∃ i, F y i = x i) ∨
    (∃ j, G x j = y j)
def Extends {K : Type u} {I : Type v} {J : Type w}
    (F : (J → K) → I → K) : Prop :=
  ∃ G : (I → K) → J → K, Wins F G
def BadSet {K : Type u} {I : Type v} {J : Type w}
    (F : (J → K) → I → K) (x : I → K) : Set (J → K) :=
  {y | ∀ i, F y i ≠ x i}
def Covers {K : Type u} {J : Type w}
    (g : J → K) (Y : Set (J → K)) : Prop :=
  ∀ y, y ∈ Y → ∃ j, y j = g j
def AffineHalf {K : Type u} {I : Type v} {J : Type w}
    [Semiring K] [Fintype J]
    (F : (J → K) → I → K) : Prop :=
  ∃ A : I → J → K, ∃ b : I → K,
    ∀ y i, F y i = (∑ j, A i j * y j) + b i
def GeneralNoGoStatement : Prop :=
  ∀ (K : Type u) [Field K] [Fintype K] (m : ℕ),
    4 ≤ Fintype.card K →
    1 ≤ m →
    ∀ F : (Fin m → K) → Fin (Fintype.card K - 1) → K,
      AffineHalf F → ¬ Extends F
abbrev F3 := ZMod 3
local instance three_is_prime : Fact (Nat.Prime 3) := ⟨by decide⟩
def q3A (i j : Fin 2) : F3 :=
  if i = 0 then
    if j = 0 then 1 else -1
  else
    1
def q3F (y : Fin 2 → F3) : Fin 2 → F3 :=
  fun i => ∑ j, q3A i j * y j
def q3G (x : Fin 2 → F3) : Fin 2 → F3 :=
  fun j =>
    if j = 0 then 2 * x 0 - x 1
    else x 0 - x 1
abbrev F5 := ZMod 5
local instance five_is_prime : Fact (Nat.Prime 5) := ⟨by decide⟩
def Q5M4NoGoStatement : Prop :=
  ∀ F : (Fin 4 → F5) → Fin 4 → F5,
    AffineHalf F → ¬ Extends F
end HatAffineGeneral


