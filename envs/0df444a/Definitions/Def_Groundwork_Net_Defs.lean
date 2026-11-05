-- Prove2me | Definitions.Def_Groundwork_Net_Defs
-- name    : Groundwork_Net_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:12.371183+00:00
-- url     : https://prove2.me/theorems/1b7ac9b5-ec3d-4715-9529-427101e9da52
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic
set_option autoImplicit false
section
namespace Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
@[expose] public def pairs (J : Type*) [Fintype J] [LinearOrder J] : Finset (J × J) :=
  univ.filter fun p => p.1 < p.2
@[expose] public def pr [LinearOrder J] (a b : J) : J × J := (min a b, max a b)
@[expose] public def tuples {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (T : ι → Finset X) (d : X) : Finset (ι → X) :=
  Fintype.piFinset fun i => if P i then T i else {d}
public abbrev Inst (J A : Type*) := J → (J → A) → ℤ
@[expose] public def labellings (J : Type*) [Fintype J] [LinearOrder J] [Fintype A] (d : A) : Finset (J × J → A) :=
  tuples (fun p : J × J => p.1 < p.2) (fun _ => univ) d
@[expose] public def star [LinearOrder J] (Λ : J × J → A) (v : J) : J → A := fun w => Λ (pr v w)
@[expose] public def Inst.Z [Fintype J] [LinearOrder J] [Fintype A] (d : A) (R : Inst J A) : ℤ :=
  ∑ Λ ∈ labellings J d, ∏ v, R v (star Λ v)
@[expose] public def Inst.pad [Fintype J] [DecidableEq J] [DecidableEq A'] (R : Inst J A) (d : A)
    (D : Finset A') (dec : A' → A) : Inst J A' :=
  fun v θ => if ∀ w, w ≠ v → θ w ∈ D then R v (fun w => if w = v then d else dec (θ w)) else 0
public structure Network (J σ τ : Type*) where
  S : J → Finset σ
  W : J → σ → ℤ
  Θ : J → J → Finset τ
  f : J → J → σ → τ → ℤ
  c : J → J → ℕ
namespace Network
@[expose] public def lab [LinearOrder J] (N : Network J σ τ) (a b : J) : Finset τ := N.Θ (min a b) (max a b)
@[expose] public def Ψ [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) : ℤ :=
  ∑ θ ∈ N.lab a b, N.f a b z θ * N.f b a z' θ
@[expose] public def value [Fintype J] [LinearOrder J] (N : Network J σ τ) : ℤ :=
  ∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2)
@[expose] public def U [Fintype J] [DecidableEq J] (N : Network J σ τ) : ℕ :=
  ∑ a, ∑ b ∈ univ.erase a, N.c a b
public structure Shaped [Fintype J] [LinearOrder J] (N : Network J σ τ) (P : ℕ) : Prop where
  card_S : ∀ a, #(N.S a) ≤ 2 ^ P
  c_symm : ∀ a b, N.c a b = N.c b a
  sum_c : ∀ a, ∑ b ∈ univ.erase a, N.c a b ≤ P
  card_lab : ∀ a b, a ≠ b → #(N.lab a b) ≤ 2 ^ N.c a b
public structure Sized [Fintype J] [LinearOrder J] (N : Network J σ τ) (P B : ℕ) : Prop extends Shaped N P where
  abs_W : ∀ a z, |N.W a z| ≤ 2 ^ B
  abs_f : ∀ a b z θ, |N.f a b z θ| ≤ 2 ^ B
  abs_Ψ : ∀ a b z z', a ≠ b → |N.Ψ a b z z'| ≤ 2 ^ B
@[expose] public def merge [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ) :
    Network J' (J → σ) (J × J → τ) where
  S G := tuples (fun a => χ a = G) N.S s₀
  W G z := (∏ a with χ a = G, N.W a (z a)) *
    ∏ p ∈ pairs J with χ p.1 = G ∧ χ p.2 = G, N.Ψ p.1 p.2 (z p.1) (z p.2)
  Θ G G' := tuples (fun p : J × J => χ p.1 = G ∧ χ p.2 = G') (fun p => N.lab p.1 p.2) t₀
  f G G' z t := ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.f p.1 p.2 (z p.1) (t (if G < G' then p else p.swap))
  c G G' := ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2
@[expose] public def toInst [Fintype J] [LinearOrder J] [DecidableEq A] (N : Network J σ τ)
    (D : J → J → Finset A) (dec : J → J → A → τ) : Inst J A :=
  fun a θ => ∑ z ∈ N.S a, N.W a z *
    ∏ b ∈ univ.erase a, if θ b ∈ D (min a b) (max a b) then N.f a b z (dec (min a b) (max a b) (θ b)) else 0
end Network
end Groundwork


