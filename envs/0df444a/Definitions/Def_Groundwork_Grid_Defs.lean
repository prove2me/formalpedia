-- Prove2me | Definitions.Def_Groundwork_Grid_Defs
-- name    : Groundwork_Grid_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:23:33.705571+00:00
-- url     : https://prove2.me/theorems/82df74a3-205a-4b09-ad91-09e3a0bc8922
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Cross_Cuts
import Mathlib.Algebra.Polynomial.Coeff
set_option autoImplicit false
section
section
namespace Groundwork.Grid
open Finset
variable {J ρ γ α τ : Type}
abbrev Rect (ρ γ : Type) := (ρ × ρ) × (γ × γ)
def Ω (ρ γ : Type) [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] : Finset (Rect ρ γ) :=
  univ.filter fun ω => ω.1.1 < ω.1.2 ∧ ω.2.1 < ω.2.2
abbrev Half (ρ γ α : Type) := ρ × γ → ρ × γ → α
def app (G : α → α → α → α → ℤ) (ℓ : Half ρ γ α) (ω : Rect ρ γ) : ℤ :=
  G (ℓ (ω.1.1, ω.2.1) (ω.1.2, ω.2.2)) (ℓ (ω.1.1, ω.2.2) (ω.1.2, ω.2.1))
    (ℓ (ω.1.2, ω.2.1) (ω.1.1, ω.2.2)) (ℓ (ω.1.2, ω.2.2) (ω.1.1, ω.2.1))
def onGrid [DecidableEq α] (R : Inst J α) (d : α) (e : J ≃ ρ × γ) : Inst (ρ × γ) α :=
  fun w h => if h w = d then R (e.symm w) (fun v => h (e v)) else 0
abbrev RowSt (ρ γ α : Type) := γ → ρ × γ → α
abbrev RowLab (γ α τ : Type) := (γ → α) × (γ × γ → τ)
structure Cut (α τ : Type) where
  lab : Finset τ
  top : α → α → τ → ℤ
  bot : α → α → τ → ℤ
  cap : ℕ
def Cut.Factors (C : Cut α τ) (G : α → α → α → α → ℤ) : Prop :=
  ∀ x y u v, G x y u v = ∑ θ ∈ C.lab, C.top x y θ * C.bot u v θ
def trInst (R : Inst (ρ × γ) α) : Inst (γ × ρ) α := fun w h => R w.swap fun w' => h w'.swap
def trG (G : Rect ρ γ → α → α → α → α → ℤ) : Rect γ ρ → α → α → α → α → ℤ :=
  fun ω x y u v => G (ω.2, ω.1) x u y v
section
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
def ZG (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) : ℤ :=
  ∑ ℓ : Half ρ γ α, (∏ w, R w (ℓ w)) *
    ((∏ a, ∏ q ∈ pairs γ, if ℓ (a, q.1) (a, q.2) = ℓ (a, q.2) (a, q.1) then 1 else 0) *
     (∏ i, ∏ p ∈ pairs ρ, if ℓ (p.1, i) (p.2, i) = ℓ (p.2, i) (p.1, i) then 1 else 0) *
     ∏ ω ∈ Ω ρ γ, app (G ω) ℓ ω)
def rowW (R : Inst (ρ × γ) α) (a : ρ) (z : RowSt ρ γ α) : ℤ :=
  (∏ i, R (a, i) (z i)) * ∏ q ∈ pairs γ, if z q.1 (a, q.2) = z q.2 (a, q.1) then 1 else 0
def rowΨ (G : Rect ρ γ → α → α → α → α → ℤ) (a b : ρ) (z z' : RowSt ρ γ α) : ℤ :=
  (∏ i, if z i (b, i) = z' i (a, i) then 1 else 0) *
    ∏ k : γ × γ with k.1 < k.2,
      G ((a, b), k) (z k.1 (b, k.2)) (z k.2 (b, k.1)) (z' k.1 (a, k.2)) (z' k.2 (a, k.1))
def rowΘ (C : Rect ρ γ → Cut α τ) (t₀ : τ) (a b : ρ) : Finset (RowLab γ α τ) :=
  univ ×ˢ tuples (fun k : γ × γ => k.1 < k.2) (fun k => (C ((a, b), k)).lab) t₀
def rowTop (C : Rect ρ γ → Cut α τ) (a b : ρ) (z : RowSt ρ γ α) (θ : RowLab γ α τ) : ℤ :=
  (∏ i, if z i (b, i) = θ.1 i then 1 else 0) *
    ∏ k : γ × γ with k.1 < k.2, (C ((a, b), k)).top (z k.1 (b, k.2)) (z k.2 (b, k.1)) (θ.2 k)
def rowBot (C : Rect ρ γ → Cut α τ) (a b : ρ) (z' : RowSt ρ γ α) (θ : RowLab γ α τ) : ℤ :=
  (∏ i, if z' i (a, i) = θ.1 i then 1 else 0) *
    ∏ k : γ × γ with k.1 < k.2, (C ((a, b), k)).bot (z' k.1 (a, k.2)) (z' k.2 (a, k.1)) (θ.2 k)
def rowNet (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ) (t₀ : τ) (L : ℕ) :
    Network ρ (RowSt ρ γ α) (RowLab γ α τ) where
  S _ := univ
  W := rowW R
  Θ a b := if a < b then rowΘ C t₀ a b else ∅
  f a b z θ := if a < b then rowTop C a b z θ else rowBot C b a z θ
  c a b := Fintype.card γ * L + ∑ k : γ × γ with k.1 < k.2, (C ((min a b, max a b), k)).cap
end
section
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]
def Pat (ρ γ : Type) [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] (n : ℕ) : Finset (Rect ρ γ → ℕ) :=
  tuples (fun ω => ω ∈ Ω ρ γ) (fun _ => range (n + 1)) 0
end
end Groundwork.Grid


