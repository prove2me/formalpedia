-- Prove2me | Definitions.Def_ToTuring_TM_Frag
-- name    : ToTuring_TM_Frag
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:54.24058+00:00
-- url     : https://prove2.me/theorems/85df7d54-2798-42ee-9520-a893748aebbc
-- title:
--   Frag
-- statement:
--   Definitions and structural lemmas for Frag, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
set_option autoImplicit false
section
section
namespace Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
structure Frag (Γ : K → Type) (σ : Type) where
  /-- the labels -/
  Λ : Type
  [fin : Fintype Λ]
  /-- the first label -/
  entry : Λ
  /-- the program -/
  m : Λ → TM2.Stmt Γ Λ σ
attribute [instance] Frag.fin
def Frag.Runs (P : Frag Γ σ) (v : σ) (S : ∀ k, List (Γ k)) (n : ℕ) (S' : ∀ k, List (Γ k)) : Prop :=
  Run (TM2.step P.m) ⟨some P.entry, v, S⟩ n ⟨none, v, S'⟩
def Frag.seq (P Q : Frag Γ σ) : Frag Γ σ where
  Λ := P.Λ ⊕ Q.Λ
  entry := .inl P.entry
  m
    | .inl l => place Sum.inl (some (.inr Q.entry)) (P.m l)
    | .inr l => place Sum.inr none (Q.m l)
def Frag.ofStmt (q : TM2.Stmt Γ Empty σ) : Frag Γ σ where
  Λ := Unit
  entry := ()
  m _ := place Empty.elim none q
def Frag.branch (q : TM2.Stmt Γ Bool σ) (P Q : Frag Γ σ) : Frag Γ σ where
  Λ := Unit ⊕ (P.Λ ⊕ Q.Λ)
  entry := .inl ()
  m
    | .inl _ => place (fun b : Bool => if b then .inr (.inl P.entry) else .inr (.inr Q.entry)) none q
    | .inr (.inl l) => place (fun l => .inr (.inl l)) none (P.m l)
    | .inr (.inr l) => place (fun l => .inr (.inr l)) none (Q.m l)
def Frag.loop (q : TM2.Stmt Γ Unit σ) (B : Frag Γ σ) : Frag Γ σ where
  Λ := Unit ⊕ B.Λ
  entry := .inl ()
  m
    | .inl _ => place (fun _ => .inr B.entry) none q
    | .inr l => place Sum.inr (some (.inl ())) (B.m l)
section within
variable {τ : Type}
def Frag.Within (P : Frag Γ (Option τ)) (S : ∀ k, List (Γ k)) (t : ℕ) (S' : ∀ k, List (Γ k)) : Prop :=
  ∃ n ≤ t, P.Runs none S n S'
end within
end Groundwork.TM


