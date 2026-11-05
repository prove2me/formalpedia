-- Prove2me | Definitions.Def_StepMachines_Math_Code
-- name    : StepMachines_Math_Code
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:33:04.962658+00:00
-- url     : https://prove2.me/theorems/1c124dc4-cfa6-430b-b2c7-46b1fe148676
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words


set_option autoImplicit false
section
namespace Groundwork
open Finset
variable {X Y : Type*}
public structure Code (S : Finset X) (n : ℕ) where
  D : Finset (List Bool)
  dec : List Bool → X
  len : ∀ w ∈ D, w.length = n
  bij : Set.BijOn dec D S
namespace Code
variable {S : Finset X} {n : ℕ}
@[expose] public def Full (c : Code S n) : Prop := c.D = words n
@[expose] public def word (n : ℕ) : Code (words n) n where
  D := words n
  dec := id
  len _ h := mem_words.1 h
  bij := Set.bijOn_id _
@[expose] public def cast (c : Code S n) {S' : Finset X} {n' : ℕ} (hS : S = S') (hn : n = n') : Code S' n' where
  D := c.D
  dec := c.dec
  len := hn ▸ c.len
  bij := hS ▸ c.bij
@[expose] public def map (c : Code S n) (φ : X → Y) (S' : Finset Y) (h : Set.BijOn φ S S') : Code S' n where
  D := c.D
  dec := φ ∘ c.dec
  len := c.len
  bij := h.comp c.bij
@[expose] public def empty (x : X) (n : ℕ) : Code (∅ : Finset X) n where
  D := ∅
  dec _ := x
  len := by simp
  bij := by simp
@[expose] public def prod {S₁ : Finset X} {S₂ : Finset Y} {n₁ n₂ : ℕ} (c₁ : Code S₁ n₁) (c₂ : Code S₂ n₂) :
    Code (S₁ ×ˢ S₂) (n₁ + n₂) where
  D := (words (n₁ + n₂)).filter fun w => w.take n₁ ∈ c₁.D ∧ w.drop n₁ ∈ c₂.D
  dec w := (c₁.dec (w.take n₁), c₂.dec (w.drop n₁))
  len w h := mem_words.1 (mem_filter.1 h).1
  bij := by
    refine ⟨fun w hw => ?_, fun w hw w' hw' h => ?_, fun x hx => ?_⟩
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      exact mem_coe.2 (mem_product.2 ⟨c₁.bij.mapsTo hw.1, c₂.bij.mapsTo hw.2⟩)
    · have hw := (mem_filter.1 (mem_coe.1 hw)).2
      have hw' := (mem_filter.1 (mem_coe.1 hw')).2
      rw [Prod.mk.injEq] at h
      rw [← List.take_append_drop n₁ w, c₁.bij.injOn hw.1 hw'.1 h.1, c₂.bij.injOn hw.2 hw'.2 h.2,
        List.take_append_drop]
    · obtain ⟨hx₁, hx₂⟩ := mem_product.1 (mem_coe.1 hx)
      obtain ⟨w₁, hw₁, e₁⟩ := c₁.bij.surjOn hx₁
      obtain ⟨w₂, hw₂, e₂⟩ := c₂.bij.surjOn hx₂
      have l₁ := c₁.len w₁ hw₁
      have l₂ := c₂.len w₂ hw₂
      have t : (w₁ ++ w₂).take n₁ = w₁ := by rw [← l₁, List.take_left]
      have d : (w₁ ++ w₂).drop n₁ = w₂ := by rw [← l₁, List.drop_left]
      refine ⟨w₁ ++ w₂, mem_coe.2 (mem_filter.2 ⟨mem_words.2 (by rw [List.length_append, l₁, l₂]), ?_, ?_⟩), ?_⟩
      · rw [t]; exact hw₁
      · rw [d]; exact hw₂
      · simp only [t, d, e₁, e₂]
end Code
end Groundwork


