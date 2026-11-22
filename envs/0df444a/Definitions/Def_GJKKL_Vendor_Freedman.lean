-- Prove2me | Definitions.Def_GJKKL_Vendor_Freedman
-- name    : GJKKL_Vendor_Freedman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:31:41.187594+00:00
-- url     : https://prove2.me/theorems/8055faf7-9005-4d92-858c-befff275ea33
-- title:
--   Freedman
-- statement:
--   Definitions and structural lemmas for Freedman, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Vendor/Freedman.lean

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Pseudorandom
open Finset
section Resample
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {P : ι → α → ℝ}
end Resample
section Freedman
variable {α : Type*} [Fintype α] {n : ℕ}
def Adapted {β : Type*} (k : ℕ) (F : (Fin n → α) → β) : Prop :=
  ∀ ω ω' : Fin n → α, (∀ i : Fin n, (i : ℕ) < k → ω i = ω' i) → F ω = F ω'
omit [Fintype α] in
theorem Adapted.update {β : Type*} {k : ℕ} {F : (Fin n → α) → β} (h : Adapted k F)
    (i : Fin n) (hi : k ≤ i) (ω : Fin n → α) (a : α) : F (Function.update ω i a) = F ω :=
  h _ _ fun j hj => by
    rw [Function.update_of_ne]
    intro hji; subst hji; omega
def Alive (G : ℕ → (Fin n → α) → Prop) (k : ℕ) (ω : Fin n → α) : Prop := ∀ j ≤ k, G j ω
noncomputable def condAbsInc (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ) (i : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ a, P i a * |X (i + 1) (Function.update ω i a) - X i ω|
open Classical in
/-- The stopped process. -/
noncomputable def stopped (X : ℕ → (Fin n → α) → ℝ) (G : ℕ → (Fin n → α) → Prop) :
    ℕ → (Fin n → α) → ℝ
  | 0 => X 0
  | k + 1 => fun ω => if Alive G k ω then X (k + 1) ω else stopped X G k ω
open Classical in
/-- The accumulated conditional expected absolute increments of the stopped process. -/
noncomputable def accInc (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ)
    (G : ℕ → (Fin n → α) → Prop) : ℕ → (Fin n → α) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun ω => if h : k < n then
      (if Alive G k ω then accInc P X G k ω + condAbsInc P X ⟨k, h⟩ ω else accInc P X G k ω)
      else accInc P X G k ω
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
def IsExposureMartingale (P : Fin n → α → ℝ) (X : ℕ → (Fin n → α) → ℝ) : Prop :=
  (∀ k, Adapted k (X k)) ∧
    ∀ (i : Fin n) ω, X i ω = ∑ a, P i a * X (i + 1) (Function.update ω i a)
end Freedman
end Pseudorandom


