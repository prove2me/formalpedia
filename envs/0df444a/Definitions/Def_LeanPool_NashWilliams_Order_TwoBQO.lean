-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Order_TwoBQO
-- name    : LeanPool_NashWilliams_Order_TwoBQO
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:41:59.788463+00:00
-- url     : https://prove2.me/theorems/364f3d66-e2e7-4293-9e50-822373722d53
-- title:
--   Two BQO
-- statement:
--   Definitions and structural lemmas for Two BQO, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Order/TwoBQO.lean

module
public import Mathlib.SetTheory.Ordinal.Basic
public import Definitions.Def_LeanPool_NashWilliams_Order_WellQuasiOrder_Regular
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set Preorder
noncomputable section
abbrev PairSeq (α : Type*) := ∀ m n : ℕ, m < n → α
namespace PairSeq
def restrict {α : Type*} (f : PairSeq α) (e : ℕ → ℕ) (he_mono : StrictMono e) : PairSeq α :=
  fun m n hmn => f (e m) (e n) (he_mono hmn)
def IsBad {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ m n l : ℕ, ∀ (hmn : m < n) (hnl : n < l), ¬ r (f m n hmn) (f n l hnl)
def IsPerfect {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ m n l : ℕ, ∀ (hmn : m < n) (hnl : n < l), r (f m n hmn) (f n l hnl)
end PairSeq
def TwoBQON {α : Type*} (r : α → α → Prop) : Prop :=
  ¬ ∃ f : PairSeq α, PairSeq.IsBad r f
def TwoBQO {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ f : PairSeq α, ∃ m n l : ℕ, ∃ (hmn : m < n) (hnl : n < l), r (f m n hmn) (f n l hnl)
def TwoBQO.LexSumRelQO {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*)
    (t : ∀ i, s i → s i → Prop) : (Σ i, s i) → (Σ i, s i) → Prop
  | ⟨i, x⟩, ⟨j, y⟩ => (r i j ∧ i ≠ j) ∨ ∃ h : i = j, t i x (h ▸ y)
variable {ι : Type*} (r : ι → ι → Prop) (s : ι → Type*) (t : ∀ i, s i → s i → Prop)
theorem TwoBQO.LexSumRelQO.refl (ht_refl : ∀ i (x : s i), t i x x) (σ : Σ i, s i) :
    TwoBQO.LexSumRelQO r s t σ σ := by
  obtain ⟨i, x⟩ := σ
  exact Or.inr ⟨rfl, ht_refl i x⟩
theorem TwoBQO.LexSumRelQO.trans (hr_refl : ∀ i, r i i)
    (hr_antisymm : ∀ i j, r i j → r j i → i = j) (hr_trans : ∀ i j k, r i j → r j k → r i k)
    (ht_trans : ∀ i (x y z : s i), t i x y → t i y z → t i x z) {σ₁ σ₂ σ₃ : Σ i, s i}
    (h₁₂ : TwoBQO.LexSumRelQO r s t σ₁ σ₂) (h₂₃ : TwoBQO.LexSumRelQO r s t σ₂ σ₃) :
    TwoBQO.LexSumRelQO r s t σ₁ σ₃ := by
  obtain ⟨i, x⟩ := σ₁
  obtain ⟨j, y⟩ := σ₂
  obtain ⟨k, z⟩ := σ₃
  simp only [TwoBQO.LexSumRelQO] at h₁₂ h₂₃ ⊢
  rcases h₁₂ with ⟨hrij, hij_ne⟩ | ⟨hij, htxy⟩ <;> rcases h₂₃ with ⟨hrjk, hjk_ne⟩ | ⟨hjk, htyz⟩
  · -- (strict, strict)
    refine Or.inl ⟨hr_trans i j k hrij hrjk, fun hik => ?_⟩
    have hrki : r k i := hik ▸ hr_refl i
    have hrkj : r k j := hik ▸ hrij
    exact hjk_ne (hr_antisymm j k hrjk hrkj)
  · -- (strict, same)
    exact Or.inl ⟨hjk ▸ hrij, hjk ▸ hij_ne⟩
  · -- (same, strict)
    exact Or.inl ⟨hij ▸ hrjk, hij ▸ hjk_ne⟩
  · -- (same, same): compose the `t`-steps after substituting the two index equalities.
    refine Or.inr ⟨hij.trans hjk, ?_⟩
    subst hij; subst hjk
    exact ht_trans i x y z htxy htyz
def DomOrder {α : Type*} (r : α → α → Prop) (X Y : Set α) : Prop := ∀ x ∈ X, ∃ y ∈ Y, r x y
def EmbedForAll {α : Type*} (r : α → α → Prop) (s s' : ℕ → α) : Prop :=
  ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ n, r (s n) (s' (e n))
instance EmbedForAll.isPreorder {Q : Type*} (r : Q → Q → Prop) [IsPreorder Q r] :
    IsPreorder (ℕ → Q) (EmbedForAll r) where
  refl s := ⟨id, strictMono_id, fun n => refl_of r (s n)⟩
  trans := by
    rintro s s' s'' ⟨e₁, he₁, h₁⟩ ⟨e₂, he₂, h₂⟩
    exact ⟨e₂ ∘ e₁, he₂.comp he₁, fun n => trans_of r (h₁ n) (h₂ (e₁ n))⟩
end


