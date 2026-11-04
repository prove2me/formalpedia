-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
-- name    : Submission_ThreeSumApsp_Lang_Regions
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:16:18.303372+00:00
-- url     : https://prove2.me/theorems/622ab431-c16e-4527-9cf6-d4b0d309ee24
-- title:
--   Regions
-- statement:
--   Shared source definitions for the weighted-cache 3SUM formalization.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Regions.lean

module
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Function.Basic
set_option autoImplicit false
@[expose] public section
namespace Light
abbrev Inside (a n b : ℕ) : Prop := a ≤ b ∧ b < a + n
abbrev Outside (a n b : ℕ) : Prop := b < a ∨ a + n ≤ b
abbrev Apart (a n a' n' : ℕ) : Prop := a + n ≤ a' ∨ a' + n' ≤ a
abbrev InOrder (top : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | [r] => r.1 + r.2 ≤ top
  | r :: r' :: rs => r.1 + r.2 ≤ r'.1 ∧ InOrder top (r' :: rs)
def SameOn (K : ℕ → Prop) (μ μ' : ℕ → ℤ) : Prop := ∀ b, K b → μ' b = μ b
abbrev SameOutside (μ μ' : ℕ → ℤ) (a n : ℕ) : Prop := SameOn (Outside a n) μ μ'
abbrev SameOutside2 (μ μ' : ℕ → ℤ) (a n b m : ℕ) : Prop :=
  SameOn (fun x => Outside a n x ∧ Outside b m x) μ μ'
abbrev SameOutside3 (μ μ' : ℕ → ℤ) (a n b m c k : ℕ) : Prop :=
  SameOn (fun x => Outside a n x ∧ Outside b m x ∧ Outside c k x) μ μ'
abbrev Kept (μ μ' : ℕ → ℤ) (fr : ℕ) : Prop := SameOn (· < fr) μ μ'
abbrev KeptBut (μ μ' : ℕ → ℤ) (fr out len : ℕ) : Prop :=
  SameOn (fun x => x < fr ∧ Outside out len x) μ μ'
variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}
theorem SameOn.cell (h : SameOn (· = b) μ μ') : μ' b = μ b := h b rfl
theorem SameOn.trans (h₁ : SameOn K μ μ') (h₂ : SameOn K μ' μ'') : SameOn K μ μ'' :=
  fun b hb => (h₂ b hb).trans (h₁ b hb)
theorem SameOn.then (h₁ : SameOn K₁ μ μ') (h₂ : SameOn K₂ μ' μ'') (hK : ∀ b, K b → K₁ b ∧ K₂ b) :
    SameOn K μ μ'' :=
  fun b hb => (h₂ b (hK b hb).2).trans (h₁ b (hK b hb).1)
variable {dst j : ℕ} {f : ℕ → ℤ}
def wrote (μ : ℕ → ℤ) (dst : ℕ) (f : ℕ → ℤ) (j : ℕ) : ℕ → ℤ :=
  fun a => if dst ≤ a ∧ a < dst + j then f (a - dst) else μ a





end Light


