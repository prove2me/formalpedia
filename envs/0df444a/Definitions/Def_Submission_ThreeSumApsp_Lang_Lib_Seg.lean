-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
-- name    : Submission_ThreeSumApsp_Lang_Lib_Seg
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:25:32.182388+00:00
-- url     : https://prove2.me/theorems/6c662c81-bd0e-4ee7-8c38-6f402591f776
-- title:
--   Seg
-- statement:
--   Definitions and structural lemmas for Seg, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Seg.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity
public import Theorems.Thm_Light_SameOn_write
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
@[expose] public section
namespace Light
open ThreeSumApsp
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]
def readSeg (μ : ℕ → ℤ) (a n : ℕ) : List ℤ := (List.range n).map fun i => μ (a + i)
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
@[simp] theorem length_readSeg : (readSeg μ a n).length = n := by simp [readSeg]
@[simp] theorem getElem_readSeg {i : ℕ} (h : i < (readSeg μ a n).length) :
    (readSeg μ a n)[i] = μ (a + i) := by
  simp [readSeg]
@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)
theorem Seg.getD (h : Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]
theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']
theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc
theorem SameOutside2.update {m c : ℕ} (h : SameOutside2 μ μ' a n b m)
    (hc : (a ≤ c ∧ c < a + n) ∨ (b ≤ c ∧ c < b + m)) (x : ℤ) :
    SameOutside2 μ (Function.update μ' c x) a n b m :=
  h.write (by omega) x
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))
def MatAt {n k : ℕ} (μ : ℕ → ℤ) (a : ℕ) (A : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), μ (a + i * k + j) = A i j
def VecAt {t n : ℕ} (μ : ℕ → ℤ) (a : ℕ) (I : Fin t → Fin n) : Prop :=
  ∀ k : Fin t, μ (a + k.val) = ((I k).val : ℤ)
end Light


