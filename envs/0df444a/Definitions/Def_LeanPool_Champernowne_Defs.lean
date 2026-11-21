-- Prove2me | Definitions.Def_LeanPool_Champernowne_Defs
-- name    : LeanPool_Champernowne_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T21:34:13.58832+00:00
-- url     : https://prove2.me/theorems/9f6f3e0f-8ac9-4b38-bcb6-7f9bf90999b9
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Arthur Champernowne and LeanPool contributors's pinned Champernowne normality in every base development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Defs.lean

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Champernowne
def bigDigits (b n : ℕ) : List ℕ := (Nat.digits b n).reverse
def champBlocks (b N : ℕ) : List ℕ :=
  ((List.range N).map fun n => bigDigits b (n + 1)).flatten
theorem champBlocks_succ (b N : ℕ) :
    champBlocks b (N + 1) = champBlocks b N ++ bigDigits b (N + 1) := by
  simp [champBlocks, List.range_succ]
theorem le_length_champBlocks (b N : ℕ) : N ≤ (champBlocks b N).length := by
  induction N with
  | zero => simp [champBlocks]
  | succ n ih =>
    rw [champBlocks_succ, List.length_append]
    have hpos : 0 < (bigDigits b (n + 1)).length := by
      rw [bigDigits, List.length_reverse]
      exact List.length_pos_of_ne_nil
        (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.succ_ne_zero n))
    omega
def champDigit (b i : ℕ) : ℕ :=
  (champBlocks b (i + 1))[i]'(lt_of_lt_of_le (Nat.lt_succ_self i)
    (le_length_champBlocks b (i + 1)))
def countOccurrences (w l : List ℕ) : ℕ :=
  l.tails.countP (w.isPrefixOf ·)
def IsNormalSequence (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Filter.Tendsto
      (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n)
      Filter.atTop (nhds ((b : ℝ) ^ w.length)⁻¹)
end Champernowne


