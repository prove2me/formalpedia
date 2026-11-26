-- Prove2me | Definitions.Def_Erdos266_Recursion
-- name    : Erdos266_Recursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:54:46.820731+00:00
-- url     : https://prove2.me/theorems/3f48496e-033b-593f-96dc-dadcef60ee26
-- title:
--   Recursion
-- statement:
--   Definitions and structural lemmas for Recursion, from Ben Keene (benkeene/erdos266; Challenge statement adapted under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Erdos Problem 266: Kovac-Tao disproof of Stolarsky's conjecture on shifted Ahmes series development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean

module
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_bigN_pos
public import Theorems.Thm_Erdos266_dOf_le
public import Theorems.Thm_Erdos266_four_mul_bigM_le
public import Theorems.Thm_Erdos266_latt
public import Theorems.Thm_Erdos266_one_le_bigM
public import Theorems.Thm_Erdos266_one_le_bigN
public import Theorems.Thm_Erdos266_tailAnchor_succ
public import Theorems.Thm_P2M_Erdos266__A_le__L_9d33a2dc6fc9

set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Erdos266
open Finset
abbrev AlgSt := (ℕ → ℕ → ℤ) × (ℕ → ℚ)
def initSt : AlgSt := (fun _ _ => 0, fun _ => 0)
noncomputable def elemR (S : ℕ → ℕ → ℤ) (l j : ℕ) : ℝ :=
  (((j + 1) * bigN l : ℕ) : ℝ) + (S l j : ℝ)
noncomputable def finSum (i k : ℕ) (S : ℕ → ℕ → ℤ) : ℝ :=
  ∑ l ∈ range k, ∑ j ∈ range (dOf l), f (i + 1) (elemR S l j)
def Inv (k : ℕ) (st : AlgSt) : Prop :=
  2 ≤ k ∧
  (∀ l, l < k → ∀ j, j < dOf l → |st.1 l j| ≤ (bigM l : ℤ)) ∧
  ∀ i, i < dOf k →
    |finSum i k st.1 + tailAnchor (i + 1) k - (st.2 i : ℝ)|
      ≤ εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2)
noncomputable def Xvec (k : ℕ) (st : AlgSt) : Fin (dOf k) → ℝ :=
  fun i => (st.2 i.val : ℝ) - finSum i.val k st.1 - tailAnchor (i.val + 1) (k + 1)
lemma four_dOf_le (k : ℕ) : 4 * dOf k * bigM k ≤ bigN k := by
  calc 4 * dOf k * bigM k ≤ 4 * k * bigM k := by
        have := dOf_le k
        exact Nat.mul_le_mul_right _ (by omega)
  _ ≤ bigN k := four_mul_bigM_le k
lemma step_hyp {k : ℕ} {st : AlgSt} (h : Inv k st) :
    ∀ i : Fin (dOf k),
      |Xvec k st i - ∑ j : Fin (dOf k), f (i.val + 1) (((j.val + 1) * bigN k : ℕ) : ℝ)|
        ≤ εL (dOf k) * bigM k / (bigN k : ℝ) ^ (i.val + 2) := by
  obtain ⟨hk, _, hinv⟩ := h
  intro i
  have hanch : ∑ j : Fin (dOf k), f (i.val + 1) (((j.val + 1) * bigN k : ℕ) : ℝ)
      = blockAnchor (i.val + 1) k := by
    rw [blockAnchor]
    exact Fin.sum_univ_eq_sum_range
      (fun j => f (i.val + 1) (((j + 1) * bigN k : ℕ) : ℝ)) (dOf k)
  have htail := tailAnchor_succ (i := i.val + 1) (by omega) k
  have hi := hinv i.val i.isLt
  have hstep : Xvec k st i - ∑ j : Fin (dOf k), f (i.val + 1) (((j.val + 1) * bigN k : ℕ) : ℝ)
      = -(finSum i.val k st.1 + tailAnchor (i.val + 1) k - (st.2 i.val : ℝ)) := by
    rw [hanch, Xvec, htail]
    ring
  rw [hstep, abs_neg]
  refine hi.trans ?_
  have hM0 : (0:ℝ) ≤ (bigM k : ℝ) := Nat.cast_nonneg _
  have hN0 : (0:ℝ) < (bigN k : ℝ) ^ (i.val + 2) := by
    have := bigN_pos k
    positivity
  have hεε := εA_le_εL (dOf k)
  apply div_le_div_of_nonneg_right ?_ hN0.le
  exact mul_le_mul_of_nonneg_right hεε hM0
lemma next_radius_pos {k : ℕ} (hk : 2 ≤ k) (d : ℕ) :
    0 < εA (dOf (k + 1)) * bigM (k + 1) / (bigN (k + 1) : ℝ) ^ (d + 2) := by
  have h1 : (0:ℝ) < εA (dOf (k + 1)) := εA_pos _
  have h2 : (1:ℝ) ≤ (bigM (k + 1) : ℝ) := by
    exact_mod_cast one_le_bigM (show 2 ≤ k + 1 by omega)
  have h3 : (0:ℝ) < (bigN (k + 1) : ℝ) ^ (d + 2) := by
    have := bigN_pos (k + 1)
    positivity
  positivity
noncomputable def blk (k : ℕ) (st : AlgSt) (h : Inv k st) : Fin (dOf k) → ℤ :=
  (latt (dOf k) (bigN k) (bigM k) (one_le_bigN k) (four_dOf_le k)
    (Xvec k st) (step_hyp h)).choose
noncomputable def newS (k : ℕ) (st : AlgSt) (h : Inv k st) : ℕ → ℕ → ℤ :=
  fun l j =>
    if l = k then (if hj : j < dOf k then blk k st h ⟨j, hj⟩ else 0) else st.1 l j
noncomputable def newQ (k : ℕ) (st : AlgSt) (h : Inv k st) : ℚ :=
  (exists_rat_near
    (finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1))
    (next_radius_pos h.1 (dOf k))).choose
open Classical in
/-- One step of the algorithm. -/
noncomputable def stepSt (k : ℕ) (st : AlgSt) : AlgSt :=
  if h : Inv k st then
    (newS k st h,
      if dOf (k + 1) = dOf k + 1
        then Function.update st.2 (dOf k) (newQ k st h)
        else st.2)
  else st
noncomputable def run : ℕ → AlgSt
  | 0 => initSt
  | k + 1 => if k < 2 then initSt else stepSt k (run k)
end Erdos266


