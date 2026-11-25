-- Prove2me | Definitions.Def_DetDLP_S8B_Parameters
-- name    : DetDLP_S8B_Parameters
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:22:28.795467+00:00
-- url     : https://prove2.me/theorems/700c1694-6d85-4b3d-af0c-e9dcee3dd9e4
-- title:
--   Polynomial-time exact Stage I block count and threshold by binary search
-- statement:
--   Binary search for the least integer whose power reaches a given bound realizes the exact ceiling of the positive real root. For binary operands and a unary-bounded exponent, this gives polynomial-time Stage I block counts, target sizes, and hash thresholds. Both the integer computations and their equality to the real-ceiling definitions are proved.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 (pp. 11–13)

import Theorems.Thm_Groundwork_len_nat_mono
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_snd
import Theorems.Thm_Groundwork_PolyT_prodMk
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_P2M_Groundwork_PolyT_ite__226169acf219
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f

set_option autoImplicit false
namespace DetDLP.S8B
open Groundwork Groundwork.PolyT
attribute [local fun_prop] Groundwork.PolyT.const Groundwork.PolyT.comp Groundwork.PolyT.fst Groundwork.PolyT.snd Groundwork.PolyT.prodMk Groundwork.PolyT.div Groundwork.PolyT.mul P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_size__c8c8eb1b342f

def bisect (a m : ℕ) (s : ℕ × ℕ) (_ : Bool) : ℕ × ℕ :=
  let mid := (s.1 + s.2) / 2
  if a ≤ mid ^ m then (s.1, mid) else (min (mid + 1) s.2, s.2)

def ceilRoot (a m : ℕ) := (a.bits.foldl (bisect a m) (0, a)).1

theorem ceilRoot_poly {α : Type} [Enc α] {a m : α → ℕ} (ha : PolyT a) (hm : Unary m) :
    PolyT (fun x => ceilRoot (a x) (m x)) := by
  apply Groundwork.PolyT.fst
  apply foldl (g := fun x => bisect (a x) (m x)) (bits ha) (by fun_prop)
  · let mid := fun p : α × (ℕ × ℕ) × Bool => (p.2.1.1 + p.2.1.2) / 2
    have hs : PolyT mid := by unfold mid; fun_prop
    have hp : PolyT (fun p : α × (ℕ × ℕ) × Bool => mid p ^ m p.1) :=
      pow_unary hs (Groundwork.PolyT.comp hm (by fun_prop))
    unfold mid at hp
    unfold bisect; dsimp only; fun_prop
  · obtain ⟨t, ht, _, hlen⟩ := len_bound ha
    refine ⟨fun n => t n + t n + 2, (ht.add ht).add (PB.const 2), ?_⟩
    intro x k
    have loop (l : List Bool) (s : ℕ × ℕ) (h : s.1 ≤ a x ∧ s.2 ≤ a x) :
        (l.foldl (bisect (a x) (m x)) s).1 ≤ a x ∧ (l.foldl (bisect (a x) (m x)) s).2 ≤ a x := by
      induction l generalizing s with
      | nil => exact h
      | cons b l ih =>
        rw [List.foldl_cons]; apply ih; unfold bisect; dsimp only; split
        · exact ⟨h.1, by dsimp; omega⟩
        · exact ⟨(min_le_right ..).trans h.2, h.2⟩
    have hh := loop (((a x).bits).take k) (0,a x) ⟨Nat.zero_le _,le_rfl⟩
    rw [len_pair]; exact Nat.add_le_add_right (Nat.add_le_add ((len_nat_mono hh.1).trans (hlen x)) ((len_nat_mono hh.2).trans (hlen x))) _

/-- A bit-length number of bisections identifies the least integer whose power is at least `a`. -/
theorem ceilRoot_eq_of_iff (a m r : ℕ) (hr : ∀ k, r ≤ k ↔ a ≤ k^m) (hra : r ≤ a) :
    ceilRoot a m = r := by
  have aux (l : List Bool) (lo hi : ℕ) (hl : lo ≤ r) (hh : r ≤ hi)
      (hw : hi-lo < 2^l.length) : (l.foldl (bisect a m) (lo, hi)).1 = r := by
    induction l generalizing lo hi with
    | nil => simp at hw; simp; omega
    | cons b l ih =>
      simp only [List.length_cons,pow_succ] at hw
      simp only [List.foldl_cons,bisect]
      split
      · rename_i ht
        apply ih _ _ hl ((hr _).2 ht); omega
      · rename_i ht
        have hmr : (lo+hi)/2 < r := Nat.lt_of_not_ge (fun h => ht ((hr _).1 h))
        rw [min_eq_left (by omega : (lo + hi)/2+1 ≤ hi)]
        apply ih _ _ (by omega) hh; omega
  apply aux a.bits 0 a (Nat.zero_le _) hra
  simpa [Nat.size_eq_bits_len] using Nat.lt_size_self a

theorem ceilRoot_eq (a m : ℕ) (hm : 0 < m) : ceilRoot a m = ⌈(a : ℝ) ^ (1/(m:ℝ))⌉₊ := by
  have h (k : ℕ) : ⌈(a : ℝ) ^ (1/(m:ℝ))⌉₊ ≤ k ↔ a ≤ k^m := by
    rw [Nat.ceil_le, one_div, Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) (by exact_mod_cast hm), Real.rpow_natCast]
    exact_mod_cast Iff.rfl
  exact ceilRoot_eq_of_iff _ _ _ h ((h a).2 (Nat.le_self_pow hm.ne' a))

def blocks (b : ℕ) := max 2 (ceilRoot (Nat.size (b+1)) 4)
def qValue (m g : ℕ) := max (4096*m) (ceilRoot (16*g) m)
def threshold (p n m g : ℕ) := (p*qValue m g + n - 1)/n

private theorem clogSize (n : ℕ) : Nat.clog 2 n = Nat.size (n-1) := by
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).2
    have := Nat.lt_size_self (n-1); omega
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1 < 2) n
    have : 0 < 2 ^ Nat.clog 2 n := by positivity
    omega

theorem blocks_eq (b : ℕ) : blocks b = blockCount b := by
  simp [blocks,blockCount,clogSize,ceilRoot_eq _ 4 (by decide)]

theorem qValue_eq (m g : ℕ) (hm : 0 < m) : qValue m g = qStar m g := by
  simp [qValue,qStar,ceilRoot_eq _ _ hm]

theorem threshold_eq (p n m g : ℕ) (hm : 0 < m) : threshold p n m g = hashThreshold p n m g := by
  unfold threshold hashThreshold; rw [qValue_eq _ _ hm]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  apply le_antisymm_iff.mpr
  have h (k : ℕ) : (p*qStar m g + n - 1)/n ≤ k ↔ ⌈(p:ℝ)*qStar m g/n⌉₊ ≤ k := by
    rw [←Nat.ceilDiv_eq_add_pred_div, ceilDiv_le_iff_le_mul hn, Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hn)]
    rw [mul_comm (k:ℝ)]; exact_mod_cast Iff.rfl
  exact ⟨(h _).2 le_rfl,(h _).1 le_rfl⟩

@[local fun_prop] theorem blocks_poly {α : Type} [Enc α] {b : α → ℕ} (hb : PolyT b) :
    PolyT (fun x => blocks (b x)) := by
  have hr := ceilRoot_poly (a := fun x => Nat.size (b x + 1)) (m := fun _ => 4) (by fun_prop) (const (List.replicate 4 ()))
  unfold blocks; fun_prop

@[local fun_prop] theorem qValue_poly {α : Type} [Enc α] {m g : α → ℕ} (hm : PolyT m) (hu : Unary m) (hg : PolyT g) :
    PolyT (fun x => qValue (m x) (g x)) := by
  have hr := ceilRoot_poly (a := fun x => 16*g x) (by fun_prop) hu
  unfold qValue; fun_prop

theorem threshold_poly {α : Type} [Enc α] {p n m g : α → ℕ} (hp : PolyT p) (hn : PolyT n) (hm : PolyT m) (hu : Unary m) (hg : PolyT g) :
    PolyT (fun x => threshold (p x) (n x) (m x) (g x)) := by
  have hq := qValue_poly hm hu hg
  unfold threshold; fun_prop

end DetDLP.S8B


