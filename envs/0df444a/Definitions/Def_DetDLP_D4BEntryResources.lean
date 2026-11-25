-- Prove2me | Definitions.Def_DetDLP_D4BEntryResources
-- name    : DetDLP_D4BEntryResources
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:36:25.350571+00:00
-- url     : https://prove2.me/theorems/0ba5daf0-9081-4793-a0ca-2e4277fd69ef
-- title:
--   Uniform natural time and descriptor-space bounds for a residual entry
-- statement:
--   The overhead of a fixed two-round controller absorbs into a fixed polynomial times the source exponential. Its work space is a fixed power of the bit parameter plus the digit-descriptor length.

import Definitions.Def_DetDLP_D4BEntryLengths
set_option autoImplicit false
namespace DetDLP.D4BEntry
open Groundwork D4Plan

def estimate (L k i j n : ℕ) := 2*(np L (np j (np i n))+L*(2*np k n+1))+3

theorem est_pb (L k i j : ℕ) : PB (estimate L k i j) := by
  have h := (np_pb L).comp ((np_pb j).comp (np_pb i))
  exact ((PB.const 2).mul (h.add ((PB.const L).mul (((PB.const 2).mul (np_pb k)).add (PB.const 1))))).add (PB.const 3)
theorem est_mono (L k i j : ℕ) : Monotone (estimate L k i j) := by
  intro a b h; unfold estimate; gcongr; exact np_mono _ (np_mono _ (np_mono _ h)); exact np_mono _ h

theorem resource (C L k i j : ℕ) : ∃ K : ℕ, ∀ n b d z : ℕ, ∀ r : ℝ, 0 ≤ r → 2 ≤ b → n ≤ C*d*(C*d)+d → z ≤ np j (np i n) →
    let σ := polyBound k n; let τ := σ*(2:ℝ)^((k:ℝ)*r)
    ∃ T : ℕ, 1 ≤ T ∧ (T:ℝ) ≤ polyBound K n*(2:ℝ)^((K:ℝ)*r) ∧
      2*(polyBound L z+L*(τ+σ+1)) ≤ T ∧ polyBound L z+L*(σ+1) ≤ ((b+d:ℕ):ℝ)^K := by
  let F := estimate L k i j
  have hf := est_pb L k i j
  obtain ⟨a,ha⟩ := hf
  have hc := (PB.const C).mul PB.id'
  have hs := (est_pb L k i j).comp ((hc.mul hc).add PB.id')
  obtain ⟨s,hS⟩ := hs
  let K := a+k+s+s
  have hak : a ≤ K := by dsimp [K]; omega
  have hkk : k ≤ K := by dsimp [K]; omega
  refine ⟨K,?_⟩; intro n b d z r hr hb hn hz σ τ
  let E := (2:ℝ)^((k:ℝ)*r)
  have he : 1 ≤ E := Real.one_le_rpow (by norm_num) (mul_nonneg (by positivity) hr)
  have hE : E ≤ (2:ℝ)^((K:ℝ)*r) := by apply Real.rpow_le_rpow_of_exponent_le (by norm_num); gcongr
  have hP : polyBound L z ≤ np L (np j (np i n)) := by rw [← np_cast]; exact_mod_cast np_mono L hz
  have hσ : (np k n : ℝ) = σ := np_cast ..
  let T := ⌈2*(polyBound L z+L*(τ+σ+1))+1⌉₊
  have hpos : 0 ≤ σ := by unfold σ polyBound; positivity
  have htpos : 0 ≤ τ := by dsimp [τ]; positivity
  have h₀ : 0 ≤ polyBound L z := by unfold polyBound; positivity
  have hT : 2*(polyBound L z+L*(τ+σ+1))+1 ≤ (T:ℝ) := Nat.le_ceil _
  have hlow : 0 ≤ (L:ℝ)*(τ+σ+1) := by positivity
  refine ⟨T,by exact_mod_cast (show (1:ℝ) ≤ T by linarith),?_,by linarith,?_⟩
  · have hT' := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*(polyBound L z+L*(τ+σ+1))+1)
    have hbase : (F n : ℝ) ≤ polyBound K n := by
      rw [←np_cast]; exact_mod_cast (ha n).trans (Nat.mul_le_mul hak (Nat.pow_le_pow_right (by omega) hak))
    apply le_trans (b := (F n:ℝ)*E) _ (mul_le_mul hbase hE (by positivity) (by unfold polyBound; positivity))
    dsimp [F,estimate]; push_cast; rw [hσ]
    have hx : polyBound L z ≤ (np L (np j (np i n)):ℝ)*E := hP.trans (le_mul_of_one_le_right (by positivity) he)
    have hy : σ ≤ σ*E := le_mul_of_one_le_right hpos he
    have he' : τ+σ+1 ≤ (2*σ+1)*E := by dsimp [τ,E] at *; nlinarith
    have hy' := mul_le_mul_of_nonneg_left he' (Nat.cast_nonneg (α:=ℝ) L)
    dsimp [T]; nlinarith
  · have hn' := (est_mono L k i j hn).trans (hS d)
    have hbound : F n ≤ (b+d)^K := by
      apply hn'.trans; calc s*(d+1)^s ≤ (b+d)^s * (b+d)^s := Nat.mul_le_mul ((Nat.lt_two_pow_self (n:=s)).le.trans (Nat.pow_le_pow_left (by omega) _)) (Nat.pow_le_pow_left (by omega) _)
        _ ≤ _ := by rw [←pow_add]; apply Nat.pow_le_pow_right (by omega); dsimp [K]; omega
    apply le_trans _ (by exact_mod_cast hbound : (F n:ℝ) ≤ ((b+d:ℕ):ℝ)^K)
    dsimp [F,estimate]; push_cast; rw [hσ]; nlinarith [Nat.cast_nonneg (α:=ℝ) L,mul_nonneg (Nat.cast_nonneg (α:=ℝ) L) hpos]
end DetDLP.D4BEntry


