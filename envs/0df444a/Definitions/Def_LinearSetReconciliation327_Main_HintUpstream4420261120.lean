-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpstream4420261120
-- name    : LinearSetReconciliation327_Main_HintUpstream4420261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:40:16.435374+00:00
-- url     : https://prove2.me/theorems/9a7b358b-7b6a-4da3-ad32-8d93a9840c23
-- title:
--   LinearSetReconciliation327 — HintUpstream44 (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpstream4420261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main.HintUpstream44

/-- For `N ≠ 0` and `z > 0`, `hN N z = z * lg (e * N) - z * lg z`. -/
lemma hN_eq {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {z : ℝ} (hz : 0 < z) :
    hN N z = z * lg (Real.exp 1 * N) - z * lg z := by
  have heN : Real.exp 1 * (N : ℝ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨Real.exp_ne_zero 1, hN0⟩
  rw [hN, if_neg (ne_of_gt hz)]
  simp only [lg]
  rw [Real.logb_div heN (ne_of_gt hz)]
  ring

theorem lemma_4_4 (N : ℕ) :
    (∀ (ι : Type) [Fintype ι] (q : ι → ℝ), (∀ i, 0 ≤ q i) → 0 < ∑ i, q i → ∑ i, q i ≤ N →
      ∑ i, hN N (q i) =
        hN N (∑ i, q i) + (∑ i, q i) * entropyFin (fun i => q i / ∑ i', q i')) ∧
    (∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v ≤ N → hN N (u + v) ≤ hN N u + hN N v) := by
  have key : ∀ (ι : Type) [Fintype ι] (q : ι → ℝ), (∀ i, 0 ≤ q i) → 0 < ∑ i, q i →
      ∑ i, q i ≤ N →
      ∑ i, hN N (q i) =
        hN N (∑ i, q i) + (∑ i, q i) * entropyFin (fun i => q i / ∑ i', q i') := by
    intro ι _ q hq0 hQpos hQleN
    set Q : ℝ := ∑ i, q i with hQ
    have hQ0 : 0 < Q := hQpos
    have hQne : Q ≠ 0 := ne_of_gt hQ0
    have hN0 : (N : ℝ) ≠ 0 := by
      have : (0:ℝ) < (N:ℝ) := by
        have h1 : (0:ℝ) < Q := hQ0
        have h2 : Q ≤ (N:ℝ) := hQleN
        linarith
      exact ne_of_gt this
    have ht1 : ∀ i, hN N (q i) = q i * lg (Real.exp 1 * N) - q i * lg (q i) := by
      intro i
      rcases eq_or_lt_of_le (hq0 i) with h | h
      · rw [← h]
        simp [hN]
      · exact hN_eq hN0 h
    have ht2 : ∀ i, (q i / Q) * lg (1 / (q i / Q)) =
        (q i / Q) * lg Q - (q i / Q) * lg (q i) := by
      intro i
      rcases eq_or_lt_of_le (hq0 i) with h | h
      · rw [← h]
        simp
      · have hqi : q i ≠ 0 := ne_of_gt h
        have h1 : (1:ℝ) / (q i / Q) = Q / q i := by field_simp
        rw [h1]
        simp only [lg]
        rw [Real.logb_div hQne hqi]
        ring
    have hQhN : hN N Q = Q * lg (Real.exp 1 * N) - Q * lg Q := hN_eq hN0 hQ0
    have hent : entropyFin (fun i => q i / Q) = lg Q - (1 / Q) * ∑ i, q i * lg (q i) := by
      rw [entropyFin, Finset.sum_congr rfl (fun i _ => ht2 i), Finset.sum_sub_distrib]
      have hsum1 : ∑ i, q i / Q * lg Q = lg Q := by
        rw [← Finset.sum_mul]
        have hQQ : ∑ i, q i / Q = Q / Q := by rw [← Finset.sum_div, hQ]
        rw [hQQ, div_self hQne, one_mul]
      have hsum2 : ∑ i, q i / Q * lg (q i) = (1 / Q) * ∑ i, q i * lg (q i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsum1, hsum2]
    rw [Finset.sum_congr rfl (fun i _ => ht1 i), Finset.sum_sub_distrib, ← Finset.sum_mul,
      hQhN, hent]
    field_simp
    ring
  refine ⟨key, ?_⟩
  intro u v hu hv huv
  by_cases h0 : u + v = 0
  · have hu0 : u = 0 := le_antisymm (by linarith) hu
    have hv0 : v = 0 := le_antisymm (by linarith) hv
    simp [hu0, hv0, hN]
  · have hQpos : 0 < u + v := lt_of_le_of_ne (by linarith) (Ne.symm h0)
    set q : Fin 2 → ℝ := fun i => if (i : ℕ) = 0 then u else v with hqdef
    have hq0 : ∀ i, 0 ≤ q i := by
      intro i
      fin_cases i <;> simp [q, hu, hv]
    have hsum2 : ∑ i, q i = u + v := by
      simp [Fin.sum_univ_two, q]
    have hmain := key (Fin 2) q hq0 (by rw [hsum2]; exact hQpos) (by rw [hsum2]; exact huv)
    have hleft : ∑ i, hN N (q i) = hN N u + hN N v := by
      simp [Fin.sum_univ_two, q]
    rw [hleft, hsum2] at hmain
    have hent0 : 0 ≤ entropyFin (fun i => q i / (u + v)) := by
      rw [entropyFin]
      apply Finset.sum_nonneg
      intro i _
      have hpi0 : 0 ≤ q i / (u + v) := div_nonneg (hq0 i) hQpos.le
      by_cases hpz : q i / (u + v) = 0
      · simp [hpz]
      · have hqle : q i ≤ u + v := by
          fin_cases i <;> simp [q] <;> linarith
        have hle1 : q i / (u + v) ≤ 1 := (div_le_one hQpos).mpr hqle
        have hinv : (1:ℝ) ≤ 1 / (q i / (u + v)) := by
          rw [one_div]
          exact (one_le_inv₀ (lt_of_le_of_ne hpi0 (Ne.symm hpz))).mpr hle1
        have hlog : 0 ≤ Real.logb 2 (1 / (q i / (u + v))) :=
          Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hinv
        exact mul_nonneg hpi0 (by simpa [lg] using hlog)
    nlinarith [hmain, hent0, hQpos]

end LinearSetReconciliation327.Main.HintUpstream44

#print axioms LinearSetReconciliation327.Main.HintUpstream44.lemma_4_4


