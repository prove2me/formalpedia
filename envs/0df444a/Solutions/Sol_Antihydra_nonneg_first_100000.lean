-- Prove2me | solution 1 for Antihydra.nonneg_first_100000
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:24:04.859117+00:00
-- url     : https://prove2.me/submissions/2b7a27b2-0e79-43a8-b190-bd9c35352577

import Theorems.Thm_Antihydra_run_block_0
import Theorems.Thm_Antihydra_run_block_1
import Theorems.Thm_Antihydra_run_block_2
import Theorems.Thm_Antihydra_run_block_3
set_option maxRecDepth 100000

namespace AntihydraSketch
open AntihydraRun

theorem sound (a : Nat → Nat) (b : Nat → Int)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ k n c p, run k (a n) c = some p → b n = (c : Int) →
      (∀ m, m ≤ k → 0 ≤ b (n + m)) ∧ a (n + k) = p.1 ∧ b (n + k) = (p.2 : Int) := by
  intro k
  induction k with
  | zero =>
    intro n c p h hb
    simp only [run, Option.some.injEq] at h
    subst h
    refine ⟨?_, rfl, hb⟩
    intro m hm
    have h0 : m = 0 := by omega
    subst h0
    rw [Nat.add_zero, hb]
    omega
  | succ k ih =>
    intro n c p h hb
    have hbn := b_rec n
    have e1 : n + (k + 1) = (n + 1) + k := by omega
    simp only [run] at h
    by_cases hp : a n % 2 = 0
    · rw [if_pos hp] at h hbn
      obtain ⟨h1, h2, h3⟩ := ih (n + 1) (c + 2) p (by rw [a_rec]; exact h) (by rw [hbn, hb]; omega)
      refine ⟨?_, by rw [e1]; exact h2, by rw [e1]; exact h3⟩
      intro m hm
      cases m with
      | zero => rw [Nat.add_zero, hb]; omega
      | succ m =>
        rw [show n + (m + 1) = (n + 1) + m by omega]
        exact h1 m (by omega)
    · rw [if_neg hp] at h hbn
      by_cases hc : c = 0
      · rw [if_pos hc] at h
        cases h
      · rw [if_neg hc] at h
        obtain ⟨h1, h2, h3⟩ := ih (n + 1) (c - 1) p (by rw [a_rec]; exact h) (by rw [hbn, hb]; omega)
        refine ⟨?_, by rw [e1]; exact h2, by rw [e1]; exact h3⟩
        intro m hm
        cases m with
        | zero => rw [Nat.add_zero, hb]; omega
        | succ m =>
          rw [show n + (m + 1) = (n + 1) + m by omega]
          exact h1 m (by omega)

theorem step (a : Nat → Nat) (b : Nat → Int)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1)
    (n A C A' C' : Nat) (hA : a n = A) (hB : b n = (C : Int))
    (hr : run 25000 A C = some (A', C')) :
    (∀ m, m ≤ 25000 → 0 ≤ b (n + m)) ∧ a (n + 25000) = A' ∧ b (n + 25000) = (C' : Int) := by
  rw [← hA] at hr
  exact sound a b a_rec b_rec 25000 n C (A', C') hr hB

end AntihydraSketch

theorem solution
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, n ≤ 100000 → b n ≥ 0 := by
  have a0 : a 0 = 8 := a_ini
  have b0 : b 0 = ((0 : Nat) : Int) := by rw [b_ini]; rfl
  obtain ⟨n0, a1', b1'⟩ := AntihydraSketch.step a b a_rec b_rec 0 _ _ _ _ a0 b0 Antihydra.run_block_0
  have a1 : a 25000 = _ := a1'
  have b1 : b 25000 = _ := b1'
  obtain ⟨n1, a2', b2'⟩ := AntihydraSketch.step a b a_rec b_rec 25000 _ _ _ _ a1 b1 Antihydra.run_block_1
  have a2 : a 50000 = _ := a2'
  have b2 : b 50000 = _ := b2'
  obtain ⟨n2, a3', b3'⟩ := AntihydraSketch.step a b a_rec b_rec 50000 _ _ _ _ a2 b2 Antihydra.run_block_2
  have a3 : a 75000 = _ := a3'
  have b3 : b 75000 = _ := b3'
  obtain ⟨n3, a4', b4'⟩ := AntihydraSketch.step a b a_rec b_rec 75000 _ _ _ _ a3 b3 Antihydra.run_block_3
  have a4 : a 100000 = _ := a4'
  have b4 : b 100000 = _ := b4'
  intro n hn
  by_cases c0 : n ≤ 25000
  · have h := n0 (n - 0) (by omega)
    rw [show 0 + (n - 0) = n by omega] at h
    exact h
  by_cases c1 : n ≤ 50000
  · have h := n1 (n - 25000) (by omega)
    rw [show 25000 + (n - 25000) = n by omega] at h
    exact h
  by_cases c2 : n ≤ 75000
  · have h := n2 (n - 50000) (by omega)
    rw [show 50000 + (n - 50000) = n by omega] at h
    exact h
  have h := n3 (n - 75000) (by omega)
  rw [show 75000 + (n - 75000) = n by omega] at h
  exact h
