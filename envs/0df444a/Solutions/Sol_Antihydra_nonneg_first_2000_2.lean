-- Prove2me | solution 2 for Antihydra.nonneg_first_2000
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:18:52.510929+00:00
-- url     : https://prove2.me/submissions/2a8d0591-94a2-4f56-ae27-76253030117e

namespace AntihydraCheck

/-- `chk k a c` simulates `k` steps from value `a` with (nonnegative) counter `c`,
returning `false` iff the counter would drop below zero. -/
def chk : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k + 1, a, c =>
    if a % 2 = 0 then chk k (3 * a / 2) (c + 2)
    else if c = 0 then false else chk k (3 * a / 2) (c - 1)

theorem key (a : Nat → Nat) (b : Nat → Int)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ k n c, chk k (a n) c = true → b n = (c : Int) → ∀ m, m ≤ k → 0 ≤ b (n + m) := by
  intro k
  induction k with
  | zero =>
    intro n c _ hb m hm
    have h0 : m = 0 := by omega
    subst h0
    rw [Nat.add_zero, hb]
    omega
  | succ k ih =>
    intro n c h hb m hm
    cases m with
    | zero =>
      rw [Nat.add_zero, hb]
      omega
    | succ m =>
      have e : n + (m + 1) = (n + 1) + m := by omega
      rw [e]
      have hbn := b_rec n
      simp only [chk] at h
      by_cases hp : a n % 2 = 0
      · rw [if_pos hp] at h hbn
        exact ih (n + 1) (c + 2) (by rw [a_rec]; exact h) (by rw [hbn, hb]; omega) m (by omega)
      · rw [if_neg hp] at h hbn
        by_cases hc : c = 0
        · rw [if_pos hc] at h
          exact absurd h Bool.false_ne_true
        · rw [if_neg hc] at h
          exact ih (n + 1) (c - 1) (by rw [a_rec]; exact h) (by rw [hbn, hb]; omega) m (by omega)

end AntihydraCheck

theorem solution
    (a : Nat → Nat) (b : Nat → Int)
    (a_ini : a 0 = 8)
    (a_rec : ∀ n, a (n + 1) = (3 * a n) / 2)
    (b_ini : b 0 = 0)
    (b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ n, n ≤ 2000 → b n ≥ 0 := by
  intro n hn
  have hc : AntihydraCheck.chk 10000 8 0 = true := by decide +kernel
  have h := AntihydraCheck.key a b a_rec b_rec 10000 0 0 (by rw [a_ini]; exact hc)
    (by rw [b_ini]; omega) n (by omega)
  rw [Nat.zero_add] at h
  exact h
