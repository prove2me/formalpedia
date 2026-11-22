-- Prove2me | Definitions.Def_GirvingAKS_Misc_Log
-- name    : GirvingAKS_Misc_Log
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:29:39.555997+00:00
-- url     : https://prove2.me/theorems/b6c13e5f-bd9b-4dc2-875e-43d954b034aa
-- title:
--   AKS sorting networks (Seiferas port) — Kernel-Efficient Rational Logarithms
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Misc/Log.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Fuel-based structural recursion for computing `⌈log_{p/q}(a/b)⌉` over natural numbers, avoiding `Nat.find` which blocks kernel reduction when the existence proof goes through `Classical.choice`.
--
--   Key definitions:
--
--   - `Nat.ceilRatLog p q a b`: smallest `n` with `p^n · b ≥ q^n · a`
--   - `Rat.ceilLog base x`: `⌈log_base(x)⌉` wrapper for rationals
--
--   The fuel bound `q · a` is sufficient by Bernoulli's inequality: `(p/q)^n ≥ (1 + 1/q)^n ≥ 1 + n/q`, so at `n = q · a` we get `(p/q)^(q·a) ≥ 1 + a ≥ a ≥ a/b`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Misc/Log.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Order.Ring.Rat

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Misc/Log.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Kernel-Efficient Rational Logarithms

  Fuel-based structural recursion for computing `⌈log_{p/q}(a/b)⌉` over
  natural numbers, avoiding `Nat.find` which blocks kernel reduction when
  the existence proof goes through `Classical.choice`.

  Key definitions:
  - `Nat.ceilRatLog p q a b`: smallest `n` with `p^n · b ≥ q^n · a`
  - `Rat.ceilLog base x`: `⌈log_base(x)⌉` wrapper for rationals

  The fuel bound `q · a` is sufficient by Bernoulli's inequality:
  `(p/q)^n ≥ (1 + 1/q)^n ≥ 1 + n/q`, so at `n = q · a` we get
  `(p/q)^(q·a) ≥ 1 + a ≥ a ≥ a/b`.
-/


section

/-! **Nat-level ceil rational log** -/

/-- Inner loop for `Nat.ceilRatLog`: counts steps until `a · qn ≤ pn · b`,
    where `pn = p^n` and `qn = q^n` are tracked incrementally.
    Structural recursion on `fuel`. -/
def Nat.ceilRatLog.go (p q a b : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, pn, qn, acc =>
    if a * qn ≤ pn * b then acc
    else go p q a b fuel (pn * p) (qn * q) (acc + 1)

/-- `⌈log_{p/q}(a/b)⌉` = smallest `n` with `p^n · b ≥ q^n · a`.
    Returns 0 for degenerate inputs (`p ≤ q`, `q = 0`, or `b = 0`).
    Fuel = `q · a`, sufficient by Bernoulli's inequality. -/
def Nat.ceilRatLog (p q a b : ℕ) : ℕ :=
  if p ≤ q ∨ q = 0 ∨ b = 0 then 0
  else Nat.ceilRatLog.go p q a b (q * a) 1 1 0

/-- `⌈log_base(x)⌉` for `ℚ`. Extracts numerators and denominators, then
    delegates to `Nat.ceilRatLog`.

    Interprets `base = p/q` and `x = a/b`, computing the smallest `n` with
    `(p/q)^n ≥ a/b`, i.e., `p^n · b ≥ q^n · a`.

    Returns 0 when `base ≤ 1` or `x ≤ 0` (handled by the degenerate-input
    guard in `Nat.ceilRatLog`). -/
def Rat.ceilLog (base x : ℚ) : ℕ :=
  Nat.ceilRatLog base.num.natAbs base.den x.num.natAbs x.den


/-! **Kernel-reduction tests** -/

/-- `⌈log_{20/13}(20)⌉ = 7` — the `stagesFactor` for `seiferasParams`. -/
theorem ceilLog_20_13_20 : Rat.ceilLog (20 / 13) 20 = 7 := by decide +kernel

/-- `Nat.clog 2 58 = 6` — the number of squarings needed. -/
theorem clog2_58 : Nat.clog 2 58 = 6 := by decide +kernel


/-! **Rat helpers** -/

theorem Rat.den_lt_natAbs_num (q : ℚ) (h : 1 < q) : q.den < q.num.natAbs := by
  have key : (q.den : ℤ) < q.num := by
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    have h2 : (q.den : ℚ) < q.num := by
      have := lt_mul_of_one_lt_left hd h
      rwa [Rat.mul_den_eq_num] at this
    exact_mod_cast h2
  omega

theorem Rat.num_pos_of_pos (q : ℚ) (h : 0 < q) : 0 < q.num := by
  exact Rat.num_pos.mpr h


/-! **Bernoulli-style helper** -/

/-- First two terms of binomial theorem: `(q+1)^(n+1) ≥ q^(n+1) + (n+1)·q^n`. -/
theorem bernoulli_nat (q : ℕ) : ∀ n : ℕ,
    q ^ (n + 1) + (n + 1) * q ^ n ≤ (q + 1) ^ (n + 1) := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ (q + 1)]
    suffices h : q ^ (n + 1 + 1) + (n + 1 + 1) * q ^ (n + 1) =
                 (q ^ (n + 1) + (n + 1) * q ^ n) * q + q ^ (n + 1) by
      rw [h]
      exact Nat.add_le_add (Nat.mul_le_mul_right q ih) (Nat.pow_le_pow_left (by omega) _)
    ring

/-- Fuel sufficiency: for `p > q > 0`, `b > 0`, and `k ≥ q·a`,
    we have `a · q^k ≤ p^k · b`. -/
theorem fuel_sufficient {p q a b : ℕ} (hp : q < p) (hq : 0 < q) (hb : 0 < b)
    {k : ℕ} (hk : q * a ≤ k) : a * q ^ k ≤ p ^ k * b := by
  by_cases ha : a = 0
  · simp [ha]
  · rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp at hk; omega
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hbern := bernoulli_nat q k'
      have hqa : a * q ^ (k' + 1) ≤ (k' + 1) * q ^ k' := by
        rw [Nat.pow_succ]
        have : a * q ≤ k' + 1 := by have := Nat.mul_comm q a; omega
        calc a * (q ^ k' * q) = (a * q) * q ^ k' := by ring
          _ ≤ (k' + 1) * q ^ k' := Nat.mul_le_mul_right _ this
      calc a * q ^ (k' + 1)
          ≤ (k' + 1) * q ^ k' := hqa
        _ ≤ q ^ (k' + 1) + (k' + 1) * q ^ k' := Nat.le_add_left _ _
        _ ≤ (q + 1) ^ (k' + 1) := hbern
        _ ≤ p ^ (k' + 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ p ^ (k' + 1) * b := Nat.le_mul_of_pos_right _ hb


/-! **go correctness** -/

/-- `go` terminates immediately when the condition holds. -/
theorem Nat.ceilRatLog.go_of_le {p q a b : ℕ} {fuel pn qn acc : ℕ}
    (h : a * qn ≤ pn * b) (hf : 0 < fuel) :
    go p q a b fuel pn qn acc = acc := by
  cases fuel with
  | zero => omega
  | succ f => simp [go, h]

/-- `go` steps when condition doesn't hold. -/
theorem Nat.ceilRatLog.go_step {p q a b : ℕ} {fuel pn qn acc : ℕ}
    (h : ¬(a * qn ≤ pn * b)) :
    go p q a b (fuel + 1) pn qn acc = go p q a b fuel (pn * p) (qn * q) (acc + 1) := by
  simp [go, h]

/-- The result of `go` is between `acc` and `acc + fuel`. -/
theorem Nat.ceilRatLog.go_bounds (p q a b fuel pn qn acc : ℕ) :
    acc ≤ go p q a b fuel pn qn acc ∧
    go p q a b fuel pn qn acc ≤ acc + fuel := by
  induction fuel generalizing pn qn acc with
  | zero => simp [go]
  | succ fuel ih =>
    simp only [go]; split
    · exact ⟨le_rfl, by omega⟩
    · obtain ⟨h1, h2⟩ := ih (pn * p) (qn * q) (acc + 1)
      exact ⟨by omega, by omega⟩

/-- `go` with `pn = p^k`, `qn = q^k` satisfies the spec: the result `n`
    has `a · q^n ≤ p^n · b`, and `p^m · b < q^m · a` for `k ≤ m < n`. -/
theorem Nat.ceilRatLog.go_spec (p q a b : ℕ)
    (hp : q < p) (hq : 0 < q) (hb : 0 < b) :
    ∀ fuel k pn qn, pn = p ^ k → qn = q ^ k → k + fuel ≥ q * a →
    let n := go p q a b fuel pn qn k
    a * q ^ n ≤ p ^ n * b ∧ ∀ m, k ≤ m → m < n → p ^ m * b < a * q ^ m := by
  intro fuel; induction fuel with
  | zero =>
    intro k pn qn hpn hqn hfuel
    simp only [go]
    exact ⟨fuel_sufficient hp hq hb (by omega), fun m hm1 hm2 ↦ by omega⟩
  | succ fuel ih =>
    intro k pn qn hpn hqn hfuel
    simp only [go]; split
    · next h =>
      subst hpn; subst hqn
      exact ⟨h, fun m hm1 hm2 ↦ by omega⟩
    · next h =>
      push_neg at h
      have := ih (k + 1) (pn * p) (qn * q)
        (by rw [hpn]; ring) (by rw [hqn]; ring) (by omega)
      obtain ⟨hspec, hmin⟩ := this
      refine ⟨hspec, fun m hm1 hm2 ↦ ?_⟩
      by_cases heq : m = k
      · subst heq; subst hpn; subst hqn; exact h
      · exact hmin m (by omega) hm2


/-! **ceilRatLog correctness** -/

/-- `ceilRatLog` achieves the bound: `a · q^n ≤ p^n · b`. -/
theorem Nat.ceilRatLog_spec {p q a b : ℕ} (hp : q < p) (hq : 0 < q) (hb : 0 < b) :
    a * q ^ (Nat.ceilRatLog p q a b) ≤ p ^ (Nat.ceilRatLog p q a b) * b := by
  unfold Nat.ceilRatLog
  split
  · next h => simp; omega
  · next h =>
    push_neg at h
    exact (Nat.ceilRatLog.go_spec p q a b hp hq hb (q * a) 0 1 1 (by simp) (by simp) (by omega)).1

/-- `ceilRatLog` is minimal: for `m < n`, the bound doesn't hold. -/
theorem Nat.ceilRatLog_min {p q a b : ℕ} (hp : q < p) (hq : 0 < q) (hb : 0 < b)
    {m : ℕ} (hm : m < Nat.ceilRatLog p q a b) :
    p ^ m * b < a * q ^ m := by
  unfold Nat.ceilRatLog at hm
  split at hm
  · omega
  · exact (Nat.ceilRatLog.go_spec p q a b hp hq hb (q * a) 0 1 1 (by simp) (by simp) (by omega)).2 m (by omega) hm

/-- Monotonicity: if `a' ≤ a` and `b ≤ b'`, then `ceilRatLog p q a' b' ≤ ceilRatLog p q a b`.
    (Smaller ratio → smaller log.) -/
theorem Nat.ceilRatLog_mono {p q : ℕ} (hp : q < p) (hq : 0 < q)
    {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') (hb' : 0 < b) :
    Nat.ceilRatLog p q a' b' ≤ Nat.ceilRatLog p q a b := by
  by_contra hlt
  push_neg at hlt
  have hb'_pos : 0 < b' := by omega
  have h1 := ceilRatLog_min hp hq hb'_pos hlt
  have h2 := ceilRatLog_spec hp hq hb' (a := a) (b := b)
  -- h1: p^m * b' < a' * q^m  (from ceilRatLog_min)
  -- h2: a * q^m ≤ p^m * b
  -- Contradiction: a' ≤ a and b ≤ b' gives a'*q^m ≤ a*q^m ≤ p^m*b ≤ p^m*b'
  set m := Nat.ceilRatLog p q a b
  have h3 : a' * q ^ m ≤ a * q ^ m := Nat.mul_le_mul_right _ ha
  have h4 : p ^ m * b ≤ p ^ m * b' := Nat.mul_le_mul_left _ hb
  omega


/-- `ceilRatLog` is bounded by any `n` satisfying the spec. -/
theorem Nat.ceilRatLog_le_of_le {p q a b : ℕ} (hp : q < p) (hq : 0 < q) (hb : 0 < b)
    {n : ℕ} (h : a * q ^ n ≤ p ^ n * b) : Nat.ceilRatLog p q a b ≤ n := by
  by_contra hlt
  push_neg at hlt
  exact Nat.not_le.mpr (ceilRatLog_min hp hq hb hlt) h

/-! **ℚ ordering bridge** -/

/-- Cross-multiplication characterization: if `a, b` have positive numerators and
    `a.num.natAbs * b.den ≤ b.num.natAbs * a.den`, then `a ≤ b`. -/
theorem Rat.le_of_natAbs_mul_den_le {a b : ℚ} (ha : 0 < a.num) (hb : 0 < b.num)
    (h : a.num.natAbs * b.den ≤ b.num.natAbs * a.den) : a ≤ b := by
  show Rat.blt b a = false
  unfold Rat.blt
  split
  · next h1 =>
    rw [Bool.and_eq_true] at h1
    exact absurd (decide_eq_true_iff.mp h1.1) (by omega)
  · split
    · next h1 h2 => exact absurd h2 (by omega)
    · split
      · rfl
      · simp only [decide_eq_false_iff_not]
        intro hlt
        have h_int : (a.num.natAbs : ℤ) * b.den ≤ (b.num.natAbs : ℤ) * a.den := by exact_mod_cast h
        rw [Int.natAbs_of_nonneg (by omega : 0 ≤ a.num),
            Int.natAbs_of_nonneg (by omega : 0 ≤ b.num)] at h_int
        omega

/-- Converse cross-multiplication: `a ≤ b` with positive numerators implies
    `a.num.natAbs * b.den ≤ b.num.natAbs * a.den`. -/
theorem Rat.natAbs_mul_den_le_of_le {a b : ℚ} (ha : 0 < a.num) (hb : 0 < b.num)
    (h : a ≤ b) : a.num.natAbs * b.den ≤ b.num.natAbs * a.den := by
  by_contra hgt
  push_neg at hgt
  have hba : b ≤ a := Rat.le_of_natAbs_mul_den_le hb ha (by omega)
  have hab : a = b := le_antisymm h hba
  rw [hab] at hgt
  exact Nat.lt_irrefl _ hgt


/-! **Rat.ceilLog correctness** -/

/-- `Rat.ceilLog` achieves the bound (Nat-level statement). -/
theorem Rat.ceilLog_spec (base x : ℚ) (hbase : 1 < base) :
    let n := Rat.ceilLog base x
    x.num.natAbs * base.den ^ n ≤ base.num.natAbs ^ n * x.den :=
  Nat.ceilRatLog_spec (Rat.den_lt_natAbs_num base hbase) base.den_pos x.den_pos

/-- `Rat.ceilLog` is minimal (Nat-level statement). -/
theorem Rat.ceilLog_min (base x : ℚ) (hbase : 1 < base)
    {m : ℕ} (hm : m < Rat.ceilLog base x) :
    base.num.natAbs ^ m * x.den < x.num.natAbs * base.den ^ m :=
  Nat.ceilRatLog_min (Rat.den_lt_natAbs_num base hbase) base.den_pos x.den_pos hm

/-- `Rat.ceilLog` achieves the bound (ℚ-level): `x ≤ base ^ (ceilLog base x)`. -/
theorem Rat.ceilLog_le (base x : ℚ) (hbase : 1 < base) (hx : 0 < x) :
    x ≤ base ^ (Rat.ceilLog base x) := by
  have hbase_num_pos : 0 < base.num := Rat.num_pos.mpr (lt_trans zero_lt_one hbase)
  apply Rat.le_of_natAbs_mul_den_le (Rat.num_pos_of_pos x hx)
  · rw [Rat.num_pow]; exact Int.pow_pos hbase_num_pos
  · rw [Rat.den_pow, Rat.num_pow, Int.natAbs_pow]
    exact Rat.ceilLog_spec base x hbase

/-- `Rat.ceilLog` is monotone in `x`: larger `x` → larger log. -/
theorem Rat.ceilLog_mono_right {base : ℚ} (hbase : 1 < base) {x₁ x₂ : ℚ}
    (hx₁ : 0 < x₁) (hle : x₁ ≤ x₂) :
    Rat.ceilLog base x₁ ≤ Rat.ceilLog base x₂ := by
  apply Nat.ceilRatLog_le_of_le (Rat.den_lt_natAbs_num base hbase) base.den_pos x₁.den_pos
  have hx₂ : 0 < x₂ := lt_of_lt_of_le hx₁ hle
  have h_le_pow : x₁ ≤ base ^ Rat.ceilLog base x₂ :=
    le_trans hle (Rat.ceilLog_le base x₂ hbase hx₂)
  have hbase_num_pos : 0 < base.num := Rat.num_pos_of_pos base (lt_trans (by norm_num : (0:ℚ) < 1) hbase)
  have hpow_num_pos : 0 < (base ^ Rat.ceilLog base x₂).num := by
    rw [Rat.num_pow]; exact Int.pow_pos hbase_num_pos
  have h := Rat.natAbs_mul_den_le_of_le (Rat.num_pos_of_pos x₁ hx₁) hpow_num_pos h_le_pow
  rw [Rat.den_pow, Rat.num_pow, Int.natAbs_pow] at h
  exact h

/-- `Rat.ceilLog` minimality (ℚ-level): `base ^ m < x` for `m < ceilLog base x`. -/
theorem Rat.ceilLog_gt (base x : ℚ) (hbase : 1 < base) (hx : 0 < x)
    {m : ℕ} (hm : m < Rat.ceilLog base x) : base ^ m < x := by
  by_contra h
  push_neg at h
  -- h : x ≤ base^m → ceilLog base x ≤ m, contradicting hm
  have hbase_num_pos : 0 < base.num := Rat.num_pos_of_pos base (lt_trans (by norm_num : (0:ℚ) < 1) hbase)
  have hpow_num_pos : 0 < (base ^ m).num := by rw [Rat.num_pow]; exact Int.pow_pos hbase_num_pos
  have hnat := Rat.natAbs_mul_den_le_of_le (Rat.num_pos_of_pos x hx) hpow_num_pos h
  rw [Rat.den_pow, Rat.num_pow, Int.natAbs_pow] at hnat
  have : Rat.ceilLog base x ≤ m :=
    Nat.ceilRatLog_le_of_le (Rat.den_lt_natAbs_num base hbase) base.den_pos x.den_pos hnat
  omega

end


