-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV6a
-- name    : RPLib_S3_EllW2MV6a
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:19:35.543903+00:00
-- url     : https://prove2.me/theorems/fc77f9d6-ea09-4793-b5f8-8bfc8e5d0e99
-- title:
--   The Eichler-Selberg trace formula in weight two: `Σ_{k ≤ N, k ≡ r} Nk(k)/k` as a double sum of AP counts
-- statement:
--   `Σ_{k ≤ N, k ≡ r} Nk(k)/k` as a double sum of AP counts.
--
--   * `gm m j = [j ⊥ m] μ(j)/j`, `Am m r = φ(e)/e` with `e = gcd(r̃, m)`; `gm_zero`, `abs_gm_le`.
--   * `Nk_div_eq`: `Nk(k)/k = Σ_{h ∣ |n|} [h ∣ k] φ(k/h)/(k/h)`.
--   * `gcd_eq_of_cast`, `phi_div_res`: on `k ≡ r (m)`, `h ⊥ m`, `h ∣ k`: `φ(k/h)/(k/h) = A_r Σ_{j ∣ k/h} g(j)`.
--   * `card_dvd_res`, `cntI_zero`, `cntI_le`.
--   * **`sum_res_eq`** (`n ≠ 0`, `|n| ⊥ m`):
--     `Σ_{k ∈ [1,N], k ≡ r} Nk(k)/k = Σ_{h ∣ |n|} A_r Σ_{j ≤ N} g(j) · cntI m (h j) r (N/(h j))`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV3a
import Definitions.Def_RPLib_S3_EllW2MV4
import Definitions.Def_RPLib_S3_EllW2MV5

/-!
# S3-ES-Wt2 (O6, file MV6a): `Σ_{k ≤ N, k ≡ r} Nk(k)/k` as a double sum of AP counts

* `gm m j = [j ⊥ m] μ(j)/j`, `Am m r = φ(e)/e` with `e = gcd(r̃, m)`; `gm_zero`, `abs_gm_le`.
* `Nk_div_eq`: `Nk(k)/k = Σ_{h ∣ |n|} [h ∣ k] φ(k/h)/(k/h)`.
* `gcd_eq_of_cast`, `phi_div_res`: on `k ≡ r (m)`, `h ⊥ m`, `h ∣ k`: `φ(k/h)/(k/h) = A_r Σ_{j ∣ k/h} g(j)`.
* `card_dvd_res`, `cntI_zero`, `cntI_le`.
* **`sum_res_eq`** (`n ≠ 0`, `|n| ⊥ m`):
  `Σ_{k ∈ [1,N], k ≡ r} Nk(k)/k = Σ_{h ∣ |n|} A_r Σ_{j ≤ N} g(j) · cntI m (h j) r (N/(h j))`.
-/

open Finset

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open scoped ArithmeticFunction.Moebius

/-- `g_m(j) = [j ⊥ m] μ(j)/j`. -/
def gm (m j : ℕ) : ℝ := if j.Coprime m then (μ j : ℝ) / j else 0

/-- `A_m(r) = φ(e)/e`, `e = gcd(r̃, m)`. -/
def Am (m : ℕ) [NeZero m] (r : ZMod m) : ℝ :=
  ((Nat.gcd r.val m).totient : ℝ) / (Nat.gcd r.val m)

lemma gm_zero (m : ℕ) : gm m 0 = 0 := by simp [gm]

lemma abs_gm_le (m j : ℕ) : |gm m j| ≤ 1 / j := abs_muR_le m j

variable {m : ℕ} [NeZero m]

lemma Nk_div_eq {n : ℤ} (hn : n ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    (Nk n k : ℝ) / k = ∑ h ∈ n.natAbs.divisors,
      if h ∣ k then ((k / h).totient : ℝ) / ((k / h : ℕ) : ℝ) else 0 := by
  rw [Nk, Nat.cast_sum, Finset.sum_div, ← Finset.sum_filter]
  have hs : k.divisors.filter (fun h : ℕ => (h : ℤ) ∣ n) = n.natAbs.divisors.filter (· ∣ k) := by
    ext h
    simp only [Finset.mem_filter, Nat.mem_divisors, Int.ofNat_dvd_left]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, Int.natAbs_ne_zero.2 hn⟩, h1⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hk⟩, h1⟩
  rw [hs]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_filter] at hh
  have hh0 : h ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hh.1)
  obtain ⟨t, rfl⟩ := hh.2
  rw [Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hh0)]
  push_cast
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.2 hh0)

lemma gcd_eq_of_cast {k : ℕ} {r : ZMod m} (hk : (k : ZMod m) = r) :
    Nat.gcd k m = Nat.gcd r.val m := by
  rw [← hk, ZMod.val_natCast, Nat.gcd_comm, Nat.gcd_rec]

lemma phi_div_res {h k : ℕ} (hhm : h.Coprime m) (hk0 : k ≠ 0) (hhk : h ∣ k) {r : ZMod m}
    (hk : (k : ZMod m) = r) :
    ((k / h).totient : ℝ) / ((k / h : ℕ) : ℝ) = Am m r * ∑ j ∈ (k / h).divisors, gm m j := by
  obtain ⟨t, rfl⟩ := hhk
  have hh0 : 0 < h := Nat.pos_of_ne_zero (left_ne_zero_of_mul hk0)
  rw [Nat.mul_div_cancel_left t hh0, phi_div_eq m (right_ne_zero_of_mul hk0), Am,
    ← gcd_eq_of_cast hk, Nat.Coprime.gcd_mul_left_cancel t hhm]
  rfl

lemma sum_divisors_eq_range (f : ℕ → ℝ) {t N : ℕ} (ht0 : t ≠ 0) (ht : t ≤ N) :
    ∑ j ∈ t.divisors, f j = ∑ j ∈ range (N + 1), if j ∣ t then f j else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, _⟩
    exact ⟨by have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) h1; omega, h1⟩
  · rintro ⟨_, h1⟩; exact ⟨h1, ht0⟩

lemma card_dvd_res {a : ℕ} (ha : 0 < a) (r : ZMod m) (N : ℕ) :
    #{k ∈ Icc 1 N | a ∣ k ∧ (k : ZMod m) = r} = cntI m a r (N / a) := by
  have hc := card_dvd_filter_eq m 1 a N ha r
  simp only [one_mul] at hc
  exact hc

lemma cntI_zero (a : ℕ) (r : ZMod m) : cntI m a r 0 = 0 := by simp [cntI]

lemma cntI_le (a : ℕ) (r : ZMod m) (I : ℕ) : cntI m a r I ≤ I :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem sum_res_inner {h : ℕ} (hh : 0 < h) (hhm : h.Coprime m) (r : ZMod m) (N : ℕ) :
    ∑ k ∈ Icc 1 N, (if (k : ZMod m) = r then
      (if h ∣ k then ((k / h).totient : ℝ) / ((k / h : ℕ) : ℝ) else 0) else 0) =
    Am m r * ∑ j ∈ range (N + 1), gm m j * cntI m (h * j) r (N / (h * j)) := by
  have hterm : ∀ k ∈ Icc 1 N, (if (k : ZMod m) = r then
      (if h ∣ k then ((k / h).totient : ℝ) / ((k / h : ℕ) : ℝ) else 0) else 0) =
      ∑ j ∈ range (N + 1), if h * j ∣ k ∧ (k : ZMod m) = r then Am m r * gm m j else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hkr : (k : ZMod m) = r
    · by_cases hhk : h ∣ k
      · have hkh0 : k / h ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hhk) hh).ne'
        rw [if_pos hkr, if_pos hhk, phi_div_res hhm (by omega) hhk hkr,
          sum_divisors_eq_range (gm m) hkh0 (le_trans (Nat.div_le_self k h) hk.2), Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : h * j ∣ k
        · rw [if_pos ((Nat.dvd_div_iff_mul_dvd hhk).2 hj), if_pos ⟨hj, hkr⟩]
        · rw [if_neg (fun h' => hj ((Nat.dvd_div_iff_mul_dvd hhk).1 h')),
            if_neg (fun h' => hj h'.1), mul_zero]
      · rw [if_pos hkr, if_neg hhk]
        exact (Finset.sum_eq_zero fun j _ => if_neg fun h' => hhk (dvd_of_mul_right_dvd h'.1)).symm
    · rw [if_neg hkr]
      exact (Finset.sum_eq_zero fun j _ => if_neg fun h' => hkr h'.2).symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [gm_zero]; ring
  · rw [card_dvd_res (Nat.mul_pos hh hj) r N]; ring

/-- **MV6a**: the residue-class sum of `Nk(k)/k` as a double sum of AP counts. -/
theorem sum_res_eq {n : ℤ} (hn : n ≠ 0) (hnm : Nat.Coprime n.natAbs m) (r : ZMod m) (N : ℕ) :
    ∑ k ∈ Icc 1 N, (if (k : ZMod m) = r then (Nk n k : ℝ) / k else 0) =
      ∑ h ∈ n.natAbs.divisors,
        Am m r * ∑ j ∈ range (N + 1), gm m j * cntI m (h * j) r (N / (h * j)) := by
  have hterm : ∀ k ∈ Icc 1 N, (if (k : ZMod m) = r then (Nk n k : ℝ) / k else 0) =
      ∑ h ∈ n.natAbs.divisors, (if (k : ZMod m) = r then
        (if h ∣ k then ((k / h).totient : ℝ) / ((k / h : ℕ) : ℝ) else 0) else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    by_cases hkr : (k : ZMod m) = r
    · simp only [if_pos hkr]; exact Nk_div_eq hn (by omega)
    · simp only [if_neg hkr, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  exact sum_res_inner (Nat.pos_of_mem_divisors hh)
    (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hh) hnm) r N

end RamanujanPetersson.EllW2


