-- Prove2me | Definitions.Def_RPLib_S3_KHF
-- name    : RPLib_S3_KHF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:40:05.590489+00:00
-- url     : https://prove2.me/theorems/eb351840-0988-4d04-a451-a1be1be785d6
-- title:
--   Kronecker-Hurwitz class number relation: from matrices to `(t, form)` pairs, and the `t`-sum of class numbers
-- statement:
--   From matrices to `(t, form)` pairs, and the `t`-sum of class numbers.
--
--   * `psi N = (P + S, R, S - P, -Q)` (trace and fixed-point form); `W4_psi`, `W4_supp` (parity of `t - B`);
--   * **`bridge`** : `∑ᶠ_{Yn n} wN = ∑ᶠ t, ∑ᶠ Q, Wd (t² - 4n) Q`;
--   * **`tsum_eq`** : `Σ_{|t| ≤ 2n, t² ≤ 4n} H(4n - t²) = 2 ∑ᶠ t, ∑ᶠ Q, Wd (t² - 4n) Q - (1/12) #{t : t² = 4n}`.
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KHD
import Definitions.Def_RPLib_S3_KHE

/-!
# S3-KH, part F: from matrices to `(t, form)` pairs, and the `t`-sum of class numbers

* `psi N = (P + S, R, S - P, -Q)` (trace and fixed-point form); `W4_psi`, `W4_supp` (parity of `t - B`);
* **`bridge`** : `∑ᶠ_{Yn n} wN = ∑ᶠ t, ∑ᶠ Q, Wd (t² - 4n) Q`;
* **`tsum_eq`** : `Σ_{|t| ≤ 2n, t² ≤ 4n} H(4n - t²) = 2 ∑ᶠ t, ∑ᶠ Q, Wd (t² - 4n) Q - (1/12) #{t : t² = 4n}`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

open RamanujanPetersson.S3

/-- Trace and fixed-point form of `N`. -/
def psi (N : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ := (N.1 + N.2.2.2, N.2.2.1, N.2.2.2 - N.1, -N.2.1)

lemma psi_inj : Function.Injective psi := by
  rintro ⟨P, Q, R, S⟩ ⟨P', Q', R', S'⟩ h
  simp only [psi, Prod.mk.injEq] at h
  show (P, Q, R, S) = (P', Q', R', S')
  simp only [Prod.mk.injEq]
  omega

/-- `Wd` as a function of `(t, A, B, C)`. -/
def W4 (n : ℤ) (x : ℤ × ℤ × ℤ × ℤ) : ℚ := Wd (x.1 ^ 2 - 4 * n) x.2

lemma W4_psi (n : ℤ) (N : ℤ × ℤ × ℤ × ℤ) : W4 n (psi N) = (Yn n).indicator wN N := by
  classical
  obtain ⟨P, Q, R, S⟩ := N
  simp only [W4, psi, Wd, Yn, det4, Set.indicator_apply, Set.mem_ofPred_eq, wN]
  exact if_congr ⟨fun h => ⟨by linarith [h.1], h.2⟩, fun h => ⟨by linarith [h.1], h.2⟩⟩ rfl rfl

lemma W4_supp (n : ℤ) : Function.support (W4 n) ⊆ Set.range psi := by
  rintro ⟨t, A, B, C⟩ hx
  rw [Function.mem_support] at hx
  simp only [W4, Wd] at hx
  split_ifs at hx with h
  · obtain ⟨hd, -⟩ := h
    have h4 : Even ((t - B) * (t + B)) := ⟨2 * (n - A * C), by linear_combination (-1 : ℤ) * hd⟩
    have hev : Even (t - B) := by
      rcases Int.even_mul.1 h4 with h | h
      · exact h
      · have e : t - B = (t + B) - 2 * B := by ring
        rw [e]; exact h.sub (even_two_mul B)
    obtain ⟨k, hk⟩ := hev
    refine ⟨(k, -C, A, k + B), ?_⟩
    show (k + (k + B), A, k + B - k, - -C) = (t, A, B, C)
    rw [neg_neg, (by omega : k + (k + B) = t), (by ring : k + B - k = B)]
  · exact absurd rfl hx

/-- **Matrices to `(t, form)` pairs.** -/
theorem bridge {n : ℕ} (hn : 0 < n) :
    ∑ᶠ N, (Yn n).indicator wN N = ∑ᶠ (t : ℤ), ∑ᶠ Q, Wd (t ^ 2 - 4 * n) Q := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have fin : (Function.support (W4 n)).Finite := by
    refine ((Y_fin hn' (le_refl (Yn n))).image psi).subset fun x hx => ?_
    obtain ⟨N, rfl⟩ := W4_supp n hx
    exact ⟨N, by rw [Function.mem_support, ← W4_psi]; exact hx, rfl⟩
  rw [← finsum_congr (W4_psi n), fs_range psi_inj _ (W4_supp n)]
  exact finsum_curry (W4 n) fin

lemma Wd_zero (Q : ℤ × ℤ × ℤ) : Wd 0 Q = 0 := by
  obtain ⟨A, B, C⟩ := Q
  simp only [Wd]
  split_ifs with h
  · by_contra hw
    obtain ⟨h1, h2, h3⟩ := wt_ne h.2 hw
    nlinarith [h.1, h.2, mul_le_mul h2 h2 h1 h.2.le, mul_le_mul_of_nonneg_left h3 h.2.le]
  · rfl

/-- **The `t`-sum.** -/
theorem tsum_eq {n : ℕ} (hn : 0 < n) :
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
        hurwitzH (4 * (n : ℤ) - t ^ 2).toNat =
      2 * ∑ᶠ (t : ℤ), ∑ᶠ Q, Wd (t ^ 2 - 4 * n) Q -
        1 / 12 * ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
          (if t ^ 2 = 4 * (n : ℤ) then (1 : ℚ) else 0) := by
  classical
  set F := (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)) with hF
  have pt : ∀ t ∈ F, hurwitzH (4 * (n : ℤ) - t ^ 2).toNat =
      2 * ∑ᶠ Q, Wd (t ^ 2 - 4 * n) Q - 1 / 12 * (if t ^ 2 = 4 * (n : ℤ) then (1 : ℚ) else 0) := by
    intro t ht
    have ht' := (Finset.mem_filter.1 ht).2
    by_cases h : t ^ 2 = 4 * (n : ℤ)
    · rw [if_pos h, h, sub_self, (by rfl : (0 : ℤ).toNat = 0), hurwitzH, if_pos rfl]
      rw [(finsum_congr Wd_zero).trans finsum_zero]; norm_num
    · have hpos : 0 < (4 * (n : ℤ) - t ^ 2).toNat := by omega
      rw [if_neg h, hH hpos, Int.toNat_of_nonneg (by omega : 0 ≤ 4 * (n : ℤ) - t ^ 2), neg_sub]
      ring
  have hsub : Function.support (fun t : ℤ => ∑ᶠ Q, Wd (t ^ 2 - 4 * n) Q) ⊆ ↑F := by
    intro t ht
    rw [Function.mem_support] at ht
    obtain ⟨⟨A, B, C⟩, hQ⟩ : ∃ Q, Wd (t ^ 2 - 4 * n) Q ≠ 0 := by
      by_contra hc
      exact ht ((finsum_congr fun Q => Classical.byContradiction fun h => hc ⟨Q, h⟩).trans finsum_zero)
    simp only [Wd] at hQ
    split_ifs at hQ with h
    · obtain ⟨h1, h2, h3⟩ := wt_ne h.2 hQ
      have hlt : t ^ 2 < 4 * (n : ℤ) := by
        nlinarith [h.1, h.2, mul_le_mul h2 h2 h1 h.2.le, mul_le_mul_of_nonneg_left h3 h.2.le]
      have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
      rw [hF, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc]
      exact ⟨⟨by nlinarith, by nlinarith⟩, hlt.le⟩
    · exact absurd rfl hQ
  rw [Finset.sum_congr rfl pt, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← finsum_eq_sum_of_support_subset _ hsub]

end RamanujanPetersson.S3.KH


