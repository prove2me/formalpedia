-- Prove2me | Definitions.Def_RPLib_S3_EllW2MV6b
-- name    : RPLib_S3_EllW2MV6b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:22:01.874514+00:00
-- url     : https://prove2.me/theorems/d96ab9b7-8487-4161-9db5-d0721da10d2e
-- title:
--   The Eichler-Selberg trace formula in weight two: the residue-class density of `Nk(k)/k`
-- statement:
--   The residue-class density of `Nk(k)/k`.
--
--   * `Cm m = Σ' j, [j ⊥ m] μ(j)/j²`; `Dm m n r = A_r · (Σ_{h ∣ |n|} 1/h) · C_m / m`.
--   * `norm_gm_div_le`, `summable_gm_div`.
--   * `tendsto_inner` (`h ⊥ m`): `(1/N) Σ_{j ≤ N} g(j) cntI m (h j) r (N/(h j)) → C_m/(h m)` (Tannery,
--     bound `1/j²`).
--   * **`tendsto_res`** (`n ≠ 0`, `|n| ⊥ m`): `(1/N) Σ_{k ∈ [1,N], k ≡ r (m)} Nk(k)/k → D_m(r)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Chapters 11 and 16

import Mathlib
import Definitions.Def_RPLib_S3_EllW2MV6a

/-!
# S3-ES-Wt2 (O6, file MV6b): the residue-class density of `Nk(k)/k`

* `Cm m = Σ' j, [j ⊥ m] μ(j)/j²`; `Dm m n r = A_r · (Σ_{h ∣ |n|} 1/h) · C_m / m`.
* `norm_gm_div_le`, `summable_gm_div`.
* `tendsto_inner` (`h ⊥ m`): `(1/N) Σ_{j ≤ N} g(j) cntI m (h j) r (N/(h j)) → C_m/(h m)` (Tannery,
  bound `1/j²`).
* **`tendsto_res`** (`n ≠ 0`, `|n| ⊥ m`): `(1/N) Σ_{k ∈ [1,N], k ≡ r (m)} Nk(k)/k → D_m(r)`.
-/

open Finset Filter Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- `C_m = Σ' j, [j ⊥ m] μ(j)/j²`. -/
def Cm (m : ℕ) : ℝ := ∑' j : ℕ, gm m j / j

/-- The residue density `D_m(r) = A_r · σ_{-1}(|n|) · C_m / m`. -/
def Dm (m : ℕ) [NeZero m] (n : ℤ) (r : ZMod m) : ℝ :=
  Am m r * (∑ h ∈ n.natAbs.divisors, (1 : ℝ) / h) * Cm m / m

lemma norm_gm_div_le (m j : ℕ) : ‖gm m j / j‖ ≤ 1 / (j : ℝ) ^ 2 := by
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  calc |gm m j| / j ≤ (1 / j) / j := div_le_div_of_nonneg_right (abs_gm_le m j) hj'.le
    _ = 1 / (j : ℝ) ^ 2 := by rw [div_div, sq]

lemma summable_gm_div (m : ℕ) : Summable (fun j : ℕ => gm m j / j) :=
  Summable.of_norm_bounded (Real.summable_one_div_nat_pow.2 one_lt_two) (norm_gm_div_le m)

variable {m : ℕ} [NeZero m]

theorem tendsto_inner {h : ℕ} (hh : 0 < h) (hhm : h.Coprime m) (r : ZMod m) :
    Tendsto (fun N : ℕ => (∑ j ∈ range (N + 1), gm m j * cntI m (h * j) r (N / (h * j))) / N)
      atTop (𝓝 (Cm m / (h * m))) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hsum : ∀ N : ℕ, (∑ j ∈ range (N + 1), gm m j * cntI m (h * j) r (N / (h * j))) / N =
      ∑' j : ℕ, gm m j * cntI m (h * j) r (N / (h * j)) / N := by
    intro N
    rw [Finset.sum_div, tsum_eq_sum (s := range (N + 1))]
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have h0 : N / (h * j) = 0 := Nat.div_eq_of_lt (by nlinarith)
    rw [h0, cntI_zero, Nat.cast_zero, mul_zero, zero_div]
  have hpt : ∀ j : ℕ, Tendsto (fun N : ℕ => gm m j * cntI m (h * j) r (N / (h * j)) / N) atTop
      (𝓝 (gm m j / j / (h * m))) := by
    intro j
    by_cases hj : j.Coprime m ∧ 0 < j
    · have hj' : (0 : ℝ) < j := by exact_mod_cast hj.2
      have ht := (tendsto_cntI_div (Nat.Coprime.mul hhm hj.1) r (Nat.mul_pos hh hj.2)).const_mul
        (gm m j)
      have he : gm m j * (1 / (((h * j : ℕ) : ℝ) * m)) = gm m j / j / (h * m) := by
        push_cast
        first | (field_simp; ring) | field_simp
      rw [← he]
      exact ht.congr fun N => (mul_div_assoc _ _ _).symm
    · have hg : gm m j = 0 := by
        rcases not_and_or.1 hj with h1 | h1
        · simp [gm, h1]
        · rw [Nat.eq_zero_of_not_pos h1, gm_zero]
      simp only [hg, zero_mul, zero_div]
      exact tendsto_const_nhds
  have hbd : ∀ N : ℕ, ∀ j : ℕ,
      ‖gm m j * cntI m (h * j) r (N / (h * j)) / N‖ ≤ 1 / (j : ℝ) ^ 2 := by
    intro N j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [gm_zero, zero_mul, zero_div, norm_zero]; positivity
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Nat.cast_zero, div_zero, norm_zero]; positivity
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (cntI m (h * j) r (N / (h * j)) : ℝ) ≤ N / j := by
      have h2 : cntI m (h * j) r (N / (h * j)) ≤ N / j :=
        (cntI_le _ _ _).trans (Nat.div_le_div_left (Nat.le_mul_of_pos_left j hh) hj)
      exact le_trans (by exact_mod_cast h2) Nat.cast_div_le
    rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]
    calc |gm m j| * (cntI m (h * j) r (N / (h * j)) : ℝ) / N ≤ (1 / j) * (N / j) / N :=
          div_le_div_of_nonneg_right (mul_le_mul (abs_gm_le m j) h1 (Nat.cast_nonneg _)
            (by positivity)) hN'.le
      _ = 1 / (j : ℝ) ^ 2 := by first | (field_simp; ring) | field_simp
  have hT := tendsto_tsum_of_dominated_convergence (Real.summable_one_div_nat_pow.2 one_lt_two)
    hpt (Eventually.of_forall hbd)
  have hC : (∑' j : ℕ, gm m j / j / (h * m)) = Cm m / (h * m) := by
    rw [Cm, tsum_div_const]
  rw [hC] at hT
  exact hT.congr fun N => (hsum N).symm

/-- **MV6**: `(1/N) Σ_{k ∈ [1,N], k ≡ r (m)} Nk(k)/k → D_m(r)`. -/
theorem tendsto_res {n : ℤ} (hn : n ≠ 0) (hnm : Nat.Coprime n.natAbs m) (r : ZMod m) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 N, (if (k : ZMod m) = r then (Nk n k : ℝ) / k else 0)) / N)
      atTop (𝓝 (Dm m n r)) := by
  have hfun : (fun N : ℕ =>
      (∑ k ∈ Icc 1 N, (if (k : ZMod m) = r then (Nk n k : ℝ) / k else 0)) / N) =
      fun N : ℕ => ∑ h ∈ n.natAbs.divisors, Am m r *
        ((∑ j ∈ range (N + 1), gm m j * cntI m (h * j) r (N / (h * j))) / N) := by
    funext N
    rw [sum_res_eq hn hnm r N, Finset.sum_div]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_div_assoc]
  rw [hfun]
  have hD : Dm m n r = ∑ h ∈ n.natAbs.divisors, Am m r * (Cm m / (h * m)) := by
    rw [Dm, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hD]
  exact tendsto_finsetSum _ fun h hh => (tendsto_inner (Nat.pos_of_mem_divisors hh)
    (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_divisors hh) hnm) r).const_mul (Am m r)

end RamanujanPetersson.EllW2


