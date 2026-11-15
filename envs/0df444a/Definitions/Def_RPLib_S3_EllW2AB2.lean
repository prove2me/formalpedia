-- Prove2me | Definitions.Def_RPLib_S3_EllW2AB2
-- name    : RPLib_S3_EllW2AB2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:43:01.338887+00:00
-- url     : https://prove2.me/theorems/4d264675-6601-4e88-8066-f07a28a7917e
-- title:
--   The Eichler-Selberg trace formula in weight two: the main term `s · Σ'_c Jm c → π² l / 2`
-- statement:
--   The main term `s · Σ'_c Jm c → π² l / 2`.
--
--   * `fpm m = ‖μ_m‖ + ‖μ_{-m}‖`; `scale_aux`; `intVS_eq` (`∫∫ VS = |c|^(-(1+2s)) · kerY`);
--     `Jm_eq`, `Jm_add_neg` (`Jm m + Jm (-m) = Fab fpm s m · kerY n y s m`).
--   * `tsum_Jm_eq`: `Σ'_c Jm c = Σ'_m Fab fpm s m · kerY n y s m` (`0 < s ≤ 1`).
--   * **`tendsto_main`**: if the Cesàro mean of `fpm` is `l` then `s · Σ'_c Jm c → π² (l/2)`.
--   * **`tendsto_ZS`**: then also `s · ZS M n δ' s y → π² (l/2)` (by `abs_ZS_sub_le`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2AB1
import Definitions.Def_RPLib_S3_EllW2ZD2

/-!
# S3-ES-Wt2 (O6, file AB2): the main term `s · Σ'_c Jm c → π² l / 2`

* `fpm m = ‖μ_m‖ + ‖μ_{-m}‖`; `scale_aux`; `intVS_eq` (`∫∫ VS = |c|^(-(1+2s)) · kerY`);
  `Jm_eq`, `Jm_add_neg` (`Jm m + Jm (-m) = Fab fpm s m · kerY n y s m`).
* `tsum_Jm_eq`: `Σ'_c Jm c = Σ'_m Fab fpm s m · kerY n y s m` (`0 < s ≤ 1`).
* **`tendsto_main`**: if the Cesàro mean of `fpm` is `l` then `s · Σ'_c Jm c → π² (l/2)`.
* **`tendsto_ZS`**: then also `s · ZS M n δ' s y → π² (l/2)` (by `abs_ZS_sub_le`).
-/

open Filter Topology Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- The symmetrised modulus weights. -/
def fpm (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (m : ℕ) : ℝ :=
  ‖muc M n δ' (m : ℤ)‖ + ‖muc M n δ' (-(m : ℤ))‖

lemma fpm_nonneg (n : ℤ) (δ' : ZMod M) (m : ℕ) : 0 ≤ fpm M n δ' m :=
  add_nonneg (norm_nonneg _) (norm_nonneg _)

lemma scale_aux {m : ℕ} (hm : 0 < m) (s y : ℝ) :
    2 / (m : ℝ) * (((m : ℝ) * y) ^ 2) ^ (-s) = (m : ℝ) ^ (-(1 + 2 * s)) * (2 * (y ^ 2) ^ (-s)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : ((m : ℝ) ^ 2) ^ (-s) = (m : ℝ) ^ (-2 * s) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hm'.le]
    congr 1; ring
  have e2 : (m : ℝ) ^ (-(1 + 2 * s)) = (m : ℝ)⁻¹ * (m : ℝ) ^ (-2 * s) := by
    rw [show -(1 + 2 * s) = -1 + -2 * s by ring, Real.rpow_add hm', Real.rpow_neg_one]
  rw [mul_pow, Real.mul_rpow (sq_nonneg _) (sq_nonneg _), e1, e2, div_eq_mul_inv]
  ring

lemma intVS_eq {n : ℤ} (hn : 0 ≤ n) {c : ℤ} (hc : c ≠ 0) (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫ u, ∫ t, VS s c n u y t = (c.natAbs : ℝ) ^ (-(1 + 2 * s)) * kerY n y s c.natAbs := by
  rw [integral_VS_scale s (by exact_mod_cast hc) hy (by exact_mod_cast hn)]
  have hA : |(c : ℝ)| = (c.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hsq : ((c : ℝ) * y) ^ 2 = ((c.natAbs : ℝ) * y) ^ 2 := by
    rw [mul_pow, mul_pow, ← hA, sq_abs]
  rw [hA, hsq, kerY, ← mul_assoc, scale_aux (Int.natAbs_pos.2 hc)]

lemma Jm_eq {n : ℤ} (hn : 0 ≤ n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0) (s : ℝ) {y : ℝ}
    (hy : 0 < y) :
    Jm M n δ' s y c = ‖muc M n δ' c‖ * ((c.natAbs : ℝ) ^ (-(1 + 2 * s)) * kerY n y s c.natAbs) := by
  rw [Jm, intVS_eq hn hc s hy]

lemma Jm_zero (n : ℤ) (δ' : ZMod M) (s y : ℝ) : Jm M n δ' s y 0 = 0 := by
  simp [Jm, muc_zero_left]

lemma Jm_add_neg {n : ℤ} (hn : 0 ≤ n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y) (m : ℕ) :
    Jm M n δ' s y (m : ℤ) + Jm M n δ' s y (-(m : ℤ)) = Fab (fpm M n δ') s m * kerY n y s m := by
  rcases Nat.eq_zero_or_pos m with h | hm
  · subst h
    simp [Jm, Fab, fpm, muc_zero_left]
  · have hc : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have hc' : -(m : ℤ) ≠ 0 := neg_ne_zero.2 hc
    rw [Jm_eq hn δ' hc s hy, Jm_eq hn δ' hc' s hy, Int.natAbs_neg, Int.natAbs_natCast, Fab, fpm]
    ring

theorem tsum_Jm_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {y : ℝ} (hy : 0 < y) :
    ∑' c : ℤ, Jm M n δ' s y c = ∑' m : ℕ, Fab (fpm M n δ') s m * kerY n y s m := by
  have h := tsum_nat_add_neg (abs_ZS_sub_le (M := M) hn δ' hs hs1 hy).1
  rw [Jm_zero, add_zero] at h
  rw [← h]
  exact tsum_congr fun m => Jm_add_neg hn.le δ' s hy m

theorem tendsto_main {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {l : ℝ}
    (hlim : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, fpm M n δ' k) / (N : ℝ)) atTop (𝓝 l))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => s * ∑' c : ℤ, Jm M n δ' s y c) (𝓝[>] 0) (𝓝 (π ^ 2 * (l / 2))) := by
  have hA := tendsto_abel_kerY (fpm_nonneg (M := M) n δ') hlim
    (show (0 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn.le) hy
  refine hA.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
  rw [tsum_Jm_eq hn δ' hs.1 hs.2 hy]

theorem tendsto_ZS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {l : ℝ}
    (hlim : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, fpm M n δ' k) / (N : ℝ)) atTop (𝓝 l))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => s * ZS M n δ' s y) (𝓝[>] 0) (𝓝 (π ^ 2 * (l / 2))) := by
  have hm := tendsto_main hn δ' hlim hy
  have h0 : Tendsto (fun s : ℝ => s * (KY y * CZD M n)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s * (KY y * CZD M n)) (𝓝 0) (𝓝 0) :=
      (continuous_mul_const (KY y * CZD M n)).tendsto' 0 0 (zero_mul _)
    exact h1.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun s : ℝ => s * (ZS M n δ' s y - ∑' c : ℤ, Jm M n δ' s y c)) (𝓝[>] 0)
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hs.1]
    exact mul_le_mul_of_nonneg_left (abs_ZS_sub_le (M := M) hn δ' hs.1 hs.2 hy).2 hs.1.le
  have h2 := hm.add hr
  rw [add_zero] at h2
  exact h2.congr fun s => by ring

end RamanujanPetersson.EllW2


