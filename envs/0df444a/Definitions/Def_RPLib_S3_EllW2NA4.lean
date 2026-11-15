-- Prove2me | Definitions.Def_RPLib_S3_EllW2NA4
-- name    : RPLib_S3_EllW2NA4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:20:54.023144+00:00
-- url     : https://prove2.me/theorems/895dfe32-1bfb-4422-8d39-66d2f022f738
-- title:
--   The Eichler-Selberg trace formula in weight two: the zero mode of the NHS kernel is bounded uniformly
-- statement:
--   The zero mode of the NHS kernel is bounded uniformly.
--
--   * `summable_zmct`: the `(c, t)` zero-mode series is (absolutely) summable on `ℤ × ℤ`.
--   * `BNA_nonneg`, `summable_BNA`, `tsum_BNA_le`: `Σ'_c BNA M n s c ≤ CNA M n` for `0 < s ≤ 1`.
--   * **`norm_zeroMode_NHS_le`**: for `0 < n`, `0 < s ≤ 1`, `1 ≤ y`,
--     `‖∫_{-1/2}^{1/2} NHS M n δ' s (x + y i) dx‖ ≤ CNA M n` (independent of `s` and `y`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2NA3

/-!
# S3-ES-Wt2 (O6, file NA4): the zero mode of the NHS kernel is bounded uniformly

* `summable_zmct`: the `(c, t)` zero-mode series is (absolutely) summable on `ℤ × ℤ`.
* `BNA_nonneg`, `summable_BNA`, `tsum_BNA_le`: `Σ'_c BNA M n s c ≤ CNA M n` for `0 < s ≤ 1`.
* **`norm_zeroMode_NHS_le`**: for `0 < n`, `0 < s ≤ 1`, `1 ≤ y`,
  `‖∫_{-1/2}^{1/2} NHS M n δ' s (x + y i) dx‖ ≤ CNA M n` (independent of `s` and `y`).
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

theorem summable_zmct {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    Summable fun ct : ℤ × ℤ => Wc M n δ' ct.1 ct.2 * ∫ u, VNZ n s y ct.1 ct.2 u := by
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  set G : ℤ × ℤ → ℝ := fun ct => if ct.1 = 0 then 0 else
    (n : ℝ) ^ s * (‖WcF M n δ' ct.1 ct.2‖ * ∫ u, VS s ct.1 n u y ct.2) with hG
  have hG0 : 0 ≤ G := fun ct => by
    simp only [hG]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.rpow_nonneg hn' s) (mul_nonneg (norm_nonneg _)
        (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _))
  set K := (n : ℝ) ^ s * (KZ M n s y * (2 * π ^ 2 * (y ^ 2) ^ (-s))) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (Real.rpow_nonneg hn' s) (mul_nonneg (KZ_nonneg n hs.le hy) (by positivity))
  have hfib : ∀ c : ℤ, Summable (fun t => G (c, t)) ∧
      ∑' t, G (c, t) ≤ K * |(c : ℝ)| ^ (-(1 + 2 * s)) := by
    intro c
    by_cases hc : c = 0
    · subst hc
      have h0 : ∀ t, G (0, t) = 0 := fun t => by simp [hG]
      simp only [h0, tsum_zero]
      exact ⟨summable_zero, mul_nonneg hK0 (by positivity)⟩
    · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      obtain ⟨hsu, hle⟩ := tsum_WcF_IU_le hn δ' hc hs.le hy
      have e : (fun t => G (c, t)) =
          fun t => (n : ℝ) ^ s * (‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t) := by
        funext t; simp only [hG, if_neg hc]
      rw [e, tsum_mul_left]
      refine ⟨hsu.mul_left _, ?_⟩
      calc (n : ℝ) ^ s * ∑' t, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t
          ≤ (n : ℝ) ^ s * (KZ M n s y * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|))) :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hn' s)
        _ = K * |(c : ℝ)| ^ (-(1 + 2 * s)) := by rw [rpow_c_identity hc' s y, hK]; ring
  have hsZ := Real.summable_abs_int_rpow (show 1 < 1 + 2 * s by linarith)
  have hsC : Summable fun c : ℤ => ∑' t, G (c, t) :=
    Summable.of_nonneg_of_le (fun c => tsum_nonneg fun t => hG0 (c, t)) (fun c => (hfib c).2)
      (hsZ.mul_left K)
  have hsG : Summable G := (summable_prod_of_nonneg hG0).2 ⟨fun c => (hfib c).1, hsC⟩
  refine Summable.of_norm_bounded hsG fun ct => ?_
  obtain ⟨c, t⟩ := ct
  by_cases hc : c = 0
  · subst hc
    simp [VNZ_zero, hG]
  · have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hint : ‖∫ u, VN s c n u y t‖ ≤ (n : ℝ) ^ s * ∫ u, VS s c n u y t := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp_rw [norm_VN s hc' hy.ne' hn']
      exact integral_const_mul _ _
    simp only [hG, if_neg hc, VNZ_of_ne n s y hc t]
    rw [norm_mul]
    calc ‖Wc M n δ' c t‖ * ‖∫ u, VN s c n u y t‖
        ≤ ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) :=
          mul_le_mul (norm_Wc_le n δ' c t) hint (norm_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) ^ s * (‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t) := by ring

lemma CN1_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ CN1 M n := by
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  unfold CN1; exact mul_nonneg (mNA_nonneg n) (mul_nonneg (by positivity) hn')

lemma CN2_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ CN2 M n := by
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  unfold CN2; exact mul_nonneg (mul_nonneg (by positivity) hn') (mNA_nonneg n)

lemma CN3_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ CN3 M n := by
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  unfold CN3; exact mul_nonneg (mul_nonneg (by positivity) hn') (by positivity)

lemma CN4_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ CN4 M n := by
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
  unfold CN4; exact mul_nonneg (mul_nonneg hn' (Nat.cast_nonneg _)) (by positivity)

lemma BNA_nonneg {n : ℤ} (hn : 0 ≤ n) {s : ℝ} (hs : 0 ≤ s) (c : ℤ) : 0 ≤ BNA M n s c := by
  unfold BNA
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (CN1_nonneg hn) (mul_nonneg hs (Real.rpow_nonneg (abs_nonneg _) _)))
    (mul_nonneg (CN2_nonneg hn) (Real.rpow_nonneg (abs_nonneg _) _)))
    (mul_nonneg (CN3_nonneg hn) (fp_fW_nonneg _ _)))
    (mul_nonneg (CN4_nonneg hn) (Real.rpow_nonneg (abs_nonneg _) _))

/-- The uniform bound of the zero mode. -/
def CNA (M : ℕ) [NeZero M] (n : ℤ) : ℝ :=
  CN1 M n * 3 + CN2 M n * 4 + CN3 M n * (2 * CW (N0f M n)) + CN4 M n * 10

lemma hasSum_BNA (n : ℤ) {s : ℝ} (hs : 0 < s) :
    HasSum (BNA M n s) (CN1 M n * (s * ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s))) +
      CN2 M n * (∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ)))) +
      CN3 M n * (∑' c : ℤ, KL.fp (fW (N0f M n)) c.natAbs) +
      CN4 M n * (∑' c : ℤ, |(c : ℝ)| ^ (-(5 / 4 : ℝ)))) := by
  have h1 := (((Real.summable_abs_int_rpow (show 1 < 1 + 2 * s by linarith)).hasSum).mul_left s).mul_left
    (CN1 M n)
  have h2 := ((Real.summable_abs_int_rpow (show (1 : ℝ) < 1 + 2 * (1 / 2) by norm_num)).hasSum).mul_left
    (CN2 M n)
  have h3 := ((summable_fW_int (sixteen_le_N0f M n)).hasSum).mul_left (CN3 M n)
  have h4 := (summable_abs_int_rpow54.hasSum).mul_left (CN4 M n)
  exact ((h1.add h2).add h3).add h4

theorem tsum_BNA_le {n : ℤ} (hn : 0 ≤ n) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∑' c : ℤ, BNA M n s c ≤ CNA M n := by
  rw [(hasSum_BNA n hs).tsum_eq]
  have hS1 : s * ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * s)) ≤ 3 := by
    have h := mul_le_mul_of_nonneg_left (tsum_abs_int_rpow_le hs) hs.le
    rw [mul_add, mul_one_div_cancel hs.ne'] at h
    linarith
  have hS2 : ∑' c : ℤ, |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) ≤ 4 := by
    have h := tsum_abs_int_rpow_le (s := 1 / 2) (by norm_num)
    have e : (2 : ℝ) + 1 / (1 / 2) = 4 := by norm_num
    rw [e] at h
    exact h
  have hS3 := tsum_fW_int_le (sixteen_le_N0f M n)
  have hS4 := tsum_abs_int_rpow54_le
  unfold CNA
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hS1 (CN1_nonneg hn)) (mul_le_mul_of_nonneg_left hS2 (CN2_nonneg hn)))
    (mul_le_mul_of_nonneg_left hS3 (CN3_nonneg hn))) (mul_le_mul_of_nonneg_left hS4 (CN4_nonneg hn))

/-- **NA (O6 zero mode).** The zero mode of `NHS` is bounded uniformly in `0 < s ≤ 1`, `y ≥ 1`. -/
theorem norm_zeroMode_NHS_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖∫ x in (-(1 / 2 : ℝ))..(1 / 2), NHS M n δ' s (ofComplex ((x : ℂ) + y * I))‖ ≤ CNA M n := by
  have hy0 : 0 < y := by linarith
  rw [zeroMode_NHS hn δ' hs (by linarith), (summable_zmct hn δ' hs hy0).tsum_prod]
  refine (tsum_of_norm_bounded (hasSum_BNA (M := M) n hs).summable.hasSum
    fun c => ?_).trans (tsum_BNA_le hn.le hs hs1)
  by_cases hc : c = 0
  · subst hc
    simp only [VNZ_zero, integral_zero, mul_zero, tsum_zero, norm_zero]
    exact BNA_nonneg hn.le hs.le 0
  · have e : ∀ t : ℤ, ∫ u, VNZ n s y c t u = ∫ u, VN s c n u y t := fun t => by
      rw [VNZ_of_ne n s y hc t]
    simp only [e]
    exact norm_tsum_Wc_intVN_le_BNA hn δ' hc hs hs1 hy

end RamanujanPetersson.EllW2


