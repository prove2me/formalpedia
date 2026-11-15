-- Prove2me | Definitions.Def_RPLib_S3_EllW2NA2
-- name    : RPLib_S3_EllW2NA2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:10:25.602126+00:00
-- url     : https://prove2.me/theorems/0998c3f0-4194-4567-9c19-0eb985cca2fb
-- title:
--   The Eichler-Selberg trace formula in weight two: the zero-mode contribution of one modulus `c`, integrated over `u`
-- statement:
--   The zero-mode contribution of one modulus `c`, integrated over `u`.
--
--   * `HNA M n δ' s y c u`: an explicit integrable majorant in `u` of `‖Σ'_t Wc(c,t) VN(c,t,u)‖`
--     (`norm_tsum_Wc_VN_le`: NA1 + PN4 + the exceptional `t`).
--   * `integrable_HNA`, `integral_HNA` (closed form).
--   * **`norm_tsum_Wc_intVN_le`**: for `c ≠ 0`, `0 < n`, `0 ≤ s`, `0 < y`,
--     `‖Σ'_t Wc(c,t) ∫_u VN(c,t,u)‖ ≤ ∫_u HNA` (closed form), by swapping `Σ'_t` and `∫_u`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2NA1

/-!
# S3-ES-Wt2 (O6, file NA2): the zero-mode contribution of one modulus `c`, integrated over `u`

* `HNA M n δ' s y c u`: an explicit integrable majorant in `u` of `‖Σ'_t Wc(c,t) VN(c,t,u)‖`
  (`norm_tsum_Wc_VN_le`: NA1 + PN4 + the exceptional `t`).
* `integrable_HNA`, `integral_HNA` (closed form).
* **`norm_tsum_Wc_intVN_le`**: for `c ≠ 0`, `0 < n`, `0 ≤ s`, `0 < y`,
  `‖Σ'_t Wc(c,t) ∫_u VN(c,t,u)‖ ≤ ∫_u HNA` (closed form), by swapping `Σ'_t` and `∫_u`.
-/

open MeasureTheory Set Filter Complex
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- The explicit `u`-majorant of the zero-mode integrand of the modulus `c`. -/
def HNA (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) (c : ℤ) (u : ℝ) : ℝ :=
  ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) *
      (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ)) +
    (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
      ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))))) +
    ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * VS s c n u y t)

theorem norm_tsum_Wc_VN_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    ‖∑' t : ℤ, Wc M n δ' c t * VN s c n u y t‖ ≤ HNA M n δ' s y c u := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [tsum_Wc_mul hn δ' c _ (summable_WcF_VN hn δ' hc hs hy u)]
  set E := ∑' t : ℤ, WcF M n δ' c t * VN s c n u y t - muc M n δ' c * ∫ t, VN s c n u y t with hE
  have e : ∑' t : ℤ, WcF M n δ' c t * VN s c n u y t -
      ∑ t ∈ excF n, WcF M n δ' c t * VN s c n u y t =
      muc M n δ' c * (∫ t, VN s c n u y t) + E - ∑ t ∈ excF n, WcF M n δ' c t * VN s c n u y t := by
    rw [hE]; ring
  rw [e]
  have h1 : ‖muc M n δ' c * ∫ t, VN s c n u y t‖ ≤
      ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) *
        (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ)) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_VN_le_final hs hc' hy hn0) (norm_nonneg _)
  have h2 : ‖E‖ ≤ (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
      ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))))) :=
    (norm_tsum_WcF_VN_sub_le hn δ' hc hs hy u).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (integral_VS_le hs hc' hy hn') (Real.rpow_nonneg hn' s))
        (div_nonneg (by linarith) (by positivity))) (add_nonneg (norm_nonneg _) (Bd_nonneg n c)))
  have h3 : ‖∑ t ∈ excF n, WcF M n δ' c t * VN s c n u y t‖ ≤
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * VS s c n u y t) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul, norm_VN s hc' hy.ne' hn']
  calc _ ≤ ‖muc M n δ' c * (∫ t, VN s c n u y t) + E‖ +
        ‖∑ t ∈ excF n, WcF M n δ' c t * VN s c n u y t‖ := norm_sub_le _ _
    _ ≤ ‖muc M n δ' c * (∫ t, VN s c n u y t)‖ + ‖E‖ +
        ‖∑ t ∈ excF n, WcF M n δ' c t * VN s c n u y t‖ := by
          gcongr; exact norm_add_le _ _
    _ ≤ HNA M n δ' s y c u := add_le_add (add_le_add h1 h2) h3

lemma integrable_HNA {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    Integrable fun u => HNA M n δ' s y c u := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  unfold HNA
  exact ((((integrable_M34 hy).const_mul _).const_mul _).add
    ((((integrable_ubnd s (c : ℝ) hy).const_mul _).const_mul _).const_mul _)).add
    (integrable_finsetSum _ fun t _ => ((integrable_VS_u hs hc' hy hn' t).const_mul _).const_mul _)

theorem integral_HNA {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    ∫ u, HNA M n δ' s y c u =
      ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) *
          (2 ^ (3 / 4 : ℝ) * (y * K34))) +
        (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
          ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)))) +
        ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hA : Integrable fun u : ℝ => ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s *
      ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) * (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ)) :=
    ((integrable_M34 hy).const_mul _).const_mul _
  have hB : Integrable fun u : ℝ => (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
      ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))))) :=
    (((integrable_ubnd s (c : ℝ) hy).const_mul _).const_mul _).const_mul _
  have hCi : ∀ t ∈ excF n, Integrable fun u : ℝ => ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * VS s c n u y t) :=
    fun t _ => ((integrable_VS_u hs hc' hy hn' t).const_mul _).const_mul _
  have hC : Integrable fun u : ℝ => ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * VS s c n u y t) :=
    integrable_finsetSum _ hCi
  have hAB : Integrable fun u : ℝ => ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s *
      ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) * (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ)) +
      (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
      ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))))) :=
    hA.add hB
  have e1 : ∫ u : ℝ, ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s *
      ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) * (2 * y ^ 2 / (u ^ 2 + y ^ 2)) ^ (3 / 4 : ℝ)) =
      ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) *
          (2 ^ (3 / 4 : ℝ) * (y * K34))) := by
    rw [integral_const_mul, integral_const_mul, integral_M34 hy]
  have e2 : ∫ u : ℝ, (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
      ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π * y / (|(c : ℝ)| * (u ^ 2 + y ^ 2)))))) =
      (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
          ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)))) := by
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_ubnd s hc' hy]
  have e3 : ∫ u : ℝ, ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * VS s c n u y t) =
      ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) := by
    rw [integral_finsetSum _ hCi]
    exact Finset.sum_congr rfl fun t _ => by rw [integral_const_mul, integral_const_mul]
  unfold HNA
  rw [integral_add hAB hC, integral_add hA hB, e1, e2, e3]

/-- **NA2.** The zero-mode contribution of one modulus `c ≠ 0`, bounded in closed form. -/
theorem norm_tsum_Wc_intVN_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) :
    ‖∑' t : ℤ, Wc M n δ' c t * ∫ u, VN s c n u y t‖ ≤
      ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) *
          (2 ^ (3 / 4 : ℝ) * (y * K34))) +
        (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
          ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)))) +
        ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hI : ∀ t : ℤ, Integrable fun u => Wc M n δ' c t * VN s c n u y t :=
    fun t => (integrable_VN_u hs hc' hy hn' t).const_mul _
  have hsumN : Summable fun t : ℤ => ∫ u, ‖Wc M n δ' c t * VN s c n u y t‖ := by
    have e : ∀ t : ℤ, ∫ u, ‖Wc M n δ' c t * VN s c n u y t‖ =
        ‖Wc M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) := by
      intro t
      simp_rw [norm_mul, norm_VN s hc' hy.ne' hn']
      rw [integral_const_mul, integral_const_mul]
    simp_rw [e]
    refine ((tsum_WcF_IU_le hn δ' hc hs hy).1.mul_left ((n : ℝ) ^ s)).of_nonneg_of_le
      (fun t => ?_) (fun t => ?_)
    · exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hn' s)
        (integral_nonneg fun u => VS_nonneg s hc' hy.ne' hn' t))
    · calc ‖Wc M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t)
          ≤ ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) :=
            mul_le_mul_of_nonneg_right (norm_Wc_le n δ' c t) (mul_nonneg (Real.rpow_nonneg hn' s)
              (integral_nonneg fun u => VS_nonneg s hc' hy.ne' hn' t))
        _ = (n : ℝ) ^ s * (‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t) := by ring
  have hex : ∑' t : ℤ, Wc M n δ' c t * ∫ u, VN s c n u y t =
      ∫ u, ∑' t : ℤ, Wc M n δ' c t * VN s c n u y t := by
    rw [← integral_tsum_of_summable_integral_norm hI hsumN]
    exact tsum_congr fun t => (integral_const_mul _ _).symm
  rw [hex]
  refine ((norm_integral_le_integral_norm _).trans ?_).trans_eq (integral_HNA hn δ' hc hs hy)
  exact integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
    (integrable_HNA hn δ' hc hs hy) (Eventually.of_forall fun u => norm_tsum_Wc_VN_le hn δ' hc hs hy u)

end RamanujanPetersson.EllW2


