-- Prove2me | Definitions.Def_RPLib_S3_EllW2NA1
-- name    : RPLib_S3_EllW2NA1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:07:59.779299+00:00
-- url     : https://prove2.me/theorems/43eb7c43-4d8d-4fb2-8fe3-eec6913bf9fb
-- title:
--   The Eichler-Selberg trace formula in weight two: the Abel-summation bound for one modulus `c` and one shift `u`
-- statement:
--   The Abel-summation bound for one modulus `c` and one shift `u`.
--
--   * `Bd M n c = 33 · L · M^(33/32) · |c|² · fp (fW (N0f M n)) |c|` (the discrepancy constant of K4b), `Bd_nonneg`.
--   * **`norm_tsum_WcF_VN_sub_le`**: for `c ≠ 0`, `0 < n`, `0 ≤ s`, `0 < y` and every `u`,
--     `‖Σ'_t WcF(c,t) VN(c,t,u) - μ_c ∫_t VN(c,t,u)‖ ≤ (‖μ_c‖ + Bd) · (4+s)/(|c| y) · n^s ∫_t VS(c,t,u)`
--     (AS `norm_tsum_periodic_sub_le` with period `|c| M`, the K4b discrepancy, and the PN3 derivative bound).
--   * `summable_WcF_VN`: the `t`-series is summable.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2K4b
import Definitions.Def_RPLib_S3_EllW2NZ

/-!
# S3-ES-Wt2 (O6, file NA1): the Abel-summation bound for one modulus `c` and one shift `u`

* `Bd M n c = 33 · L · M^(33/32) · |c|² · fp (fW (N0f M n)) |c|` (the discrepancy constant of K4b), `Bd_nonneg`.
* **`norm_tsum_WcF_VN_sub_le`**: for `c ≠ 0`, `0 < n`, `0 ≤ s`, `0 < y` and every `u`,
  `‖Σ'_t WcF(c,t) VN(c,t,u) - μ_c ∫_t VN(c,t,u)‖ ≤ (‖μ_c‖ + Bd) · (4+s)/(|c| y) · n^s ∫_t VS(c,t,u)`
  (AS `norm_tsum_periodic_sub_le` with period `|c| M`, the K4b discrepancy, and the PN3 derivative bound).
* `summable_WcF_VN`: the `t`-series is summable.
-/

open MeasureTheory Set Filter Complex
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- The discrepancy constant of the modulus `c` (K4b). -/
def Bd (M : ℕ) [NeZero M] (n c : ℤ) : ℝ :=
  33 * (Fintype.card (Fin 2 → ZMod M) : ℝ) * (M : ℝ) ^ ((33 : ℝ) / 32) * (c.natAbs : ℝ) ^ 2 *
    KL.fp (fW (N0f M n)) c.natAbs

lemma Bd_nonneg (n c : ℤ) : 0 ≤ Bd M n c := by
  unfold Bd
  exact mul_nonneg (by positivity) (fp_fW_nonneg _ _)

theorem summable_WcF_VN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Summable fun t : ℤ => WcF M n δ' c t * VN s c n u y t := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  refine Summable.of_norm_bounded
    ((summable_VN (u := u) hs hc' hy hn').norm.mul_left
      (c.natAbs * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2)) (fun t => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_WcF_le n δ' c t) (norm_nonneg _)

theorem norm_tsum_WcF_VN_sub_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) {y : ℝ} (hy : 0 < y) (u : ℝ) :
    ‖∑' t : ℤ, WcF M n δ' c t * VN s c n u y t - muc M n δ' c * ∫ t, VN s c n u y t‖ ≤
      (‖muc M n δ' c‖ + Bd M n c) *
        ((4 + s) / (|(c : ℝ)| * y) * ((n : ℝ) ^ s * ∫ t, VS s c n u y t)) := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn.le
  have hq : 0 < c.natAbs * M := Nat.mul_pos (Int.natAbs_pos.2 hc) (NeZero.pos M)
  have hmain := norm_tsum_periodic_sub_le (f := fun t : ℤ => WcF M n δ' c t) (μ := muc M n δ' c) hq
    (fun t => WcF_periodic n δ' c t) (sum_WcF_eq n δ' hc) (Bd_nonneg n c)
    (fun m _ => norm_sum_WcF_sub_le_fW hn δ' hc m) (norm_WcF_le n δ' c)
    (hasDerivAt_VN (u := u) s hc' hy.ne' hn') (integrable_dVN (u := u) hs hc' hy hn')
    (integrable_VN (u := u) hs hc' hy hn') (summable_VN (u := u) hs hc' hy hn')
  refine hmain.trans (mul_le_mul_of_nonneg_left (integral_norm_dVN_le (u := u) hs hc' hy hn') ?_)
  exact add_nonneg (norm_nonneg _) (Bd_nonneg n c)

end RamanujanPetersson.EllW2


