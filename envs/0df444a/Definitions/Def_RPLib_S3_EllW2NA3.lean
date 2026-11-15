-- Prove2me | Definitions.Def_RPLib_S3_EllW2NA3
-- name    : RPLib_S3_EllW2NA3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:17:21.895631+00:00
-- url     : https://prove2.me/theorems/bec727b6-003a-48f1-8677-09758bbb672f
-- title:
--   The Eichler-Selberg trace formula in weight two: the modulus-`c` zero-mode bound, uniform in `y ≥ 1`, `0 < s ≤ 1`
-- statement:
--   The modulus-`c` zero-mode bound, uniform in `y ≥ 1`, `0 < s ≤ 1`.
--
--   * `mNA M n = n L / 2` (bounds `‖μ_c‖`), constants `CN1 … CN4` (independent of `c`, `s`, `y`).
--   * `BNA M n s c = CN1 · s|c|^(-(1+2s)) + CN2 · |c|^(-2) + CN3 · fp (fW N0) |c| + CN4 · |c|^(-5/4)`.
--   * **`norm_tsum_Wc_intVN_le_BNA`**: for `c ≠ 0`, `0 < n`, `0 < s ≤ 1`, `1 ≤ y`,
--     `‖Σ'_t Wc(c,t) ∫_u VN(c,t,u)‖ ≤ BNA M n s c` (from NA2 `norm_tsum_Wc_intVN_le`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2NA2

/-!
# S3-ES-Wt2 (O6, file NA3): the modulus-`c` zero-mode bound, uniform in `y ≥ 1`, `0 < s ≤ 1`

* `mNA M n = n L / 2` (bounds `‖μ_c‖`), constants `CN1 … CN4` (independent of `c`, `s`, `y`).
* `BNA M n s c = CN1 · s|c|^(-(1+2s)) + CN2 · |c|^(-2) + CN3 · fp (fW N0) |c| + CN4 · |c|^(-5/4)`.
* **`norm_tsum_Wc_intVN_le_BNA`**: for `c ≠ 0`, `0 < n`, `0 < s ≤ 1`, `1 ≤ y`,
  `‖Σ'_t Wc(c,t) ∫_u VN(c,t,u)‖ ≤ BNA M n s c` (from NA2 `norm_tsum_Wc_intVN_le`).
-/

open MeasureTheory Set Filter Complex
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma rpow_c_div {c : ℝ} (hc : c ≠ 0) (s y : ℝ) :
    (c ^ 2 * y ^ 2) ^ (-s) / |c| = (y ^ 2) ^ (-s) * |c| ^ (-(1 + 2 * s)) := by
  have hπ : (2 * π ^ 2 : ℝ) ≠ 0 := by positivity
  refine mul_left_cancel₀ hπ ?_
  calc 2 * π ^ 2 * ((c ^ 2 * y ^ 2) ^ (-s) / |c|) = (c ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |c|) := by
        ring
    _ = 2 * π ^ 2 * (y ^ 2) ^ (-s) * |c| ^ (-(1 + 2 * s)) := rpow_c_identity hc s y
    _ = 2 * π ^ 2 * ((y ^ 2) ^ (-s) * |c| ^ (-(1 + 2 * s))) := by ring

/-- The bound `n L / 2` for `‖μ_c‖`. -/
def mNA (M : ℕ) [NeZero M] (n : ℤ) : ℝ := (n.toNat : ℝ) * (Fintype.card (Fin 2 → ZMod M) : ℝ) / 2

lemma mNA_nonneg (n : ℤ) : 0 ≤ mNA M n := by unfold mNA; positivity

def CN1 (M : ℕ) [NeZero M] (n : ℤ) : ℝ := mNA M n * (16 * K34 ^ 2 * 2 ^ (3 / 4 : ℝ) * n)
def CN2 (M : ℕ) [NeZero M] (n : ℤ) : ℝ := 10 * π ^ 2 * n * mNA M n
def CN3 (M : ℕ) [NeZero M] (n : ℤ) : ℝ :=
  10 * π ^ 2 * n * (33 * (Fintype.card (Fin 2 → ZMod M) : ℝ) * (M : ℝ) ^ ((33 : ℝ) / 32))
def CN4 (M : ℕ) [NeZero M] (n : ℤ) : ℝ :=
  n * ((excF n).card : ℝ) * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * π)

/-- The uniform bound for the modulus `c`. -/
def BNA (M : ℕ) [NeZero M] (n : ℤ) (s : ℝ) (c : ℤ) : ℝ :=
  CN1 M n * (s * |(c : ℝ)| ^ (-(1 + 2 * s))) + CN2 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) +
    CN3 M n * KL.fp (fW (N0f M n)) c.natAbs + CN4 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ))

theorem norm_tsum_Wc_intVN_le_BNA {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {c : ℤ} (hc : c ≠ 0)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖∑' t : ℤ, Wc M n δ' c t * ∫ u, VN s c n u y t‖ ≤ BNA M n s c := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hca : 0 < |(c : ℝ)| := abs_pos.2 hc'
  have hc1 : 1 ≤ |(c : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
  have hy0 : 0 < y := by linarith
  have hnZ : (1 : ℤ) ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnZ
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hns : (n : ℝ) ^ s ≤ n :=
    (Real.rpow_le_rpow_of_exponent_le hn1 hs1).trans_eq (Real.rpow_one _)
  have hns0 : 0 ≤ (n : ℝ) ^ s := Real.rpow_nonneg hn0 s
  have hyy : 1 ≤ y ^ 2 := by nlinarith
  have hc2 : 1 ≤ (c : ℝ) ^ 2 := by rw [← sq_abs]; nlinarith
  have hy2 : (y ^ 2) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hyy (by linarith)
  have hX1 : ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_mul_of_one_le_of_one_le hc2 hyy) (by linarith)
  have hX0 : 0 ≤ ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) := Real.rpow_nonneg (by positivity) _
  have hmuc : ‖muc M n δ' c‖ ≤ mNA M n := norm_muc_le hn δ' hc
  have hL : (0 : ℝ) ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := by positivity
  refine (norm_tsum_Wc_intVN_le hn δ' hc hs.le hy0).trans ?_
  -- the main term
  have h1 : ‖muc M n δ' c‖ * (16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) /
      (|(c : ℝ)| * y) * (2 ^ (3 / 4 : ℝ) * (y * K34))) ≤ CN1 M n * (s * |(c : ℝ)| ^ (-(1 + 2 * s))) := by
    have e1 : 16 * K34 * s * (n : ℝ) ^ s * ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / (|(c : ℝ)| * y) *
        (2 ^ (3 / 4 : ℝ) * (y * K34)) =
        16 * K34 ^ 2 * 2 ^ (3 / 4 : ℝ) * s * (n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / |(c : ℝ)|) := by
      field_simp
    have hK : 0 ≤ 16 * K34 ^ 2 * 2 ^ (3 / 4 : ℝ) * s := mul_nonneg (by positivity) hs.le
    have hXZ : ((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / |(c : ℝ)| ≤ |(c : ℝ)| ^ (-(1 + 2 * s)) := by
      rw [rpow_c_div hc' s y]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hca.le _) hy2
    rw [e1]
    calc ‖muc M n δ' c‖ * (16 * K34 ^ 2 * 2 ^ (3 / 4 : ℝ) * s * (n : ℝ) ^ s *
          (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) / |(c : ℝ)|))
        ≤ mNA M n * (16 * K34 ^ 2 * 2 ^ (3 / 4 : ℝ) * s * n * |(c : ℝ)| ^ (-(1 + 2 * s))) :=
          mul_le_mul hmuc (mul_le_mul (mul_le_mul_of_nonneg_left hns hK) hXZ
            (div_nonneg hX0 hca.le) (mul_nonneg hK hn0))
            (mul_nonneg (mul_nonneg hK hns0) (div_nonneg hX0 hca.le)) (mNA_nonneg n)
      _ = CN1 M n * (s * |(c : ℝ)| ^ (-(1 + 2 * s))) := by unfold CN1; ring
  -- the error term
  have h2 : (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
      ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|)))) ≤
      CN2 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) + CN3 M n * KL.fp (fW (N0f M n)) c.natAbs := by
    have hq : (4 + s) / (|(c : ℝ)| * y) ≤ 5 / |(c : ℝ)| := by
      rw [div_le_div_iff₀ (mul_pos hca hy0) hca]
      nlinarith [mul_le_mul_of_nonneg_left hy hca.le, mul_le_mul_of_nonneg_right hs1 hca.le]
    have hz : |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) = (|(c : ℝ)| ^ 2)⁻¹ := by
      rw [show (-(1 + 2 * (1 / 2 : ℝ))) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hca.le,
        Real.rpow_natCast]
    have hN : ((c.natAbs : ℕ) : ℝ) = |(c : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have hP : 0 ≤ 2 * π ^ 2 / |(c : ℝ)| := by positivity
    calc (‖muc M n δ' c‖ + Bd M n c) * ((4 + s) / (|(c : ℝ)| * y) *
          ((n : ℝ) ^ s * (((c : ℝ) ^ 2 * y ^ 2) ^ (-s) * (2 * π ^ 2 / |(c : ℝ)|))))
        ≤ (mNA M n + Bd M n c) * (5 / |(c : ℝ)| * ((n : ℝ) * (1 * (2 * π ^ 2 / |(c : ℝ)|)))) :=
          mul_le_mul (add_le_add hmuc le_rfl) (mul_le_mul hq (mul_le_mul hns
            (mul_le_mul_of_nonneg_right hX1 hP) (mul_nonneg hX0 hP) hn0)
            (mul_nonneg hns0 (mul_nonneg hX0 hP)) (by positivity))
            (mul_nonneg (div_nonneg (by linarith) (mul_pos hca hy0).le)
              (mul_nonneg hns0 (mul_nonneg hX0 hP)))
            (add_nonneg (mNA_nonneg n) (Bd_nonneg n c))
      _ = CN2 M n * |(c : ℝ)| ^ (-(1 + 2 * (1 / 2 : ℝ))) + CN3 M n * KL.fp (fW (N0f M n)) c.natAbs := by
          unfold CN2 CN3 Bd
          rw [hz, hN]
          field_simp
          ring
  -- the exceptional terms
  have h3 : ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t) ≤
      CN4 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ)) := by
    have hS0 : 0 ≤ ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t :=
      Finset.sum_nonneg fun t _ => mul_nonneg (norm_nonneg _)
        (integral_nonneg fun u => VS_nonneg' _ _ _ _ _ _)
    have hLy : (Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) * (y ^ 2) ^ (-s) ≤
        (Fintype.card (Fin 2 → ZMod M) : ℝ) * π :=
      (mul_le_mul (mul_le_mul_of_nonneg_left (div_le_self Real.pi_pos.le hy) hL) hy2
        (Real.rpow_nonneg (by positivity) _) (by positivity)).trans_eq (mul_one _)
    calc ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ((n : ℝ) ^ s * ∫ u, VS s c n u y t)
        = (n : ℝ) ^ s * ∑ t ∈ excF n, ‖WcF M n δ' c t‖ * ∫ u, VS s c n u y t := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
      _ ≤ (n : ℝ) * (((excF n).card : ℝ) * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (π / y) *
            (y ^ 2) ^ (-s)) * |(c : ℝ)| ^ (-(5 / 4 : ℝ))) :=
          mul_le_mul hns (exc_sum_le hn.le δ' hc hs.le hy0) hS0 hn0
      _ ≤ (n : ℝ) * (((excF n).card : ℝ) * ((Fintype.card (Fin 2 → ZMod M) : ℝ) * π) *
            |(c : ℝ)| ^ (-(5 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLy (Nat.cast_nonneg _)) (Real.rpow_nonneg hca.le _)) hn0
      _ = CN4 M n * |(c : ℝ)| ^ (-(5 / 4 : ℝ)) := by unfold CN4; ring
  unfold BNA
  linarith [h1, h2, h3]

end RamanujanPetersson.EllW2


