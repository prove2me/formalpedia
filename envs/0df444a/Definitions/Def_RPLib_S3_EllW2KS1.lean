-- Prove2me | Definitions.Def_RPLib_S3_EllW2KS1
-- name    : RPLib_S3_EllW2KS1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:42:21.993197+00:00
-- url     : https://prove2.me/theorems/9ed7478d-6146-4d2e-bac4-2a7315353939
-- title:
--   The Eichler-Selberg trace formula in weight two: exact scaling of the `R^(-s-1)` zero-mode integral
-- statement:
--   Exact scaling of the `R^(-s-1)` zero-mode integral.
--
--   `Qe ε μ τ = (μ² + 1 − τ² + ε)² + 4τ²`.
--   * `Qe_factor`: if `m² = μ² + ε` then `Qe ε μ τ = (1 + (m − τ)²)(1 + (m + τ)²)`; `one_le_Qe` (`ε ≥ 0`).
--   * `Qe0_le_nine_mul` (`0 ≤ ε ≤ 1`): `Qe 0 μ τ ≤ 9 Qe ε μ τ`.
--   * `Rp_scale`: `Rp c n (y μ) y (2 c y τ) = (c y)² Qe (n / (c y)²) μ τ`.
--   * `integral_VS_scale`: `∫ u, ∫ t, VS s c n u y t = 2/|c| · ((c y)²)^(-s) · KS s (n/(c y)²)`,
--     `KS s ε = ∫ μ, ∫ τ, Qe ε μ τ ^ (-s-1)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2P

/-!
# S3-ES-Wt2 (KS1): exact scaling of the `R^(-s-1)` zero-mode integral

`Qe ε μ τ = (μ² + 1 − τ² + ε)² + 4τ²`.
* `Qe_factor`: if `m² = μ² + ε` then `Qe ε μ τ = (1 + (m − τ)²)(1 + (m + τ)²)`; `one_le_Qe` (`ε ≥ 0`).
* `Qe0_le_nine_mul` (`0 ≤ ε ≤ 1`): `Qe 0 μ τ ≤ 9 Qe ε μ τ`.
* `Rp_scale`: `Rp c n (y μ) y (2 c y τ) = (c y)² Qe (n / (c y)²) μ τ`.
* `integral_VS_scale`: `∫ u, ∫ t, VS s c n u y t = 2/|c| · ((c y)²)^(-s) · KS s (n/(c y)²)`,
  `KS s ε = ∫ μ, ∫ τ, Qe ε μ τ ^ (-s-1)`.
-/

set_option autoImplicit false

open MeasureTheory Real

noncomputable section

namespace RamanujanPetersson.EllW2

/-- The normalised profile. -/
def Qe (ε μ τ : ℝ) : ℝ := (μ ^ 2 + 1 - τ ^ 2 + ε) ^ 2 + 4 * τ ^ 2

/-- The normalised double integral. -/
def KS (s ε : ℝ) : ℝ := ∫ μ : ℝ, ∫ τ : ℝ, Qe ε μ τ ^ (-s - 1)

lemma Qe_factor {ε μ τ m : ℝ} (h : μ ^ 2 + ε = m ^ 2) :
    Qe ε μ τ = (1 + (m - τ) ^ 2) * (1 + (m + τ) ^ 2) := by
  unfold Qe
  linear_combination (μ ^ 2 + ε + m ^ 2 + 2 - 2 * τ ^ 2) * h

lemma Qe_zero (μ τ : ℝ) : Qe 0 μ τ = (1 + (μ - τ) ^ 2) * (1 + (μ + τ) ^ 2) :=
  Qe_factor (by ring)

lemma one_le_Qe {ε : ℝ} (hε : 0 ≤ ε) (μ τ : ℝ) : 1 ≤ Qe ε μ τ := by
  rw [Qe_factor (m := √(μ ^ 2 + ε)) (Real.sq_sqrt (by positivity)).symm]
  exact one_le_mul_of_one_le_of_one_le (by nlinarith [sq_nonneg (√(μ ^ 2 + ε) - τ)])
    (by nlinarith [sq_nonneg (√(μ ^ 2 + ε) + τ)])

lemma Qe_pos {ε : ℝ} (hε : 0 ≤ ε) (μ τ : ℝ) : 0 < Qe ε μ τ :=
  lt_of_lt_of_le one_pos (one_le_Qe hε μ τ)

lemma Qe_neg_mu (ε μ τ : ℝ) : Qe ε (-μ) τ = Qe ε μ τ := by
  unfold Qe; ring

lemma one_add_sq_le_three_mul {a b : ℝ} (h0 : 0 ≤ b - a) (h1 : b - a ≤ 1) :
    1 + a ^ 2 ≤ 3 * (1 + b ^ 2) := by
  nlinarith [sq_nonneg (a + b), mul_nonneg h0 (sub_nonneg.2 h1)]

lemma Qe0_le_nine_mul {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (μ τ : ℝ) :
    Qe 0 μ τ ≤ 9 * Qe ε μ τ := by
  set m := √(μ ^ 2 + ε) with hmdef
  have hm : m ^ 2 = μ ^ 2 + ε := Real.sq_sqrt (by positivity)
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have ha0 : 0 ≤ |μ| := abs_nonneg μ
  have hsa : |μ| ^ 2 = μ ^ 2 := sq_abs μ
  have hlo : |μ| ≤ m := by nlinarith
  have hhi : m ≤ |μ| + 1 := by nlinarith
  rw [Qe_factor (m := |μ|) (by rw [hsa]; ring), Qe_factor hm.symm]
  have k1 : 1 + (|μ| - τ) ^ 2 ≤ 3 * (1 + (m - τ) ^ 2) :=
    one_add_sq_le_three_mul (by linarith) (by linarith)
  have k2 : 1 + (|μ| + τ) ^ 2 ≤ 3 * (1 + (m + τ) ^ 2) :=
    one_add_sq_le_three_mul (by linarith) (by linarith)
  have p1 : 0 ≤ 1 + (|μ| - τ) ^ 2 := by positivity
  have p2 : 0 ≤ 1 + (|μ| + τ) ^ 2 := by positivity
  calc (1 + (|μ| - τ) ^ 2) * (1 + (|μ| + τ) ^ 2)
      ≤ (3 * (1 + (m - τ) ^ 2)) * (3 * (1 + (m + τ) ^ 2)) :=
        mul_le_mul k1 k2 p2 (by positivity)
    _ = 9 * ((1 + (m - τ) ^ 2) * (1 + (m + τ) ^ 2)) := by ring

/-! ## Scaling -/

lemma Rp_scale {c n y : ℝ} (hc : c ≠ 0) (hy : y ≠ 0) (μ τ : ℝ) :
    Rp c n (y * μ) y (2 * c * y * τ) = (c * y) ^ 2 * Qe (n / (c * y) ^ 2) μ τ := by
  unfold Rp RcN Qe
  field_simp
  ring

lemma VS_scale (s : ℝ) {c n y : ℝ} (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (μ τ : ℝ) :
    VS s c n (y * μ) y (2 * c * y * τ) =
      ((c * y) ^ 2) ^ (-s - 1) * Qe (n / (c * y) ^ 2) μ τ ^ (-s - 1) := by
  unfold VS
  rw [Rp_scale hc hy, Real.mul_rpow (sq_nonneg _) (Qe_pos (by positivity) μ τ).le]

lemma integral_scale (g : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) : ∫ t, g t = |a| * ∫ τ, g (a * τ) := by
  rw [Measure.integral_comp_mul_left g a, smul_eq_mul, ← mul_assoc, abs_inv,
    mul_inv_cancel₀ (abs_ne_zero.2 ha), one_mul]

theorem integral_VS_scale (s : ℝ) {c n y : ℝ} (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    ∫ u, ∫ t, VS s c n u y t = 2 / |c| * ((c * y) ^ 2) ^ (-s) * KS s (n / (c * y) ^ 2) := by
  have hy0 : y ≠ 0 := hy.ne'
  have ha : 2 * c * y ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) hy0
  have h1 : ∀ μ : ℝ, ∫ t, VS s c n (y * μ) y t = |2 * c * y| *
      (((c * y) ^ 2) ^ (-s - 1) * ∫ τ, Qe (n / (c * y) ^ 2) μ τ ^ (-s - 1)) := by
    intro μ
    rw [integral_scale _ ha]
    congr 1
    simp_rw [VS_scale s hc hy0 hn]
    exact integral_const_mul _ _
  rw [integral_scale _ hy0]
  simp_rw [h1]
  rw [integral_const_mul, integral_const_mul]
  unfold KS
  rw [Real.rpow_sub_one (pow_ne_zero 2 (mul_ne_zero hc hy0))]
  generalize (∫ μ : ℝ, ∫ τ : ℝ, Qe (n / (c * y) ^ 2) μ τ ^ (-s - 1)) = K
  generalize ((c * y) ^ 2) ^ (-s) = X
  have hca : 0 < |c| := abs_pos.2 hc
  rw [abs_mul, abs_mul, abs_two, abs_of_pos hy, mul_pow, ← sq_abs c]
  field_simp

end RamanujanPetersson.EllW2


