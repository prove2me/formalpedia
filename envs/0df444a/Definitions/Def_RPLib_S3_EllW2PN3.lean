-- Prove2me | Definitions.Def_RPLib_S3_EllW2PN3
-- name    : RPLib_S3_EllW2PN3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:45:40.683957+00:00
-- url     : https://prove2.me/theorems/c31f2495-fe66-4cc8-8a44-30c0cd4dec70
-- title:
--   The Eichler-Selberg trace formula in weight two: the NHS zero-mode profile `VN`
-- statement:
--   The NHS zero-mode profile `VN`.
--
--   At a real trace `t`, `VN s = y² n^s Q⁻² Rp^(-s)` (`Q = Qp`, file PN2).
--   * `hasDerivAt_VN` (derivative `dVN`), `continuous_VN`.
--   * `norm_VN_eq`, **`norm_VN`**: `|VN| = n^s VS s`.
--   * **`norm_dVN_le`**: `|∂_t VN| ≤ (4 + s)/(|c| y) |VN|`.
--   * `integrable_VN`, `integrable_dVN`, `summable_VN`, `integral_norm_dVN_le`, `norm_integral_VN_le`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2PN2

/-!
# S3-ES-Wt2 (O6, file PN3): the NHS zero-mode profile `VN`

At a real trace `t`, `VN s = y² n^s Q⁻² Rp^(-s)` (`Q = Qp`, file PN2).
* `hasDerivAt_VN` (derivative `dVN`), `continuous_VN`.
* `norm_VN_eq`, **`norm_VN`**: `|VN| = n^s VS s`.
* **`norm_dVN_le`**: `|∂_t VN| ≤ (4 + s)/(|c| y) |VN|`.
* `integrable_VN`, `integrable_dVN`, `summable_VN`, `integral_norm_dVN_le`, `norm_integral_VN_le`.
-/

open MeasureTheory Set Filter Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

/-- The NHS zero-mode profile at a real trace `t`: `y² n^s Q⁻² Rp^(-s)`. -/
def VN (s c n u y t : ℝ) : ℂ :=
  ((y ^ 2 * n ^ s : ℝ) : ℂ) * ((Qp c n u y t ^ 2)⁻¹ * ((Rp c n u y t ^ (-s) : ℝ) : ℂ))

/-- `∂_t VN`. -/
def dVN (s c n u y t : ℝ) : ℂ :=
  ((y ^ 2 * n ^ s : ℝ) : ℂ) * (dinvQ c n u y t * ((Rp c n u y t ^ (-s) : ℝ) : ℂ) +
    (Qp c n u y t ^ 2)⁻¹ * ((dRp c n u y t * (-s) * Rp c n u y t ^ (-s - 1) : ℝ) : ℂ))

variable {c n u y : ℝ}

lemma Rp_nonneg (t : ℝ) : 0 ≤ Rp c n u y t := by
  rw [Rp_eq_Pq]
  positivity

lemma hasDerivAt_VN (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    HasDerivAt (VN s c n u y) (dVN s c n u y t) t := by
  have hR := Rp_pos (u := u) hc hy hn t
  have h1 := hasDerivAt_invQ (u := u) hc hy hn t
  have h2 : HasDerivAt (fun t => ((Rp c n u y t ^ (-s) : ℝ) : ℂ))
      (((dRp c n u y t * (-s) * Rp c n u y t ^ (-s - 1) : ℝ) : ℂ)) t :=
    ((hasDerivAt_Rp hc hy hn t).rpow_const (Or.inl hR.ne')).ofReal_comp
  exact (h1.mul h2).const_mul _

lemma continuous_VN (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) : Continuous (VN s c n u y) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_VN s hc hy hn t).continuousAt

lemma norm_VN_eq (s : ℝ) (hn : 0 ≤ n) (t : ℝ) :
    ‖VN s c n u y t‖ = y ^ 2 * n ^ s * (‖(Qp c n u y t ^ 2)⁻¹‖ * Rp c n u y t ^ (-s)) := by
  have hA : 0 ≤ y ^ 2 * n ^ s := mul_nonneg (sq_nonneg y) (Real.rpow_nonneg hn s)
  rw [VN, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hA,
    Real.norm_of_nonneg (Real.rpow_nonneg (Rp_nonneg t) _)]

lemma VS_zero_mul (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    VS 0 c n u y t * Rp c n u y t ^ (-s) = VS s c n u y t := by
  have hR := Rp_pos (u := u) hc hy hn t
  rw [VS, VS, ← Real.rpow_add hR]
  congr 1
  ring

/-- **`|VN| = n^s VS s`.** -/
lemma norm_VN (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) (t : ℝ) :
    ‖VN s c n u y t‖ = n ^ s * VS s c n u y t := by
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  rw [norm_VN_eq s hn, norm_inv_Qp_sq hy, ← VS_zero_mul s hc hy hn t,
    show ∀ a b d e : ℝ, a * b * (a⁻¹ * d * e) = (a * a⁻¹) * (b * (d * e)) from
      fun a b d e => by ring, mul_inv_cancel₀ hy2, one_mul]

lemma abs_dRpow_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    |dRp c n u y t * (-s) * Rp c n u y t ^ (-s - 1)| ≤ s / (|c| * y) * Rp c n u y t ^ (-s) := by
  have hR := Rp_pos (u := u) hc hy.ne' hn t
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs, abs_of_nonneg (Real.rpow_nonneg hR.le _)]
  have hd := abs_dRp_le (u := u) hc hy hn t
  have e : Rp c n u y t * Rp c n u y t ^ (-s - 1) = Rp c n u y t ^ (-s) := by
    have := Real.rpow_add hR 1 (-s - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (-s - 1) = -s by ring] at this
    rw [this]
  calc |dRp c n u y t| * s * Rp c n u y t ^ (-s - 1)
      ≤ Rp c n u y t / (|c| * y) * s * Rp c n u y t ^ (-s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hs) (Real.rpow_nonneg hR.le _)
    _ = s / (|c| * y) * (Rp c n u y t * Rp c n u y t ^ (-s - 1)) := by ring
    _ = s / (|c| * y) * Rp c n u y t ^ (-s) := by rw [e]

/-- **`|∂_t VN| ≤ (4 + s)/(|c| y) |VN|`.** -/
lemma norm_dVN_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    ‖dVN s c n u y t‖ ≤ (4 + s) / (|c| * y) * ‖VN s c n u y t‖ := by
  have hR := Rp_pos (u := u) hc hy.ne' hn t
  have hA : 0 ≤ y ^ 2 * n ^ s := mul_nonneg (sq_nonneg y) (Real.rpow_nonneg hn s)
  have hg0 : 0 ≤ Rp c n u y t ^ (-s) := Real.rpow_nonneg hR.le _
  have h1 := norm_dinvQ_le (u := u) hc hy hn t
  have h2 := abs_dRpow_le (u := u) hs hc hy hn t
  have hq0 : 0 ≤ ‖(Qp c n u y t ^ 2)⁻¹‖ := norm_nonneg _
  have hN : ‖dVN s c n u y t‖ ≤ y ^ 2 * n ^ s * (‖dinvQ c n u y t‖ * Rp c n u y t ^ (-s) +
      ‖(Qp c n u y t ^ 2)⁻¹‖ * |dRp c n u y t * (-s) * Rp c n u y t ^ (-s - 1)|) := by
    rw [dVN, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) hA
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hg0,
      Real.norm_eq_abs]
  rw [norm_VN_eq s hn]
  calc ‖dVN s c n u y t‖ ≤ _ := hN
    _ ≤ y ^ 2 * n ^ s * (4 / (|c| * y) * ‖(Qp c n u y t ^ 2)⁻¹‖ * Rp c n u y t ^ (-s) +
        ‖(Qp c n u y t ^ 2)⁻¹‖ * (s / (|c| * y) * Rp c n u y t ^ (-s))) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hA
      · exact mul_le_mul_of_nonneg_right h1 hg0
      · exact mul_le_mul_of_nonneg_left h2 hq0
    _ = (4 + s) / (|c| * y) *
        (y ^ 2 * n ^ s * (‖(Qp c n u y t ^ 2)⁻¹‖ * Rp c n u y t ^ (-s))) := by ring

lemma integrable_VN {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable (VN s c n u y) :=
  ((integrable_VS (u := u) hs hc hy hn).const_mul (n ^ s)).mono'
    (continuous_VN s hc hy.ne' hn).aestronglyMeasurable
    (Eventually.of_forall fun t => (norm_VN s hc hy.ne' hn t).le)

lemma aestronglyMeasurable_dVN (s : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) (hn : 0 ≤ n) :
    AEStronglyMeasurable (dVN s c n u y) volume := by
  have h : deriv (VN s c n u y) = dVN s c n u y :=
    funext fun t => (hasDerivAt_VN s hc hy hn t).deriv
  rw [← h]
  exact (measurable_deriv _).aestronglyMeasurable

lemma norm_dVN_le' {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) (t : ℝ) :
    ‖dVN s c n u y t‖ ≤ (4 + s) / (|c| * y) * (n ^ s * VS s c n u y t) := by
  have h := norm_dVN_le (u := u) hs hc hy hn t
  rwa [norm_VN s hc hy.ne' hn t] at h

lemma integrable_dVN {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Integrable (dVN s c n u y) :=
  (((integrable_VS (u := u) hs hc hy hn).const_mul (n ^ s)).const_mul ((4 + s) / (|c| * y))).mono'
    (aestronglyMeasurable_dVN s hc hy.ne' hn)
    (Eventually.of_forall fun t => norm_dVN_le' hs hc hy hn t)

lemma summable_VN {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    Summable fun t : ℤ => VN s c n u y t :=
  summable_int_of_deriv (hasDerivAt_VN s hc hy.ne' hn) (integrable_dVN hs hc hy hn)
    (integrable_VN hs hc hy hn)

lemma integral_norm_dVN_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    ∫ t, ‖dVN s c n u y t‖ ≤ (4 + s) / (|c| * y) * (n ^ s * ∫ t, VS s c n u y t) := by
  rw [← integral_const_mul, ← integral_const_mul]
  exact integral_mono (integrable_dVN hs hc hy hn).norm
    (((integrable_VS hs hc hy hn).const_mul _).const_mul _) fun t => norm_dVN_le' hs hc hy hn t

lemma norm_integral_VN_le {s : ℝ} (hs : 0 ≤ s) (hc : c ≠ 0) (hy : 0 < y) (hn : 0 ≤ n) :
    ‖∫ t, VN s c n u y t‖ ≤ n ^ s * ∫ t, VS s c n u y t := by
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact integral_congr_ae (Eventually.of_forall fun t => norm_VN s hc hy.ne' hn t)

end RamanujanPetersson.EllW2


