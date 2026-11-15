-- Prove2me | Definitions.Def_RPLib_S3_KernelSDF
-- name    : RPLib_S3_KernelSDF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:42:42.864734+00:00
-- url     : https://prove2.me/theorems/c37779b1-45e6-49d2-81eb-7191a349c384
-- title:
--   The Eichler-Selberg trace formula in weight two: the `s = 0` kernel `K0` and the uniform `y^(-1/2)` bound
-- statement:
--   The `s = 0` kernel `K0` and the uniform `y^(-1/2)` bound.
--
--   * `K0 M z w = KG0 M 0 z w + Σ_{Tset} Eterm 0 + Σ_{c'} MF M 0 z w c'`.
--   * `tendsto_KG`: `KG M s z w → K0 M z w` as `s → 0+` (`M ≥ 3`).
--   * `norm_KG_le` (`0 < s ≤ 1/2`) and `norm_K0_le`: `‖·‖ ≤ CKG M y0 (Im w) * (Im z)^(-1/2)` for `Im z ≥ y0`,
--     uniformly in `Re z` and `s`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDE2

/-!
# S3-ES-Wt2, part KS_D (F): the `s = 0` kernel `K0` and the uniform `y^(-1/2)` bound

* `K0 M z w = KG0 M 0 z w + Σ_{Tset} Eterm 0 + Σ_{c'} MF M 0 z w c'`.
* `tendsto_KG`: `KG M s z w → K0 M z w` as `s → 0+` (`M ≥ 3`).
* `norm_KG_le` (`0 < s ≤ 1/2`) and `norm_K0_le`: `‖·‖ ≤ CKG M y0 (Im w) * (Im z)^(-1/2)` for `Im z ≥ y0`,
  uniformly in `Re z` and `s`.
-/

open Complex Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

/-- The `s = 0` kernel (the limit of `KG M s` as `s → 0+`). -/
def K0 (M : ℕ) [NeZero M] (z w : ℂ) : ℂ :=
  KG0 M 0 z w + ∑' p : Tset M, Eterm 0 z w p.1 + ∑' c' : ℕ, MF M 0 z w c'

/-- **(i)** `KG M s → K0` as `s → 0+`. -/
theorem tendsto_KG {M : ℕ} [NeZero M] (hM : 3 ≤ M) {z w : ℂ} (hy : 0 < z.im) (hv : 0 < w.im) :
    Tendsto (fun s => KG M s z w) (𝓝[>] 0) (𝓝 (K0 M z w)) := by
  have h := ((tendsto_KG0 M hy hv).add (tendsto_tsum_Eterm M hy hv)).add
    (tendsto_tsum_MF (M := M) hy hv).2
  unfold K0
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
  rw [(KG_split hM hs.1 hs.2.le hy hv).2, (tsum_Mterm_eq_MF hM hs.1 hs.2.le hy hv).2]

/-! ### Elementary bounds -/

lemma rho_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : rho b ≤ rho a := by
  have h := inv_anti₀ (pow_pos ha 2) (pow_le_pow_left₀ ha.le hab 2)
  unfold rho; linarith

lemma Bnd_le {y0 a Y : ℝ} (hy0 : 0 < y0) (hY : y0 ≤ Y) (ha : 0 < a) (haY : a ≤ Y) :
    Bnd Y ≤ π * rho y0 ^ 2 / a := by
  have h1 : 0 ≤ rho Y := le_trans zero_le_one (one_le_rho Y)
  have h2 : rho Y ^ 2 ≤ rho y0 ^ 2 := pow_le_pow_left₀ h1 (rho_anti hy0 hY) 2
  have h3 : 0 ≤ π * rho y0 ^ 2 := by positivity
  unfold Bnd
  calc π * rho Y ^ 2 / Y ≤ π * rho y0 ^ 2 / Y :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 Real.pi_pos.le) (ha.le.trans haY)
    _ ≤ π * rho y0 ^ 2 / a := div_le_div_of_nonneg_left h3 ha haY

lemma rpow_le_T {t s : ℝ} (ht : 0 < t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    t ^ s ≤ 1 + t ^ (1 / 2 : ℝ) := by
  have h0 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  rcases le_or_gt t 1 with h | h
  · linarith [Real.rpow_le_one ht.le h hs0]
  · linarith [Real.rpow_le_rpow_of_exponent_le h.le hs1]

lemma T_div_le {y0 y v : ℝ} (hy0 : 0 < y0) (hy : y0 ≤ y) (hv : 0 < v) :
    (1 + (y * v) ^ (1 / 2 : ℝ)) / y ≤
      (y0 ^ (-(1 / 2) : ℝ) + v ^ (1 / 2 : ℝ)) * y ^ (-(1 / 2) : ℝ) := by
  have hy' : 0 < y := hy0.trans_le hy
  have ha : 0 < y ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hy' _
  have haa : y ^ (-(1 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ) = y⁻¹ := by
    rw [← Real.rpow_add hy', show (-(1 / 2) : ℝ) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
  have haay : y ^ (-(1 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ) * y = 1 := by
    rw [haa, inv_mul_cancel₀ hy'.ne']
  have hya : y ^ (1 / 2 : ℝ) = y * y ^ (-(1 / 2) : ℝ) := by
    conv_lhs => rw [show (1 / 2 : ℝ) = 1 + -(1 / 2) by norm_num]
    rw [Real.rpow_add hy', Real.rpow_one]
  have hyv : (y * v) ^ (1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) * v ^ (1 / 2 : ℝ) := Real.mul_rpow hy'.le hv.le
  have hb : y ^ (-(1 / 2) : ℝ) ≤ y0 ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hy0 hy (by norm_num)
  have h1 := mul_le_mul_of_nonneg_right hb (mul_nonneg ha.le hy'.le)
  have hv0 : 0 ≤ v ^ (1 / 2 : ℝ) := Real.rpow_nonneg hv.le _
  rw [hyv, hya, div_le_iff₀ hy']
  nlinarith [h1, haay]

lemma sq_rpow_quarter {y : ℝ} (hy : 0 ≤ y) : (y ^ 2) ^ (-(1 / 4) : ℝ) = y ^ (-(1 / 2) : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

def SGs : ℝ := ∑' n : ℤ, (1 + (n : ℝ) ^ 2)⁻¹

lemma SGs_nonneg : 0 ≤ SGs := tsum_nonneg fun n => by positivity

/-! ### The three pieces -/

theorem norm_KG0_le {M : ℕ} [NeZero M] {s y0 T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy0 : 0 < y0)
    {z w : ℂ} (hy : y0 ≤ z.im) (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) :
    ‖KG0 M s z w‖ ≤ T / z.im * (π * rho (y0 / M) ^ 2 * M * SGs / (M : ℝ) ^ 2) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hM1 : (1 : ℝ) ≤ (M : ℝ) ^ 2 :=
    one_le_pow₀ (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  have hyz : 0 < z.im := hy0.trans_le hy
  have hyv : 0 < z.im * w.im := mul_pos hyz hv
  have hζ : ((z + w) / (M : ℂ)).im = (z.im + w.im) / M := by
    rw [Complex.div_natCast_im, Complex.add_im]
  have hζp : 0 < ((z + w) / (M : ℂ)).im := by rw [hζ]; exact div_pos (add_pos hyz hv) hMr
  have hB : Bnd ((z + w) / (M : ℂ)).im ≤ π * rho (y0 / M) ^ 2 / (z.im / M) := by
    rw [hζ]
    exact Bnd_le (div_pos hy0 hMr) (div_le_div_of_nonneg_right (by linarith) hMr.le)
      (div_pos hyz hMr) (div_le_div_of_nonneg_right (by linarith) hMr.le)
  have hG : ‖Gs s ((z + w) / M)‖ ≤ π * rho (y0 / M) ^ 2 / (z.im / M) * SGs :=
    (norm_Gs_le hs0 hs1 hζp).trans (mul_le_mul_of_nonneg_right hB SGs_nonneg)
  have hq : 0 ≤ z.im * w.im / (M : ℝ) ^ 2 := div_nonneg hyv.le (by positivity)
  have hpow : (z.im * w.im / (M : ℝ) ^ 2) ^ s ≤ T :=
    (Real.rpow_le_rpow hq (div_le_self hyv.le hM1) hs0).trans hT
  have hT0 : 0 ≤ T := (Real.rpow_nonneg hyv.le s).trans hT
  unfold KG0
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq s), norm_inv,
    norm_pow, Complex.norm_natCast]
  calc (z.im * w.im / (M : ℝ) ^ 2) ^ s * ((M : ℝ) ^ 2)⁻¹ * ‖Gs s ((z + w) / M)‖
      ≤ T * ((M : ℝ) ^ 2)⁻¹ * (π * rho (y0 / M) ^ 2 / (z.im / M) * SGs) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hpow (by positivity)) hG (norm_nonneg _)
          (mul_nonneg hT0 (by positivity))
    _ = T / z.im * (π * rho (y0 / M) ^ 2 * M * SGs / (M : ℝ) ^ 2) := by rw [div_div_eq_mul_div]; ring

theorem norm_tsum_Eterm_le_half (M : ℕ) {s y0 : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hy0 : 0 < y0)
    {z w : ℂ} (hy : y0 ≤ z.im) (hv : 0 < w.im) :
    ‖∑' p : Tset M, Eterm s z w p.1‖ ≤
      Kerr (y0 * w.im) * (Kv w.im * (w.im ^ 2) ^ (-(3 / 4 : ℝ)) *
        ((min (1 / 4) (y0 ^ 2)) ^ (-(5 / 4 : ℝ)) * S2)) * z.im ^ (-(1 / 2) : ℝ) := by
  have hyz : 0 < z.im := hy0.trans_le hy
  refine (norm_tsum_Eterm_le M hs0 hs1 hy0 hy hv (mul_pos hy0 hv)
    (mul_le_mul_of_nonneg_right hy hv.le)).trans (le_of_eq ?_)
  unfold Kz
  rw [sq_rpow_quarter hyz.le]
  ring

theorem norm_tsum_MF_le_half {M : ℕ} [NeZero M] {s y0 T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hy0 : 0 < y0) {z w : ℂ} (hy : y0 ≤ z.im) (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) :
    ‖∑' c' : ℕ, MF M s z w c'‖ ≤
      T / z.im * (π * rho (y0 / M) ^ 2 * M * Bnd (w.im / M) * (∑' p, majS M p + 4)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hyz : 0 < z.im := hy0.trans_le hy
  have hT0 : 0 ≤ T := (Real.rpow_nonneg (mul_pos hyz hv).le s).trans hT
  have hB : Bnd (z.im / M) ≤ π * rho (y0 / M) ^ 2 / (z.im / M) :=
    Bnd_le (div_pos hy0 hMr) (div_le_div_of_nonneg_right hy hMr.le) (div_pos hyz hMr) le_rfl
  have hBv : 0 ≤ Bnd (w.im / M) := (Bnd_pos (div_pos hv hMr)).le
  have hS : 0 ≤ ∑' p, majS M p := tsum_nonneg (majS_nonneg M)
  have hs' : 8 * s ^ 2 + 4 * s ≤ 4 := by nlinarith
  have hP : 0 ≤ π * rho (y0 / M) ^ 2 / (z.im / M) := div_nonneg (by positivity) (div_pos hyz hMr).le
  refine (norm_tsum_MF_le hs0 (by linarith) hyz hv hT).trans ?_
  calc T * (Bnd (z.im / M) * Bnd (w.im / M)) * (∑' p, majS M p + (8 * s ^ 2 + 4 * s))
      ≤ T * (π * rho (y0 / M) ^ 2 / (z.im / M) * Bnd (w.im / M)) * (∑' p, majS M p + 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hBv) hT0)
          (by linarith) (add_nonneg hS (by positivity)) (mul_nonneg hT0 (mul_nonneg hP hBv))
    _ = T / z.im * (π * rho (y0 / M) ^ 2 * M * Bnd (w.im / M) * (∑' p, majS M p + 4)) := by rw [div_div_eq_mul_div]; ring

/-! ### **(ii)** The uniform bound -/

/-- The constant of the uniform bound (`Im z ≥ y0`, `v = Im w`). -/
def CKG (M : ℕ) [NeZero M] (y0 v : ℝ) : ℝ :=
  (y0 ^ (-(1 / 2) : ℝ) + v ^ (1 / 2 : ℝ)) *
      (π * rho (y0 / M) ^ 2 * M * SGs / (M : ℝ) ^ 2 +
        π * rho (y0 / M) ^ 2 * M * Bnd (v / M) * (∑' p, majS M p + 4)) +
    Kerr (y0 * v) * (Kv v * (v ^ 2) ^ (-(3 / 4 : ℝ)) * ((min (1 / 4) (y0 ^ 2)) ^ (-(5 / 4 : ℝ)) * S2))

theorem norm_split_le {M : ℕ} [NeZero M] {s y0 : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hy0 : 0 < y0)
    {z w : ℂ} (hy : y0 ≤ z.im) (hv : 0 < w.im) :
    ‖KG0 M s z w + ∑' p : Tset M, Eterm s z w p.1 + ∑' c' : ℕ, MF M s z w c'‖ ≤
      CKG M y0 w.im * z.im ^ (-(1 / 2) : ℝ) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hyz : 0 < z.im := hy0.trans_le hy
  have hT := rpow_le_T (mul_pos hyz hv) hs0 hs1
  have h1 := norm_KG0_le (M := M) hs0 (by linarith) hy0 hy hv hT
  have h2 := norm_tsum_Eterm_le_half M hs0 (by linarith) hy0 hy hv
  have h3 := norm_tsum_MF_le_half (M := M) hs0 hs1 hy0 hy hv hT
  have h4 := T_div_le hy0 hy hv
  have hA : 0 ≤ π * rho (y0 / M) ^ 2 * M * SGs / (M : ℝ) ^ 2 :=
    div_nonneg (mul_nonneg (by positivity) SGs_nonneg) (by positivity)
  have hBv : 0 ≤ Bnd (w.im / M) := (Bnd_pos (div_pos hv hMr)).le
  have hS : 0 ≤ ∑' p, majS M p := tsum_nonneg (majS_nonneg M)
  have hB : 0 ≤ π * rho (y0 / M) ^ 2 * M * Bnd (w.im / M) * (∑' p, majS M p + 4) :=
    mul_nonneg (mul_nonneg (by positivity) hBv) (add_nonneg hS (by norm_num))
  calc ‖KG0 M s z w + ∑' p : Tset M, Eterm s z w p.1 + ∑' c' : ℕ, MF M s z w c'‖
      ≤ ‖KG0 M s z w‖ + ‖∑' p : Tset M, Eterm s z w p.1‖ + ‖∑' c' : ℕ, MF M s z w c'‖ :=
        norm_add₃_le
    _ ≤ (y0 ^ (-(1 / 2) : ℝ) + w.im ^ (1 / 2 : ℝ)) * z.im ^ (-(1 / 2) : ℝ) *
            (π * rho (y0 / M) ^ 2 * M * SGs / (M : ℝ) ^ 2) +
          Kerr (y0 * w.im) * (Kv w.im * (w.im ^ 2) ^ (-(3 / 4 : ℝ)) *
            ((min (1 / 4) (y0 ^ 2)) ^ (-(5 / 4 : ℝ)) * S2)) * z.im ^ (-(1 / 2) : ℝ) +
          (y0 ^ (-(1 / 2) : ℝ) + w.im ^ (1 / 2 : ℝ)) * z.im ^ (-(1 / 2) : ℝ) *
            (π * rho (y0 / M) ^ 2 * M * Bnd (w.im / M) * (∑' p, majS M p + 4)) :=
        add_le_add (add_le_add (h1.trans (mul_le_mul_of_nonneg_right h4 hA)) h2)
          (h3.trans (mul_le_mul_of_nonneg_right h4 hB))
    _ = CKG M y0 w.im * z.im ^ (-(1 / 2) : ℝ) := by unfold CKG; ring

/-- **(ii)** for `KG` (`0 < s ≤ 1/2`). -/
theorem norm_KG_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) {s y0 : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2)
    (hy0 : 0 < y0) {z w : ℂ} (hy : y0 ≤ z.im) (hv : 0 < w.im) :
    ‖KG M s z w‖ ≤ CKG M y0 w.im * z.im ^ (-(1 / 2) : ℝ) := by
  have hyz : 0 < z.im := hy0.trans_le hy
  rw [(KG_split hM hs (by linarith) hyz hv).2, (tsum_Mterm_eq_MF hM hs (by linarith) hyz hv).2]
  exact norm_split_le hs.le hs1 hy0 hy hv

/-- **(ii)** for `K0`. -/
theorem norm_K0_le {M : ℕ} [NeZero M] {y0 : ℝ} (hy0 : 0 < y0) {z w : ℂ} (hy : y0 ≤ z.im)
    (hv : 0 < w.im) : ‖K0 M z w‖ ≤ CKG M y0 w.im * z.im ^ (-(1 / 2) : ℝ) :=
  norm_split_le le_rfl (by norm_num) hy0 hy hv

end RamanujanPetersson.KernelSD


