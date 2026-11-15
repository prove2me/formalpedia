-- Prove2me | Definitions.Def_RPLib_S3_KernelSDD
-- name    : RPLib_S3_KernelSDD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:35:28.179936+00:00
-- url     : https://prove2.me/theorems/4fdb8c6c-24d2-4d7c-a144-b8c30c59ebc8
-- title:
--   The Eichler-Selberg trace formula in weight two: Fourier form of the MAIN blocks and the Kloosterman majorant
-- statement:
--   Fourier form of the MAIN blocks and the Kloosterman majorant.
--
--   * `KK M c' m r = klR M L 1 r m + klR M L (-1) r m` (`L = Lm M c'`); `MFm` the `(m, r)` mode; `hasSum_MF`.
--   * `majF` on `(ℤ × ℤ) × ℕ`, `summable_majF` (Kloosterman bound via `summable_klR_div`).
--   * `norm_MFm_le` (modes `≠ 0`), `norm_MFm_zero_le` (`(0,0)` mode), `sum_rpow_le` (`Σ (c'+1)^(-1-ε) ≤ 1 + 1/ε`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDC
import Definitions.Def_RPLib_S3_KloostermanC

/-!
# S3-ES-Wt2, part KS_D (D): Fourier form of the MAIN blocks and the Kloosterman majorant

* `KK M c' m r = klR M L 1 r m + klR M L (-1) r m` (`L = Lm M c'`); `MFm` the `(m, r)` mode; `hasSum_MF`.
* `majF` on `(ℤ × ℤ) × ℕ`, `summable_majF` (Kloosterman bound via `summable_klR_div`).
* `norm_MFm_le` (modes `≠ 0`), `norm_MFm_zero_le` (`(0,0)` mode), `sum_rpow_le` (`Σ (c'+1)^(-1-ε) ≤ 1 + 1/ε`).
-/

open Complex Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

def KK (M : ℕ) [NeZero M] (c' : ℕ) (m r : ℤ) : ℂ :=
  KL.klR M (Lm M c') 1 (r : ZMod (Lm M c')) (m : ZMod (Lm M c')) +
    KL.klR M (Lm M c') (-1) (r : ZMod (Lm M c')) (m : ZMod (Lm M c'))

def MFm (M : ℕ) [NeZero M] (s : ℝ) (z w : ℂ) (c' : ℕ) (mr : ℤ × ℤ) : ℂ :=
  ((WtR M s (z.im * w.im) c' : ℝ) : ℂ) * (gS s (z.im / M) (mr.1 : ℝ) * gS s (w.im / M) (mr.2 : ℝ) *
    (fourier mr.1 ((z.re / M : ℝ) : UnitAddCircle) * fourier mr.2 ((w.re / M : ℝ) : UnitAddCircle)) *
      KK M c' mr.1 mr.2)

lemma fourier_zeta (M c' : ℕ) [NeZero M] (z : ℂ) (n : ℕ) (m : ℤ) :
    fourier m (((zeta M c' z n).re : ℝ) : UnitAddCircle) =
      fourier m ((z.re / M : ℝ) : UnitAddCircle) *
        Complex.exp (2 * π * I * ((m * (n : ℤ) : ℤ) : ℂ) / ((Lm M c' : ℕ) : ℂ)) := by
  have hM' : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hc1 : ((c' : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero c'
  rw [fourier_coe_apply, fourier_coe_apply, re_zeta, ← Complex.exp_add]
  congr 1
  simp only [Lm]
  push_cast
  field_simp

lemma stdAddChar_units (L : ℕ) [NeZero L] (x : (ZMod L)ˣ) (m r : ℤ) :
    (ZMod.stdAddChar ((r : ZMod L) * (x : ZMod L) + (m : ZMod L) * (x : ZMod L)⁻¹) : ℂ) =
      Complex.exp (2 * π * I * ((r * (((x : ZMod L).val : ℕ) : ℤ) +
        m * ((((x⁻¹ : (ZMod L)ˣ) : ZMod L).val : ℕ) : ℤ) : ℤ) : ℂ) / (L : ℂ)) := by
  rw [← ZMod.stdAddChar_coe, ZMod.inv_coe_unit]
  congr 1
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

lemma hasSum_Gs_prod {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ζ ξ : ℂ} (hζ : 0 < ζ.im) (hξ : 0 < ξ.im) :
    HasSum (fun mr : ℤ × ℤ => (gS s ζ.im mr.1 * fourier mr.1 (ζ.re : UnitAddCircle)) *
      (gS s ξ.im mr.2 * fourier mr.2 (ξ.re : UnitAddCircle))) (Gs s ζ * Gs s ξ) := by
  have h1 : Summable (fun n : ℤ => ‖gS s ζ.im n * fourier n (ζ.re : UnitAddCircle)‖) :=
    (summable_norm_gS hs0 hs1 hζ).congr fun n => by rw [norm_mul, norm_fourier_coe, mul_one]
  have h2 : Summable (fun n : ℤ => ‖gS s ξ.im n * fourier n (ξ.re : UnitAddCircle)‖) :=
    (summable_norm_gS hs0 hs1 hξ).congr fun n => by rw [norm_mul, norm_fourier_coe, mul_one]
  have h := (summable_mul_of_summable_norm h1 h2).hasSum
  rwa [← tsum_mul_tsum_of_summable_norm h1 h2, (hasSum_Gs hs0 hs1 hζ).tsum_eq,
    (hasSum_Gs hs0 hs1 hξ).tsum_eq] at h

lemma sum_chiU_eq (M c' : ℕ) [NeZero M] (m r : ℤ) :
    ∑ x : (ZMod (Lm M c'))ˣ, chiU M c' x * (ZMod.stdAddChar ((r : ZMod (Lm M c')) * (x : ZMod (Lm M c')) +
      (m : ZMod (Lm M c')) * (x : ZMod (Lm M c'))⁻¹) : ℂ) = KK M c' m r := by
  simp only [KK, KL.klR, chiU, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]

/-- **Fourier form of the `c'`-block.** -/
theorem hasSum_MF {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (c' : ℕ) : HasSum (MFm M s z w c') (MF M s z w c') := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hx : ∀ x : (ZMod (Lm M c'))ˣ, HasSum (fun mr : ℤ × ℤ =>
      chiU M c' x * ((gS s (z.im / M) (mr.1 : ℝ) * gS s (w.im / M) (mr.2 : ℝ) *
        (fourier mr.1 ((z.re / M : ℝ) : UnitAddCircle) * fourier mr.2 ((w.re / M : ℝ) : UnitAddCircle))) *
        (ZMod.stdAddChar ((mr.2 : ZMod (Lm M c')) * (x : ZMod (Lm M c')) +
          (mr.1 : ZMod (Lm M c')) * (x : ZMod (Lm M c'))⁻¹) : ℂ)))
      (chiU M c' x * (Gs s (zeta M c' z ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val) *
          Gs s (zeta M c' w ((x : ZMod (Lm M c')).val)))) := by
    intro x
    have hζ : 0 < (zeta M c' z ((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val).im := by
      rw [im_zeta]; positivity
    have hξ : 0 < (zeta M c' w ((x : ZMod (Lm M c')).val)).im := by rw [im_zeta]; positivity
    refine ((hasSum_Gs_prod hs0 hs1 hζ hξ).mul_left (chiU M c' x)).congr_fun fun mr => ?_
    rw [im_zeta, im_zeta, fourier_zeta, fourier_zeta, stdAddChar_units]
    have e : Complex.exp (2 * π * I * ((mr.2 * (((x : ZMod (Lm M c')).val : ℕ) : ℤ) +
        mr.1 * ((((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val : ℕ) : ℤ) : ℤ) : ℂ) /
          ((Lm M c' : ℕ) : ℂ)) =
        Complex.exp (2 * π * I * ((mr.1 * ((((x⁻¹ : (ZMod (Lm M c'))ˣ) : ZMod (Lm M c')).val : ℕ) : ℤ) : ℤ) : ℂ) /
          ((Lm M c' : ℕ) : ℂ)) *
        Complex.exp (2 * π * I * ((mr.2 * (((x : ZMod (Lm M c')).val : ℕ) : ℤ) : ℤ) : ℂ) /
          ((Lm M c' : ℕ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  unfold MF
  refine ((hasSum_sum (s := Finset.univ) fun x _ => hx x).mul_left
    ((WtR M s (z.im * w.im) c' : ℝ) : ℂ)).congr_fun fun mr => ?_
  rw [MFm, ← sum_chiU_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ### Bounds -/

lemma WtR_nonneg (M : ℕ) {s t : ℝ} (ht : 0 ≤ t) (c' : ℕ) : 0 ≤ WtR M s t c' := by
  unfold WtR; exact div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)

lemma Lm_sq_le (M : ℕ) [NeZero M] (c' : ℕ) :
    ((Lm M c' : ℕ) : ℝ) ^ 2 ≤ ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have h24 : (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 4 := pow_le_pow_right₀ hM1 (by norm_num)
  calc ((Lm M c' : ℕ) : ℝ) ^ 2 = ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 2 := by simp only [Lm]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h24 (sq_nonneg _)

lemma one_le_X (M : ℕ) [NeZero M] (c' : ℕ) : ((c' : ℝ) + 1) ^ 2 ≤ ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hc : (1 : ℝ) ≤ (c' : ℝ) + 1 := by linarith [(Nat.cast_nonneg c' : (0 : ℝ) ≤ c')]
  have h1 : (c' + 1 : ℝ) ≤ (M : ℝ) * (c' + 1) := le_mul_of_one_le_left (by linarith) hM1
  have h2 : ((c' : ℝ) + 1) ^ 2 ≤ ((M : ℝ) * (c' + 1)) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h4 : (1 : ℝ) ≤ (M : ℝ) ^ 4 := one_le_pow₀ hM1
  nlinarith [sq_nonneg ((M : ℝ) * (c' + 1))]

lemma WtR_le (M : ℕ) [NeZero M] {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 < t) (c' : ℕ) :
    WtR M s t c' ≤ max 1 t / ((Lm M c' : ℕ) : ℝ) ^ 2 := by
  have hX1 : 1 ≤ ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4 :=
    le_trans (one_le_pow₀ (by linarith [(Nat.cast_nonneg c' : (0 : ℝ) ≤ c')])) (one_le_X M c')
  have hL0 : (0 : ℝ) < ((Lm M c' : ℕ) : ℝ) ^ 2 := by have := NeZero.pos (Lm M c'); positivity
  have hq : (t / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4)) ^ s ≤ max 1 t :=
    (KernelSD.rpow_le_max_one (div_pos ht (by linarith)) hs0 hs1).trans
      (max_le_max le_rfl (div_le_self ht.le hX1))
  unfold WtR
  calc _ ≤ max 1 t / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4) :=
        div_le_div_of_nonneg_right hq (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hL0 (Lm_sq_le M c')

def majF (M : ℕ) [NeZero M] (p : (ℤ × ℤ) × ℕ) : ℝ :=
  if p.1 = 0 then 0 else
    (1 + (p.1.1 : ℝ) ^ 2)⁻¹ * (1 + (p.1.2 : ℝ) ^ 2)⁻¹ * (‖KK M p.2 p.1.1 p.1.2‖ / ((Lm M p.2 : ℕ) : ℝ) ^ 2)

lemma majF_nonneg (M : ℕ) [NeZero M] (p : (ℤ × ℤ) × ℕ) : 0 ≤ majF M p := by
  unfold majF; split_ifs <;> positivity

lemma Bnd_pos {y : ℝ} (hy : 0 < y) : 0 < Bnd y := by
  unfold Bnd; have := one_le_rho y; positivity

/-- Modes `(m, r) ≠ 0`. -/
theorem norm_MFm_le {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (c' : ℕ) (mr : ℤ × ℤ) (hmr : mr ≠ 0) :
    ‖MFm M s z w c' mr‖ ≤ max 1 (z.im * w.im) * (Bnd (z.im / M) * Bnd (w.im / M)) * majF M (mr, c') := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hy' : 0 < z.im / M := div_pos hy hMr
  have hv' : 0 < w.im / M := div_pos hv hMr
  have hB1 := Bnd_pos hy'
  have hB2 := Bnd_pos hv'
  have hW := WtR_le M hs0 hs1 (mul_pos hy hv) c'
  have hW0 := WtR_nonneg M (mul_pos hy hv).le (s := s) c'
  have g1 := norm_gS_le hs0 hs1 hy' (mr.1 : ℝ)
  have g2 := norm_gS_le hs0 hs1 hv' (mr.2 : ℝ)
  have hL0 : (0 : ℝ) < ((Lm M c' : ℕ) : ℝ) ^ 2 := by have := NeZero.pos (Lm M c'); positivity
  have hm1 : (0 : ℝ) < 1 + (mr.1 : ℝ) ^ 2 := by positivity
  have hm2 : (0 : ℝ) < 1 + (mr.2 : ℝ) ^ 2 := by positivity
  rw [majF, if_neg hmr, MFm, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_coe,
    norm_fourier_coe, Complex.norm_real, Real.norm_of_nonneg hW0]
  calc WtR M s (z.im * w.im) c' * (‖gS s (z.im / M) (mr.1 : ℝ)‖ * ‖gS s (w.im / M) (mr.2 : ℝ)‖ * (1 * 1) *
        ‖KK M c' mr.1 mr.2‖)
      ≤ max 1 (z.im * w.im) / ((Lm M c' : ℕ) : ℝ) ^ 2 * (Bnd (z.im / M) / (1 + (mr.1 : ℝ) ^ 2) *
          (Bnd (w.im / M) / (1 + (mr.2 : ℝ) ^ 2)) * (1 * 1) * ‖KK M c' mr.1 mr.2‖) := by gcongr
    _ = _ := by field_simp

/-- The `(0,0)` mode: `O(s²) (c'+1)^(-1-2s)`. -/
theorem norm_MFm_zero_le {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (c' : ℕ) :
    ‖MFm M s z w c' 0‖ ≤ 8 * s ^ 2 * (max 1 (z.im * w.im) * (Bnd (z.im / M) * Bnd (w.im / M))) *
      ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hy' : 0 < z.im / M := div_pos hy hMr
  have hv' : 0 < w.im / M := div_pos hv hMr
  have hB1 := Bnd_pos hy'
  have hB2 := Bnd_pos hv'
  have ht : 0 < z.im * w.im := mul_pos hy hv
  have hC : (0 : ℝ) < (c' : ℝ) + 1 := by positivity
  set X : ℝ := ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4 with hX
  have hX0 : 0 < X := by positivity
  have hCX := one_le_X M c'
  have hK : ‖KK M c' 0 0‖ ≤ 2 * ((Lm M c' : ℕ) : ℝ) := by
    unfold KK
    refine (norm_add_le _ _).trans ?_
    linarith [KL.norm_klR_le M (Lm M c') 1 ((0 : ℤ) : ZMod (Lm M c')) ((0 : ℤ) : ZMod (Lm M c')),
      KL.norm_klR_le M (Lm M c') (-1) ((0 : ℤ) : ZMod (Lm M c')) ((0 : ℤ) : ZMod (Lm M c'))]
  have g1 := norm_gS_zero_le hs0 hs1 hy'
  have g2 := norm_gS_zero_le hs0 hs1 hv'
  -- the weight
  have hq : (z.im * w.im / X) ^ s ≤ max 1 (z.im * w.im) * ((c' : ℝ) + 1) ^ (-(2 * s)) := by
    rw [Real.div_rpow ht.le hX0.le, div_eq_mul_inv]
    refine mul_le_mul (KernelSD.rpow_le_max_one ht hs0 hs1) ?_ (by positivity) (by positivity)
    rw [Real.rpow_neg hC.le]
    refine inv_anti₀ (by positivity) ?_
    rw [Real.rpow_mul hC.le, Real.rpow_two]
    exact Real.rpow_le_rpow (by positivity) hCX hs0
  have hLX : 2 * ((Lm M c' : ℕ) : ℝ) / X ≤ 2 * ((c' : ℝ) + 1) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, div_le_iff₀ hX0]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
    have h4 : (1 : ℝ) ≤ (M : ℝ) ^ 4 := one_le_pow₀ hM1
    rw [hX]; simp only [Lm]; push_cast
    field_simp
    nlinarith [sq_nonneg ((M : ℝ)), mul_pos hMr hC, sq_nonneg ((M : ℝ) * (c' + 1))]
  have hW : WtR M s (z.im * w.im) c' * (2 * ((Lm M c' : ℕ) : ℝ)) ≤
      2 * max 1 (z.im * w.im) * ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) := by
    have e : ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) = ((c' : ℝ) + 1) ^ (-(2 * s)) * ((c' : ℝ) + 1) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hC]; ring_nf
    rw [e]
    calc WtR M s (z.im * w.im) c' * (2 * ((Lm M c' : ℕ) : ℝ))
        = (z.im * w.im / X) ^ s * (2 * ((Lm M c' : ℕ) : ℝ) / X) := by unfold WtR; rw [← hX]; ring
      _ ≤ (max 1 (z.im * w.im) * ((c' : ℝ) + 1) ^ (-(2 * s))) * (2 * ((c' : ℝ) + 1) ^ (-(1 : ℝ))) :=
          mul_le_mul hq hLX (by positivity) (by positivity)
      _ = _ := by ring
  have hW0 := WtR_nonneg M ht.le (s := s) c'
  simp only [MFm, Prod.fst_zero, Prod.snd_zero, Int.cast_zero]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_coe, norm_fourier_coe, Complex.norm_real,
    Real.norm_of_nonneg hW0]
  calc WtR M s (z.im * w.im) c' * (‖gS s (z.im / M) 0‖ * ‖gS s (w.im / M) 0‖ * (1 * 1) * ‖KK M c' 0 0‖)
      ≤ WtR M s (z.im * w.im) c' * ((2 * s * Bnd (z.im / M)) * (2 * s * Bnd (w.im / M)) * (1 * 1) *
          (2 * ((Lm M c' : ℕ) : ℝ))) := by gcongr
    _ = 4 * s ^ 2 * (Bnd (z.im / M) * Bnd (w.im / M)) * (WtR M s (z.im * w.im) c' * (2 * ((Lm M c' : ℕ) : ℝ))) := by
        ring
    _ ≤ 4 * s ^ 2 * (Bnd (z.im / M) * Bnd (w.im / M)) * (2 * max 1 (z.im * w.im) * ((c' : ℝ) + 1) ^ (-(1 + 2 * s))) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

/-! ### `Σ (c'+1)^(-1-ε) ≤ 1 + 1/ε` -/

lemma rpow_step {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ε * (((n + 1 : ℕ) : ℝ) + 1) ^ (-(1 + ε)) ≤ ((n : ℝ) + 1) ^ (-ε) - (((n + 1 : ℕ) : ℝ) + 1) ^ (-ε) := by
  have e2 : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  rw [e2]
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hu : 0 < ((n : ℝ) + 1) / ((n : ℝ) + 2) := div_pos ha hb
  have hexp : 1 + ε * (1 - ((n : ℝ) + 1) / ((n : ℝ) + 2)) ≤ (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ (-ε) := by
    rw [Real.rpow_def_of_pos hu]
    have hlog := Real.log_le_sub_one_of_pos hu
    have h1 := Real.add_one_le_exp (Real.log (((n : ℝ) + 1) / ((n : ℝ) + 2)) * -ε)
    have h2 := mul_le_mul_of_nonneg_left hlog hε.le
    nlinarith
  have hsplit : ((n : ℝ) + 1) ^ (-ε) = ((n : ℝ) + 2) ^ (-ε) * (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ (-ε) := by
    rw [← Real.mul_rpow hb.le hu.le, mul_div_cancel₀ _ hb.ne']
  have hb1 : ((n : ℝ) + 2) ^ (-(1 + ε)) = ((n : ℝ) + 2) ^ (-ε) * ((n : ℝ) + 2)⁻¹ := by
    rw [show -(1 + ε) = -ε + (-1) by ring, Real.rpow_add hb, Real.rpow_neg_one]
  have h1u : 1 - ((n : ℝ) + 1) / ((n : ℝ) + 2) = ((n : ℝ) + 2)⁻¹ := by
    rw [one_sub_div hb.ne', inv_eq_one_div]; congr 1; ring
  rw [h1u] at hexp
  rw [hsplit, hb1]
  have hbpos : 0 < ((n : ℝ) + 2) ^ (-ε) := Real.rpow_pos_of_pos hb _
  have := mul_le_mul_of_nonneg_left hexp hbpos.le
  nlinarith

theorem sum_rpow_le {ε : ℝ} (hε : 0 < ε) :
    Summable (fun c' : ℕ => ((c' : ℝ) + 1) ^ (-(1 + ε))) ∧
      ∑' c' : ℕ, ((c' : ℝ) + 1) ^ (-(1 + ε)) ≤ 1 + 1 / ε := by
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) ^ (-(1 + ε)) := fun n => Real.rpow_nonneg (by positivity) _
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-(1 + ε)) ≤ 1 + 1 / ε := by
    intro N
    rcases N with _ | K
    · simp only [Finset.range_zero, Finset.sum_empty]; positivity
    · rw [Finset.sum_range_succ']
      have htel : ε * ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(1 + ε)) ≤ 1 := by
        rw [Finset.mul_sum]
        calc ∑ i ∈ Finset.range K, ε * (((i + 1 : ℕ) : ℝ) + 1) ^ (-(1 + ε))
            ≤ ∑ i ∈ Finset.range K, ((((i : ℕ) : ℝ) + 1) ^ (-ε) - (((i + 1 : ℕ) : ℝ) + 1) ^ (-ε)) :=
              Finset.sum_le_sum fun i _ => rpow_step hε i
          _ = (((0 : ℕ) : ℝ) + 1) ^ (-ε) - (((K : ℕ) : ℝ) + 1) ^ (-ε) :=
              Finset.sum_range_sub' (fun i : ℕ => ((i : ℝ) + 1) ^ (-ε)) K
          _ ≤ 1 := by
            have : 0 ≤ (((K : ℕ) : ℝ) + 1) ^ (-ε) := Real.rpow_nonneg (by positivity) _
            simp only [Nat.cast_zero, zero_add, Real.one_rpow]; linarith
      have h0 : (((0 : ℕ) : ℝ) + 1) ^ (-(1 + ε)) = 1 := by simp
      rw [h0]
      have : ∑ i ∈ Finset.range K, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(1 + ε)) ≤ 1 / ε := by
        rw [le_div_iff₀ hε, mul_comm]; exact htel
      linarith
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

end RamanujanPetersson.KernelSD


