-- Prove2me | Definitions.Def_RPLib_S3_KernelSDE
-- name    : RPLib_S3_KernelSDE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:38:41.634713+00:00
-- url     : https://prove2.me/theorems/87c626f2-26b9-417e-8cc9-2486d508b545
-- title:
--   The Eichler-Selberg trace formula in weight two: the MAIN sum split into the `(0,0)` modes and the rest
-- statement:
--   The MAIN sum split into the `(0,0)` modes and the rest.
--
--   All bounds take a weight `T` with `(Im z Im w)^s ≤ T` (the limit uses `T = max 1 (y v)`; the
--   uniform `y^(-1/2)` bound later uses `T = max 1 (y v)^(1/2)` for `s ≤ 1/2`).
--
--   * `WtR_le_T`, `norm_MFm_le_T`, `norm_MFm_zero_le_T`.
--   * `Fm` (modes `≠ 0` on `ℕ × (ℤ × ℤ)`), `majS`, `summable_majS`, `norm_Fm_le`, `summable_Fm`,
--     `hasSum_Fm_fiber`.
--   * `MFm_zero_s_zero`, `zero_part_le` (`Σ_{c'} ‖(0,0)-mode‖ ≤ T Bnd Bnd (8 s² + 4 s)`).
--   * `hasSum_MF_split`: `Σ_{c'} MF = Σ_{c'} MFm c' 0 + Σ_p Fm p`; `norm_tsum_MF_le`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDD2

/-!
# S3-ES-Wt2, part KS_D (E): the MAIN sum split into the `(0,0)` modes and the rest

All bounds take a weight `T` with `(Im z Im w)^s ≤ T` (the limit uses `T = max 1 (y v)`; the
uniform `y^(-1/2)` bound later uses `T = max 1 (y v)^(1/2)` for `s ≤ 1/2`).

* `WtR_le_T`, `norm_MFm_le_T`, `norm_MFm_zero_le_T`.
* `Fm` (modes `≠ 0` on `ℕ × (ℤ × ℤ)`), `majS`, `summable_majS`, `norm_Fm_le`, `summable_Fm`,
  `hasSum_Fm_fiber`.
* `MFm_zero_s_zero`, `zero_part_le` (`Σ_{c'} ‖(0,0)-mode‖ ≤ T Bnd Bnd (8 s² + 4 s)`).
* `hasSum_MF_split`: `Σ_{c'} MF = Σ_{c'} MFm c' 0 + Σ_p Fm p`; `norm_tsum_MF_le`.
-/

open Complex Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

/-! ### Bounds with a weight `T ≥ (y v)^s` -/

lemma WtR_le_T (M : ℕ) [NeZero M] {s t T : ℝ} (hs0 : 0 ≤ s) (ht : 0 < t) (hT : t ^ s ≤ T) (c' : ℕ) :
    WtR M s t c' ≤ T / ((Lm M c' : ℕ) : ℝ) ^ 2 := by
  have hX1 : 1 ≤ ((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4 :=
    le_trans (one_le_pow₀ (by linarith [(Nat.cast_nonneg c' : (0 : ℝ) ≤ c')])) (one_le_X M c')
  have hL0 : (0 : ℝ) < ((Lm M c' : ℕ) : ℝ) ^ 2 := by have := NeZero.pos (Lm M c'); positivity
  have hq : (t / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4)) ^ s ≤ T :=
    (Real.rpow_le_rpow (div_pos ht (by linarith)).le (div_le_self ht.le hX1) hs0).trans hT
  have hT0 : 0 ≤ T := (Real.rpow_nonneg ht.le s).trans hT
  unfold WtR
  calc _ ≤ T / (((M : ℝ) * (c' + 1)) ^ 2 * (M : ℝ) ^ 4) :=
        div_le_div_of_nonneg_right hq (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_left hT0 hL0 (Lm_sq_le M c')

theorem norm_MFm_le_T {M : ℕ} [NeZero M] {s T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) (c' : ℕ) (mr : ℤ × ℤ) (hmr : mr ≠ 0) :
    ‖MFm M s z w c' mr‖ ≤ T * (Bnd (z.im / M) * Bnd (w.im / M)) * majF M (mr, c') := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hy' : 0 < z.im / M := div_pos hy hMr
  have hv' : 0 < w.im / M := div_pos hv hMr
  have hB1 := Bnd_pos hy'
  have hB2 := Bnd_pos hv'
  have ht := mul_pos hy hv
  have hT0 : 0 ≤ T := (Real.rpow_nonneg ht.le s).trans hT
  have hW := WtR_le_T M hs0 ht hT c'
  have hW0 := WtR_nonneg M ht.le (s := s) c'
  have g1 := norm_gS_le hs0 hs1 hy' (mr.1 : ℝ)
  have g2 := norm_gS_le hs0 hs1 hv' (mr.2 : ℝ)
  have hL0 : (0 : ℝ) < ((Lm M c' : ℕ) : ℝ) ^ 2 := by have := NeZero.pos (Lm M c'); positivity
  have hm1 : (0 : ℝ) < 1 + (mr.1 : ℝ) ^ 2 := by positivity
  have hm2 : (0 : ℝ) < 1 + (mr.2 : ℝ) ^ 2 := by positivity
  have hg12 : ‖gS s (z.im / M) (mr.1 : ℝ)‖ * ‖gS s (w.im / M) (mr.2 : ℝ)‖ ≤
      Bnd (z.im / M) / (1 + (mr.1 : ℝ) ^ 2) * (Bnd (w.im / M) / (1 + (mr.2 : ℝ) ^ 2)) :=
    mul_le_mul g1 g2 (norm_nonneg _) (by positivity)
  rw [majF, if_neg hmr, MFm, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_coe,
    norm_fourier_coe, Complex.norm_real, Real.norm_of_nonneg hW0]
  calc WtR M s (z.im * w.im) c' * (‖gS s (z.im / M) (mr.1 : ℝ)‖ * ‖gS s (w.im / M) (mr.2 : ℝ)‖ * (1 * 1) *
        ‖KK M c' mr.1 mr.2‖)
      ≤ T / ((Lm M c' : ℕ) : ℝ) ^ 2 * (Bnd (z.im / M) / (1 + (mr.1 : ℝ) ^ 2) *
          (Bnd (w.im / M) / (1 + (mr.2 : ℝ) ^ 2)) * (1 * 1) * ‖KK M c' mr.1 mr.2‖) :=
        mul_le_mul hW (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg12 (by norm_num))
          (norm_nonneg _)) (by positivity) (div_nonneg hT0 hL0.le)
    _ = _ := by field_simp

theorem norm_MFm_zero_le_T {M : ℕ} [NeZero M] {s T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ}
    (hy : 0 < z.im) (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) (c' : ℕ) :
    ‖MFm M s z w c' 0‖ ≤ 8 * s ^ 2 * (T * (Bnd (z.im / M) * Bnd (w.im / M))) *
      ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hy' : 0 < z.im / M := div_pos hy hMr
  have hv' : 0 < w.im / M := div_pos hv hMr
  have hB1 := Bnd_pos hy'
  have hB2 := Bnd_pos hv'
  have ht : 0 < z.im * w.im := mul_pos hy hv
  have hT0 : 0 ≤ T := (Real.rpow_nonneg ht.le s).trans hT
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
  have hq : (z.im * w.im / X) ^ s ≤ T * ((c' : ℝ) + 1) ^ (-(2 * s)) := by
    rw [Real.div_rpow ht.le hX0.le, div_eq_mul_inv]
    refine mul_le_mul hT ?_ (by positivity) hT0
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
      2 * T * ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) := by
    have e : ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) =
        ((c' : ℝ) + 1) ^ (-(2 * s)) * ((c' : ℝ) + 1) ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hC]; ring_nf
    rw [e]
    calc WtR M s (z.im * w.im) c' * (2 * ((Lm M c' : ℕ) : ℝ))
        = (z.im * w.im / X) ^ s * (2 * ((Lm M c' : ℕ) : ℝ) / X) := by unfold WtR; rw [← hX]; ring
      _ ≤ (T * ((c' : ℝ) + 1) ^ (-(2 * s))) * (2 * ((c' : ℝ) + 1) ^ (-(1 : ℝ))) :=
          mul_le_mul hq hLX (by positivity) (mul_nonneg hT0 (by positivity))
      _ = _ := by ring
  have hW0 := WtR_nonneg M ht.le (s := s) c'
  simp only [MFm, Prod.fst_zero, Prod.snd_zero, Int.cast_zero]
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_coe, norm_fourier_coe, Complex.norm_real,
    Real.norm_of_nonneg hW0]
  calc WtR M s (z.im * w.im) c' * (‖gS s (z.im / M) 0‖ * ‖gS s (w.im / M) 0‖ * (1 * 1) * ‖KK M c' 0 0‖)
      ≤ WtR M s (z.im * w.im) c' * ((2 * s * Bnd (z.im / M)) * (2 * s * Bnd (w.im / M)) * (1 * 1) *
          (2 * ((Lm M c' : ℕ) : ℝ))) := by gcongr
    _ = 4 * s ^ 2 * (Bnd (z.im / M) * Bnd (w.im / M)) *
          (WtR M s (z.im * w.im) c' * (2 * ((Lm M c' : ℕ) : ℝ))) := by ring
    _ ≤ 4 * s ^ 2 * (Bnd (z.im / M) * Bnd (w.im / M)) * (2 * T * ((c' : ℝ) + 1) ^ (-(1 + 2 * s))) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

/-! ### The modes `(m, r) ≠ 0` on `ℕ × (ℤ × ℤ)` -/

def Fm (M : ℕ) [NeZero M] (s : ℝ) (z w : ℂ) (p : ℕ × (ℤ × ℤ)) : ℂ :=
  if p.2 = 0 then 0 else MFm M s z w p.1 p.2

def majS (M : ℕ) [NeZero M] (p : ℕ × (ℤ × ℤ)) : ℝ := majF M (p.2, p.1)

lemma summable_majS (M : ℕ) [NeZero M] : Summable (majS M) :=
  (summable_majF M).comp_injective Prod.swap_injective

lemma majS_nonneg (M : ℕ) [NeZero M] (p : ℕ × (ℤ × ℤ)) : 0 ≤ majS M p := majF_nonneg M _

lemma norm_Fm_le {M : ℕ} [NeZero M] {s T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) (p : ℕ × (ℤ × ℤ)) :
    ‖Fm M s z w p‖ ≤ T * (Bnd (z.im / M) * Bnd (w.im / M)) * majS M p := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hB1 := Bnd_pos (div_pos hy hMr)
  have hB2 := Bnd_pos (div_pos hv hMr)
  have hT0 : 0 ≤ T := (Real.rpow_nonneg (mul_pos hy hv).le s).trans hT
  unfold Fm majS
  split_ifs with h
  · rw [norm_zero]; exact mul_nonneg (by positivity) (majF_nonneg M _)
  · exact norm_MFm_le_T hs0 hs1 hy hv hT p.1 p.2 h

lemma summable_Fm {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) : Summable (Fm M s z w) :=
  Summable.of_norm_bounded ((summable_majS M).mul_left _)
    (norm_Fm_le hs0 hs1 hy hv (KernelSD.rpow_le_max_one (mul_pos hy hv) hs0 hs1))

lemma hasSum_Fm_fiber {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (c' : ℕ) :
    HasSum (fun mr : ℤ × ℤ => Fm M s z w (c', mr)) (MF M s z w c' - MFm M s z w c' 0) := by
  have h := (hasSum_MF (M := M) hs0 hs1 hy hv c').update 0 0
  rw [zero_sub, neg_add_eq_sub] at h
  have e : (fun mr : ℤ × ℤ => Fm M s z w (c', mr)) = Function.update (MFm M s z w c') 0 0 := by
    funext mr; simp only [Fm, Function.update_apply]
  rw [e]; exact h

/-! ### The `(0, 0)` modes -/

lemma MFm_zero_s_zero {M : ℕ} [NeZero M] {z w : ℂ} (hy : 0 < z.im) (c' : ℕ) : MFm M 0 z w c' 0 = 0 := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have g := norm_gS_zero_le le_rfl zero_le_one (div_pos hy hMr)
  have h0 : gS 0 (z.im / M) 0 = 0 := norm_le_zero_iff.mp (g.trans (by norm_num))
  simp [MFm, h0]

theorem zero_part_le {M : ℕ} [NeZero M] {s T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) :
    Summable (fun c' : ℕ => ‖MFm M s z w c' 0‖) ∧
      ∑' c' : ℕ, ‖MFm M s z w c' 0‖ ≤ T * (Bnd (z.im / M) * Bnd (w.im / M)) * (8 * s ^ 2 + 4 * s) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hB1 := Bnd_pos (div_pos hy hMr)
  have hB2 := Bnd_pos (div_pos hv hMr)
  have hT0 : 0 ≤ T := (Real.rpow_nonneg (mul_pos hy hv).le s).trans hT
  rcases hs0.eq_or_lt with h | h
  · subst h
    simp only [MFm_zero_s_zero hy, norm_zero, tsum_zero]
    exact ⟨summable_zero, by norm_num⟩
  · obtain ⟨hS, hS'⟩ := sum_rpow_le (ε := 2 * s) (by linarith)
    have hb := fun c' : ℕ => norm_MFm_zero_le_T (M := M) hs0 hs1 hy hv hT c'
    have hS2 := hS.mul_left (8 * s ^ 2 * (T * (Bnd (z.im / M) * Bnd (w.im / M))))
    have hN : Summable (fun c' : ℕ => ‖MFm M s z w c' 0‖) :=
      hS2.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    refine ⟨hN, ?_⟩
    calc ∑' c' : ℕ, ‖MFm M s z w c' 0‖
        ≤ ∑' c' : ℕ, 8 * s ^ 2 * (T * (Bnd (z.im / M) * Bnd (w.im / M))) * ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) :=
          hN.tsum_le_tsum hb hS2
      _ = 8 * s ^ 2 * (T * (Bnd (z.im / M) * Bnd (w.im / M))) *
            ∑' c' : ℕ, ((c' : ℝ) + 1) ^ (-(1 + 2 * s)) := tsum_mul_left
      _ ≤ 8 * s ^ 2 * (T * (Bnd (z.im / M) * Bnd (w.im / M))) * (1 + 1 / (2 * s)) :=
          mul_le_mul_of_nonneg_left hS' (by positivity)
      _ = _ := by field_simp; ring

/-! ### The split -/

theorem hasSum_MF_split {M : ℕ} [NeZero M] {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ} (hy : 0 < z.im)
    (hv : 0 < w.im) :
    HasSum (MF M s z w) (∑' c' : ℕ, MFm M s z w c' 0 + ∑' p, Fm M s z w p) := by
  have hT := KernelSD.rpow_le_max_one (mul_pos hy hv) hs0 hs1
  have h0 := (zero_part_le (M := M) hs0 hs1 hy hv hT).1.of_norm
  have hfib := (summable_Fm (M := M) hs0 hs1 hy hv).hasSum.prod_fiberwise
    (fun c' => hasSum_Fm_fiber hs0 hs1 hy hv c')
  have h2 := hfib.add h0.hasSum
  simp only [sub_add_cancel] at h2
  rw [add_comm]; exact h2

theorem norm_tsum_MF_le {M : ℕ} [NeZero M] {s T : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z w : ℂ}
    (hy : 0 < z.im) (hv : 0 < w.im) (hT : (z.im * w.im) ^ s ≤ T) :
    ‖∑' c' : ℕ, MF M s z w c'‖ ≤
      T * (Bnd (z.im / M) * Bnd (w.im / M)) * (∑' p, majS M p + (8 * s ^ 2 + 4 * s)) := by
  obtain ⟨hz, hzb⟩ := zero_part_le (M := M) hs0 hs1 hy hv hT
  rw [(hasSum_MF_split hs0 hs1 hy hv).tsum_eq]
  have h1 : ‖∑' c' : ℕ, MFm M s z w c' 0‖ ≤ ∑' c' : ℕ, ‖MFm M s z w c' 0‖ := norm_tsum_le_tsum_norm hz
  have h2 : ‖∑' p, Fm M s z w p‖ ≤ ∑' p, T * (Bnd (z.im / M) * Bnd (w.im / M)) * majS M p :=
    tsum_of_norm_bounded ((summable_majS M).mul_left _).hasSum (norm_Fm_le hs0 hs1 hy hv hT)
  rw [tsum_mul_left] at h2
  rw [mul_add]
  linarith [norm_add_le (∑' c' : ℕ, MFm M s z w c' 0) (∑' p, Fm M s z w p)]

end RamanujanPetersson.KernelSD


