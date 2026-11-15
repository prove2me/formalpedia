-- Prove2me | Definitions.Def_RPLib_S3_KernelSDD2
-- name    : RPLib_S3_KernelSDD2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:36:27.818446+00:00
-- url     : https://prove2.me/theorems/d3932e24-303b-497a-a776-5fb4e0977f87
-- title:
--   The Eichler-Selberg trace formula in weight two: summability of the Kloosterman majorant `majF`
-- statement:
--   Summability of the Kloosterman majorant `majF`.
--
--   * `norm_KK_div_le`: `‖KK M c' m r‖ / Lm² ≤ 2 hfun (M + 11) r m (Lm M c')`.
--   * `gcd_rpow_le`: `gcd(m, r)^(1/8) ≤ (1 + m²)^(1/4) (1 + r²)^(1/4)`.
--   * `wtK m = (1 + m²)^(-3/4)`, `summable_wtK`.
--   * `summable_majF_fiber`: for each `(m, r)`, `Σ_{c'} majF ≤ 2 CK (M + 11) wtK m wtK r`;
--     `summable_majF : Summable (majF M)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSDD

/-!
# S3-ES-Wt2, part KS_D (D2): summability of the Kloosterman majorant `majF`

* `norm_KK_div_le`: `‖KK M c' m r‖ / Lm² ≤ 2 hfun (M + 11) r m (Lm M c')`.
* `gcd_rpow_le`: `gcd(m, r)^(1/8) ≤ (1 + m²)^(1/4) (1 + r²)^(1/4)`.
* `wtK m = (1 + m²)^(-3/4)`, `summable_wtK`.
* `summable_majF_fiber`: for each `(m, r)`, `Σ_{c'} majF ≤ 2 CK (M + 11) wtK m wtK r`;
  `summable_majF : Summable (majF M)`.
-/

open Complex Filter Topology
open scoped Real

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelSD

open RamanujanPetersson.Kernel RamanujanPetersson.KernelS RamanujanPetersson.GSA

lemma Lm_injective (M : ℕ) [NeZero M] : Function.Injective (Lm M) := by
  intro a b h
  have hM : 0 < M := NeZero.pos M
  unfold Lm at h
  have h1 := Nat.eq_of_mul_eq_mul_left hM h
  have h2 := Nat.eq_of_mul_eq_mul_left hM h1
  omega

lemma CK_nonneg (N : ℕ) : 0 ≤ KL.CK N := by
  unfold KL.CK; positivity

lemma klR_Lm_le (M : ℕ) [NeZero M] (u : ZMod M) (c' : ℕ) (m r : ℤ) :
    ‖KL.klR M (Lm M c') u (m : ZMod (Lm M c')) (r : ZMod (Lm M c'))‖ / ((Lm M c' : ℕ) : ℝ) ^ 2 ≤
      KL.hfun (M + 11) m r (Lm M c') :=
  KL.norm_klR_div_le (NeZero.pos M) (by omega) (by omega) (Lm M c') (dvd_mul_right M _) u m r

lemma norm_KK_div_le (M : ℕ) [NeZero M] (c' : ℕ) (m r : ℤ) :
    ‖KK M c' m r‖ / ((Lm M c' : ℕ) : ℝ) ^ 2 ≤ 2 * KL.hfun (M + 11) r m (Lm M c') := by
  have h1 := klR_Lm_le M 1 c' r m
  have h2 := klR_Lm_le M (-1) c' r m
  have hL : (0 : ℝ) < ((Lm M c' : ℕ) : ℝ) ^ 2 := by have := NeZero.pos (Lm M c'); positivity
  unfold KK
  have hn := div_le_div_of_nonneg_right
    (norm_add_le (KL.klR M (Lm M c') 1 (r : ZMod (Lm M c')) (m : ZMod (Lm M c')))
      (KL.klR M (Lm M c') (-1) (r : ZMod (Lm M c')) (m : ZMod (Lm M c')))) hL.le
  rw [add_div] at hn
  linarith

lemma gcd_rpow_le (m r : ℤ) :
    ((Int.gcd m r : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤
      (1 + (m : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (1 + (r : ℝ) ^ 2) ^ ((1 : ℝ) / 4) := by
  have hg : Int.gcd m r ≤ m.natAbs + r.natAbs := by
    show Nat.gcd m.natAbs r.natAbs ≤ _
    rcases Nat.eq_zero_or_pos m.natAbs with h | h
    · rw [h, Nat.gcd_zero_left]; omega
    · exact (Nat.gcd_le_left _ h).trans (Nat.le_add_right _ _)
  have hgR : ((Int.gcd m r : ℕ) : ℝ) ≤ |(m : ℝ)| + |(r : ℝ)| := by
    have := (Nat.cast_le (α := ℝ)).mpr hg
    rw [Nat.cast_add, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs] at this
    exact this
  have hm := abs_nonneg (m : ℝ)
  have hr := abs_nonneg (r : ℝ)
  have hm2 : |(m : ℝ)| ^ 2 = (m : ℝ) ^ 2 := sq_abs _
  have hr2 : |(r : ℝ)| ^ 2 = (r : ℝ) ^ 2 := sq_abs _
  have hmr0 := mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg (r : ℝ))
  have hP : ((Int.gcd m r : ℕ) : ℝ) ≤ (1 + (m : ℝ) ^ 2) * (1 + (r : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (|(m : ℝ)| - 1), sq_nonneg (|(r : ℝ)| - 1)]
  have hP1 : 1 ≤ (1 + (m : ℝ) ^ 2) * (1 + (r : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (m : ℝ), sq_nonneg (r : ℝ)]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  calc ((Int.gcd m r : ℕ) : ℝ) ^ ((1 : ℝ) / 8)
      ≤ ((1 + (m : ℝ) ^ 2) * (1 + (r : ℝ) ^ 2)) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) hP (by norm_num)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)

lemma inv_mul_rpow_eq {x : ℝ} (hx : 0 < x) : x⁻¹ * x ^ ((1 : ℝ) / 4) = x ^ (-(3 / 4 : ℝ)) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hx]; congr 1; norm_num

/-- The one-variable weight `(1 + m²)^(-3/4)`. -/
def wtK (m : ℤ) : ℝ := (1 + (m : ℝ) ^ 2) ^ (-(3 / 4 : ℝ))

lemma wtK_nonneg (m : ℤ) : 0 ≤ wtK m := Real.rpow_nonneg (by positivity) _

lemma summable_wtK : Summable wtK := by
  refine summable_S1.of_nonneg_of_le (fun m => wtK_nonneg m) (fun m => ?_)
  unfold wtK
  have h1 : 0 < (max 1 |(m : ℝ)|) ^ 2 := pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) 2
  apply Real.rpow_le_rpow_of_nonpos h1 _ (by norm_num)
  rcases le_total 1 |(m : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]; linarith
  · rw [max_eq_left h]; nlinarith [sq_nonneg (m : ℝ)]

theorem summable_majF_fiber (M : ℕ) [NeZero M] (mr : ℤ × ℤ) :
    Summable (fun c' : ℕ => majF M (mr, c')) ∧
      ∑' c' : ℕ, majF M (mr, c') ≤ 2 * KL.CK (M + 11) * (wtK mr.1 * wtK mr.2) := by
  have hCK := CK_nonneg (M + 11)
  obtain ⟨m, r⟩ := mr
  by_cases h0 : (m, r) = (0 : ℤ × ℤ)
  · have hz : ∀ c' : ℕ, majF M ((m, r), c') = 0 := fun c' => by simp [majF, h0]
    simp only [hz, tsum_zero]
    exact ⟨summable_zero, mul_nonneg (mul_nonneg (by norm_num) hCK)
      (mul_nonneg (wtK_nonneg _) (wtK_nonneg _))⟩
  have hmr : r ≠ 0 ∨ m ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (by rw [hc.1, hc.2]; rfl)
  have hA0 : 0 ≤ (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ := by positivity
  have hsum := KL.summable_hfun (N := M + 11) (by omega) r m hmr
  have hsH : Summable (fun c' : ℕ => KL.hfun (M + 11) r m (Lm M c')) :=
    hsum.comp_injective (Lm_injective M)
  have hTH : ∑' c' : ℕ, KL.hfun (M + 11) r m (Lm M c') ≤
      KL.CK (M + 11) * ((Int.gcd r m : ℕ) : ℝ) ^ ((1 : ℝ) / 8) :=
    (tsum_comp_le_tsum_of_inj hsum (KL.hfun_nonneg (M + 11) r m) (Lm_injective M)).trans
      (KL.tsum_hfun_le (by omega) r m hmr)
  have hfib : ∀ c' : ℕ, majF M ((m, r), c') =
      (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ * (‖KK M c' m r‖ / ((Lm M c' : ℕ) : ℝ) ^ 2) :=
    fun c' => by unfold majF; exact if_neg h0
  have hle : ∀ c' : ℕ, majF M ((m, r), c') ≤
      (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ * (2 * KL.hfun (M + 11) r m (Lm M c')) := fun c' => by
    rw [hfib]; exact mul_le_mul_of_nonneg_left (norm_KK_div_le M c' m r) hA0
  have hs2 : Summable (fun c' : ℕ =>
      (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ * (2 * KL.hfun (M + 11) r m (Lm M c'))) :=
    (hsH.mul_left 2).mul_left _
  have hs1 : Summable (fun c' : ℕ => majF M ((m, r), c')) :=
    hs2.of_nonneg_of_le (fun c' => majF_nonneg M _) hle
  refine ⟨hs1, ?_⟩
  have hg := gcd_rpow_le r m
  have e1 := inv_mul_rpow_eq (x := 1 + (m : ℝ) ^ 2) (by positivity)
  have e2 := inv_mul_rpow_eq (x := 1 + (r : ℝ) ^ 2) (by positivity)
  have hG0 : 0 ≤ ((Int.gcd r m : ℕ) : ℝ) ^ ((1 : ℝ) / 8) := by positivity
  calc ∑' c' : ℕ, majF M ((m, r), c')
      ≤ ∑' c' : ℕ, (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ * (2 * KL.hfun (M + 11) r m (Lm M c')) :=
        hs1.tsum_le_tsum hle hs2
    _ = (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ * (2 * ∑' c' : ℕ, KL.hfun (M + 11) r m (Lm M c')) := by
        rw [tsum_mul_left, tsum_mul_left]
    _ ≤ (1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ *
          (2 * (KL.CK (M + 11) * ((Int.gcd r m : ℕ) : ℝ) ^ ((1 : ℝ) / 8))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTH (by norm_num)) hA0
    _ = 2 * KL.CK (M + 11) * ((1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ *
          ((Int.gcd r m : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) := by ring
    _ ≤ 2 * KL.CK (M + 11) * ((1 + (m : ℝ) ^ 2)⁻¹ * (1 + (r : ℝ) ^ 2)⁻¹ *
          ((1 + (r : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (1 + (m : ℝ) ^ 2) ^ ((1 : ℝ) / 4))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hA0)
          (mul_nonneg (by norm_num) hCK)
    _ = 2 * KL.CK (M + 11) * (wtK m * wtK r) := by
        rw [wtK, wtK, ← e1, ← e2]; ring

theorem summable_majF (M : ℕ) [NeZero M] : Summable (majF M) := by
  rw [summable_prod_of_nonneg (fun p => majF_nonneg M p)]
  refine ⟨fun mr => (summable_majF_fiber M mr).1, ?_⟩
  refine Summable.of_nonneg_of_le (fun mr => tsum_nonneg fun c' => majF_nonneg M _)
    (fun mr => (summable_majF_fiber M mr).2) ?_
  exact (summable_wtK.mul_of_nonneg summable_wtK wtK_nonneg wtK_nonneg).mul_left (2 * KL.CK (M + 11))

end RamanujanPetersson.KernelSD


