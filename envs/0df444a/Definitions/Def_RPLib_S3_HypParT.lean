-- Prove2me | Definitions.Def_RPLib_S3_HypParT
-- name    : RPLib_S3_HypParT
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:19:26.20721+00:00
-- url     : https://prove2.me/theorems/46097159-198b-4dbf-ac86-17ef13404505
-- title:
--   The Eichler-Selberg trace formula, hyperbolic part T: summing Stokes over the rest matrices
-- statement:
--   The weights $[\det g = n,\ g \text{ hyperbolic or parabolic}]\cdot(\text{level count})/2$, uniform bounds on the truncated region, and the identity that the truncated integral equals minus the weighted sum of top-edge integrals (arcs cancel under $S$, sides under $T$), with its limit as $Y \to \infty$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_HypParS
import Definitions.Def_RPLib_S3_HypParD

/-!
# S3-HypParTerms, part T (O4b, second half): summing Stokes over the rest matrices

* `setIntegral_H_eq`, `coe_image_trunc`: `∫_{𝒟 ∩ {im ≤ Y}} F = ∫_{regY Y} F / y²`.
* `wt`: the weight `[det = n ∧ rest] levelCount / 2`; `Ktil_eq_wt`, `wt_conj`.
* uniform bounds on the truncated region; `summable_wt_mul`.
* `integral_trunc`: `∫_{𝒟 ∩ {im ≤ Y}} Ktil = -Σ' g, wt g * topI g m Y` (arcs cancel by `S`, sides by `T`).
* `tendsto_trunc`: `-Σ' g, wt g * topI g m Y → ∫_𝒟 Ktil` as `Y → ∞`.
-/

open Complex MeasureTheory Set Filter
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.HypPar

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

/-! ## Part 1: from `ℍ` to `ℝ²` -/

theorem setIntegral_H_eq (S : Set ℍ) (hS : MeasurableSet S) (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hSR : UpperHalfPlane.coe '' S = Complex.measurableEquivRealProd ⁻¹' R) (F : ℍ → ℂ) :
    ∫ z in S, F z = ∫ p in R, F (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) := by
  have hR' : MeasurableSet (Complex.measurableEquivRealProd ⁻¹' R) :=
    Complex.measurableEquivRealProd.measurable hR
  have hmeas : MeasurableSet (UpperHalfPlane.coe '' S) := by rw [hSR]; exact hR'
  have hsub : UpperHalfPlane.coe '' S ⊆ {z : ℂ | 0 < z.im} := by
    rintro _ ⟨z, _, rfl⟩; exact z.im_pos
  have hU : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const Complex.measurable_im
  rw [← MeasureTheory.integral_indicator hS, Bergman.integral_eq_setIntegral]
  have h1 : ∫ z in {z : ℂ | 0 < z.im}, ((z.im) ^ 2)⁻¹ • S.indicator F (ofComplex z) =
      ∫ z in {z : ℂ | 0 < z.im}, (UpperHalfPlane.coe '' S).indicator
        (fun z : ℂ => ((z.im) ^ 2)⁻¹ • F (ofComplex z)) z := by
    refine setIntegral_congr_fun hU fun z hz => ?_
    have hz' : 0 < z.im := hz
    by_cases hm : ofComplex z ∈ S
    · have hz2 : z ∈ UpperHalfPlane.coe '' S :=
        ⟨ofComplex z, hm, by rw [ofComplex_apply_of_im_pos hz']⟩
      rw [indicator_of_mem hm, indicator_of_mem hz2]
    · have hz2 : z ∉ UpperHalfPlane.coe '' S := by
        rintro ⟨w, hw, rfl⟩; exact hm (by rw [ofComplex_apply]; exact hw)
      rw [indicator_of_notMem hm, indicator_of_notMem hz2, smul_zero]
  rw [h1, MeasureTheory.setIntegral_indicator hmeas, inter_eq_right.2 hsub, hSR]
  have key := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => F (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2)) R
  rw [← key]
  refine setIntegral_congr_fun hR' fun z _ => ?_
  simp only [Complex.measurableEquivRealProd_apply, Complex.re_add_im, Complex.real_smul]
  push_cast
  ring

lemma measurableSet_trunc (Y : ℝ) : MeasurableSet (𝒟 ∩ {z : ℍ | z.im ≤ Y}) :=
  ModularGroup.isClosed_fd.measurableSet.inter
    (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)

lemma coe_image_trunc (Y : ℝ) :
    UpperHalfPlane.coe '' (𝒟 ∩ {z : ℍ | z.im ≤ Y}) = Complex.measurableEquivRealProd ⁻¹' regY Y := by
  ext w
  simp only [mem_image, mem_preimage, Complex.measurableEquivRealProd_apply, regY, mem_ofPred_eq,
    mem_Icc, mem_inter_iff, arcH]
  constructor
  · rintro ⟨z, ⟨hz, hY⟩, rfl⟩
    have h1 : 1 ≤ Complex.normSq (z : ℂ) := hz.1
    have h2 : |z.re| ≤ (1 : ℝ) / 2 := hz.2
    rw [Complex.normSq_apply] at h1
    have him : 0 < (z : ℂ).im := z.im_pos
    refine ⟨abs_le.1 h2, ?_, hY⟩
    rw [Real.sqrt_le_iff]
    exact ⟨him.le, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, hY⟩
    have hs : 0 < √(1 - w.re ^ 2) := Real.sqrt_pos.2 (by nlinarith)
    have hpos : 0 < w.im := lt_of_lt_of_le hs h3
    have h4 := (Real.sqrt_le_iff.1 h3).2
    refine ⟨⟨w, hpos⟩, ⟨⟨?_, ?_⟩, hY⟩, rfl⟩
    · change 1 ≤ Complex.normSq w
      rw [Complex.normSq_apply]
      nlinarith
    · change |w.re| ≤ (1 : ℝ) / 2
      exact abs_le.2 ⟨h1, h2⟩

/-! ## Part 2: uniform bounds on the truncated region -/

/-- Points with `|x| ≤ 1/2`, `1/2 ≤ y ≤ Y`. -/
def InK (Y : ℝ) (z : ℂ) : Prop := |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im ∧ z.im ≤ Y

lemma inK_of {Y x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : 1 / 2 ≤ y) (hyY : y ≤ Y) : InK Y ((x : ℂ) + y * I) := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  unfold InK; rw [hre, him]; exact ⟨hx, hy, hyY⟩

lemma half_le_arcH_half : (1 / 2 : ℝ) ≤ arcH (1 / 2) := by
  unfold arcH
  have h : √((1 / 2 : ℝ) ^ 2) ≤ √(1 - (1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
  rwa [Real.sqrt_sq (by norm_num)] at h

lemma inK_of_regY {Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ regY Y) : InK Y ((p.1 : ℂ) + p.2 * I) :=
  inK_of (abs_le.2 ⟨hp.1.1, hp.1.2⟩) (half_le_arcH_half.trans ((arcH_ge hp.1).trans hp.2.1)) hp.2.2

lemma N_le_normSq_Q_K {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {Y : ℝ} (hY : 1 ≤ Y) {z : ℂ}
    (hz : InK Y z) : N g ≤ 144 * Y ^ 4 * normSq (Q g z (-conj z)) := by
  obtain ⟨hx, hy, hyY⟩ := hz
  have h := N_le_normSq_Q g hdet.le z (-conj z) (by linarith) (by simp; linarith)
  have e1 : (-conj z).im = z.im := by simp
  have e2 : ‖-conj z‖ = ‖z‖ := by rw [norm_neg, Complex.norm_conj]
  rw [e1, e2] at h
  have hz2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hQ : 0 ≤ normSq (Q g z (-conj z)) := normSq_nonneg _
  have hN : 0 < N g := N_pos hdet
  have hre : z.re ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 hx; nlinarith
  have him2 : z.im ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ (by linarith) hyY 2
  have hA1 : 1 + ‖z‖ ^ 2 ≤ 3 * Y ^ 2 := by rw [hz2]; nlinarith
  have hA : (1 + ‖z‖ ^ 2) * (1 + ‖z‖ ^ 2) ≤ 9 * Y ^ 4 := by
    have := mul_le_mul hA1 hA1 (by positivity) (by positivity)
    nlinarith
  have hB : (1 / 16 : ℝ) ≤ (z.im * z.im) ^ 2 := by
    have : (1 / 4 : ℝ) ≤ z.im * z.im := by nlinarith
    nlinarith
  have h3 := mul_le_mul_of_nonneg_right hA hQ
  have h4 := mul_le_mul_of_nonneg_right hB hN.le
  nlinarith

lemma inv_pow_le_of_sq (k : ℕ) {q N D : ℝ} (hq : 0 ≤ q) (hN : 0 < N) (hD : 1 ≤ D) (h : N ≤ D * q ^ 2) :
    (q ^ k)⁻¹ ≤ D ^ k * (√N ^ k)⁻¹ := by
  have hq0 : 0 < q := by
    rcases hq.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; norm_num at h; linarith
  have hs : √N ≤ D * q := by
    rw [← pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero, Real.sq_sqrt hN.le,
      mul_pow]
    have : D * q ^ 2 ≤ D ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg q)
    linarith
  have hsk : √N ^ k ≤ D ^ k * q ^ k := by rw [← mul_pow]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs k
  have hpos : 0 < √N ^ k := pow_pos (Real.sqrt_pos.2 hN) k
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (pow_pos hq0 k) hpos]
  linarith

/-- `N(g)^{-k/2}` without `rpow`. -/
def Eg (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : ℝ := (√(N g) ^ k)⁻¹

lemma Eg_nonneg (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : 0 ≤ Eg k g := by unfold Eg; positivity

lemma Eg_eq (k : ℕ) {g : Matrix (Fin 2) (Fin 2) ℤ} (hN : 0 ≤ N g) : Eg k g = N g ^ (-(k : ℝ) / 2) := by
  rw [Eg, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN, ← Real.rpow_neg hN]
  congr 1; ring

lemma summable_Eg {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) :
    Summable ({g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (Eg k)) := by
  have hs : (1 : ℝ) < (k : ℝ) / 2 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [← summable_subtype_iff_indicator]
  refine (summable_N_rpow hn hs).congr fun g => ?_
  have hg : (g : Matrix (Fin 2) (Fin 2) ℤ).det = n := g.2
  show N g.1 ^ (-((k : ℝ) / 2)) = Eg k g.1
  rw [Eg_eq k (N_pos (by rw [hg]; exact hn)).le, neg_div]

lemma norm_phiG_le_K {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (k : ℕ) {Y : ℝ} (hY : 1 ≤ Y) (z : ℍ)
    (hz : InK Y (z : ℂ)) : ‖phiG k g z‖ ≤ Y ^ k * (144 * Y ^ 4) ^ k * Eg k g := by
  have hN := N_le_normSq_Q_K hdet hY hz
  rw [← Complex.sq_norm] at hN
  have hD : (1 : ℝ) ≤ 144 * Y ^ 4 := by nlinarith [one_le_pow₀ (n := 4) hY]
  have hinv := inv_pow_le_of_sq k (norm_nonneg _) (N_pos hdet) hD hN
  rw [phiG, norm_mul, Complex.norm_conj, norm_inv, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg z.im_pos.le]
  have him : z.im ^ k ≤ Y ^ k := pow_le_pow_left₀ z.im_pos.le hz.2.2 k
  calc (‖Q g (z : ℂ) (-conj (z : ℂ))‖ ^ k)⁻¹ * z.im ^ k ≤ ((144 * Y ^ 4) ^ k * Eg k g) * Y ^ k :=
        mul_le_mul hinv him (pow_nonneg z.im_pos.le k)
          (mul_nonneg (pow_nonneg (by positivity) k) (Eg_nonneg k g))
    _ = Y ^ k * (144 * Y ^ 4) ^ k * Eg k g := by ring

lemma norm_VG_le_K {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (m : ℕ) (hm : 1 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) {z : ℂ} (hz : InK Y z) (hL : 8 * (g.det : ℝ) * Y ^ 2 * (144 * Y ^ 4) ≤ N g) :
    ‖VG g m z‖ ≤ 2 * Y ^ m * (144 * Y ^ 4) ^ (m + 1) * Eg (m + 1) g := by
  have hD : (1 : ℝ) ≤ 144 * Y ^ 4 := by nlinarith [one_le_pow₀ (n := 4) hY]
  have hy : 0 < z.im := by linarith [hz.2.1]
  have hN := N_le_normSq_Q_K hdet hY hz
  have hCQ : normSq (Cf g z (conj z)) = normSq (Q g z (-conj z)) := by
    rw [Cf_conj, Complex.normSq_conj]
  rw [← hCQ] at hN
  have hdetR : (0 : ℝ) < g.det := by exact_mod_cast hdet
  have hlarge : 8 * (g.det : ℝ) * z.im ^ 2 ≤ normSq (Cf g z (conj z)) := by
    have h1 : z.im ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hy.le hz.2.2 2
    have h2 := hL.trans hN
    have h3 : 8 * (g.det : ℝ) * Y ^ 2 ≤ normSq (Cf g z (conj z)) := by
      by_contra hc
      rw [not_le] at hc
      have := mul_lt_mul_of_pos_left hc (by linarith : (0 : ℝ) < 144 * Y ^ 4)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * g.det)]
  have hu := norm_uf_sq_le_of_large m hy hdet hlarge
  rw [← Complex.sq_norm] at hN
  have hinv := inv_pow_le_of_sq (m + 1) (norm_nonneg _) (N_pos hdet) hD hN
  have hE := Eg_nonneg (m + 1) g
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hu' : ‖uf g m z (conj z)‖ ^ 2 ≤ (2 * Y ^ m * (144 * Y ^ 4) ^ (m + 1) * Eg (m + 1) g) ^ 2 := by
    have e : 2 * (z.im ^ 2) ^ m / normSq (Cf g z (conj z)) ^ (m + 1) =
        2 * (z.im ^ m) ^ 2 * ((‖Cf g z (conj z)‖ ^ (m + 1))⁻¹) ^ 2 := by
      rw [← Complex.sq_norm]; ring
    have h1 : (z.im ^ m) ^ 2 ≤ (Y ^ m) ^ 2 :=
      pow_le_pow_left₀ (pow_nonneg hy.le m) (pow_le_pow_left₀ hy.le hz.2.2 m) 2
    have h2 : ((‖Cf g z (conj z)‖ ^ (m + 1))⁻¹) ^ 2 ≤ ((144 * Y ^ 4) ^ (m + 1) * Eg (m + 1) g) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.2 (pow_nonneg (norm_nonneg _) _)) hinv 2
    have h3 := mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
    rw [e] at hu
    nlinarith [sq_nonneg (Y ^ m * ((144 * Y ^ 4) ^ (m + 1) * Eg (m + 1) g))]
  have hpos : 0 ≤ 2 * Y ^ m * (144 * Y ^ 4) ^ (m + 1) * Eg (m + 1) g :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hY0 m)) (pow_nonneg (by positivity) _)) hE
  have hu2 := (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).1 hu'
  unfold VG
  rw [norm_div, Complex.norm_natCast]
  calc ‖uf g m z (conj z)‖ / (m : ℝ) ≤ ‖uf g m z (conj z)‖ :=
        div_le_self (norm_nonneg _) (by exact_mod_cast hm)
    _ ≤ _ := hu2

/-! ## Part 3: the weight -/

section Weight

variable {M : ℕ} [NeZero M]

open Classical in
/-- The rest weight `[det g = n ∧ rest] levelCount / 2` (the coefficient in `Ktil`). -/
def wt (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) : ℂ :=
  if g.det = n ∧ IsRest g then (S3.levelCount M δ' g : ℂ) / 2 else 0

lemma wt_of_not {n : ℤ} {δ' : ZMod M} {g : S3.Conj.Mat} (h : ¬(g.det = n ∧ IsRest g)) :
    wt M n δ' g = 0 := by
  unfold wt; rw [if_neg h]

lemma Ktil_eq_wt (k : ℕ) (n : ℤ) (δ' : ZMod M) (z : ℍ) :
    Ktil k M n δ' z = ∑' g : S3.Conj.Mat, wt M n δ' g * phiG k g z := by
  unfold Ktil wt
  congr 1; funext g
  split_ifs <;> simp

lemma norm_wt_le (n : ℤ) (δ' : ZMod M) (g : S3.Conj.Mat) :
    ‖wt M n δ' g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) := by
  have h1 : S3.levelCount M δ' g ≤ Fintype.card (Fin 2 → ZMod M) := by
    unfold S3.levelCount; exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have h1' : (S3.levelCount M δ' g : ℝ) ≤ Fintype.card (Fin 2 → ZMod M) := by exact_mod_cast h1
  have h2 : (0 : ℝ) ≤ S3.levelCount M δ' g := Nat.cast_nonneg _
  unfold wt
  split_ifs
  · rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat]
    linarith [div_le_self h2 (by norm_num : (1 : ℝ) ≤ 2)]
  · simp

lemma wt_conj (n : ℤ) (δ' : ZMod M) (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    wt M n δ' (S3.Conj.conj h g) = wt M n δ' g := by
  unfold wt
  have e : (S3.Conj.conj h g).det = n ∧ IsRest (S3.Conj.conj h g) ↔ g.det = n ∧ IsRest g := by
    rw [S3.Conj.det_conj, isRest_conj]
  by_cases hg : g.det = n ∧ IsRest g
  · rw [if_pos (e.2 hg), if_pos hg, levelCount_conj]
  · rw [if_neg (fun h' => hg (e.1 h')), if_neg hg]

lemma goodQ_of_rest {g : S3.Conj.Mat} (hr : IsRest g) : GoodQ g :=
  goodQ_of (fun h => hr (Or.inl h)) (not_lt.1 fun h => hr (Or.inr h))

lemma eventually_large {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) {R0 : ℝ} (hR0 : 0 < R0) :
    ∀ᶠ g : Matrix (Fin 2) (Fin 2) ℤ in cofinite, g.det = n → R0 ≤ N g := by
  have hs := summable_Eg hn hk
  have hε : (0 : ℝ) < (√R0 ^ k)⁻¹ := inv_pos.2 (pow_pos (Real.sqrt_pos.2 hR0) k)
  filter_upwards [hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)] with g hg hdet
  rw [indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from hdet)] at hg
  have hNp := N_pos (g := g) (by rw [hdet]; exact hn)
  unfold Eg at hg
  have h1 : √R0 ^ k < √(N g) ^ k :=
    (inv_lt_inv₀ (pow_pos (Real.sqrt_pos.2 hNp) k) (pow_pos (Real.sqrt_pos.2 hR0) k)).1 hg
  have h2 : √R0 < √(N g) := lt_of_pow_lt_pow_left₀ k (Real.sqrt_nonneg _) h1
  exact ((Real.sqrt_lt_sqrt_iff hR0.le).1 h2).le

lemma summable_wt_mul {n : ℤ} (hn : 0 < n) {k : ℕ} (hk : 3 ≤ k) (δ' : ZMod M) {T : S3.Conj.Mat → ℂ}
    {C R0 : ℝ} (hC : 0 ≤ C) (hR0 : 0 < R0)
    (hT : ∀ g : S3.Conj.Mat, g.det = n → IsRest g → R0 ≤ N g → ‖T g‖ ≤ C * Eg k g) :
    Summable fun g => wt M n δ' g * T g := by
  have hs := summable_Eg hn hk
  refine Summable.of_norm_bounded_eventually
    (hs.mul_left ((Fintype.card (Fin 2 → ZMod M) : ℝ) * C)) ?_
  filter_upwards [eventually_large hn hk hR0] with g hg
  by_cases h : g.det = n ∧ IsRest g
  · rw [norm_mul, indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from h.1)]
    have h1 := norm_wt_le n δ' g
    have h2 := hT g h.1 h.2 (hg h.1)
    calc ‖wt M n δ' g‖ * ‖T g‖ ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) * (C * Eg k g) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (Fintype.card (Fin 2 → ZMod M) : ℝ) * C * Eg k g := by ring
  · rw [wt_of_not h, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (indicator_nonneg (fun g _ => Eg_nonneg k g) g)

end Weight

/-! ## Part 4: bounds on the boundary integrals -/

/-- The uniform constant `2 Y^m (144 Y⁴)^(m+1)` of `norm_VG_le_K`. -/
def CV (m : ℕ) (Y : ℝ) : ℝ := 2 * Y ^ m * (144 * Y ^ 4) ^ (m + 1)

lemma CV_nonneg (m : ℕ) {Y : ℝ} (hY : 0 ≤ Y) : 0 ≤ CV m Y := by
  unfold CV
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hY m)) (pow_nonneg (by positivity) _)

lemma norm_topI_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) (hL : 8 * (g.det : ℝ) * Y ^ 2 * (144 * Y ^ 4) ≤ N g) :
    ‖topI g m Y‖ ≤ CV m Y * Eg (m + 1) g := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := CV m Y * Eg (m + 1) g) (f := fun x : ℝ => VG g m (x + Y * I)) (fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      exact norm_VG_le_K hdet m hm hY (inK_of (abs_le.2 ⟨hx.1.le, hx.2⟩) (by linarith) le_rfl) hL)
  refine h.trans_eq ?_
  norm_num

lemma abs_arcH'_le {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) : |arcH' x| ≤ 1 := by
  have h1 : (1 / 2 : ℝ) ≤ √(1 - x ^ 2) := half_le_arcH_half.trans (arcH_ge hx)
  have h2 : |x| ≤ 1 / 2 := abs_le.2 ⟨hx.1, hx.2⟩
  unfold arcH'
  rw [abs_div, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < √(1 - x ^ 2)), div_le_one (by linarith)]
  linarith

lemma norm_arc_factor_le {x : ℝ} (hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ‖1 - I * (arcH' x : ℂ)‖ ≤ 2 := by
  have h := abs_arcH'_le hx
  calc ‖1 - I * (arcH' x : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖I * (arcH' x : ℂ)‖ := norm_sub_le _ _
    _ = 1 + |arcH' x| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, norm_one]
    _ ≤ 2 := by linarith

lemma norm_arcI_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) (hL : 8 * (g.det : ℝ) * Y ^ 2 * (144 * Y ^ 4) ≤ N g) :
    ‖arcI g m‖ ≤ 2 * CV m Y * Eg (m + 1) g := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2 : ℝ)) (b := 1 / 2)
    (C := 2 * CV m Y * Eg (m + 1) g)
    (f := fun x : ℝ => (1 - I * (arcH' x : ℂ)) * VG g m (x + arcH x * I)) (fun x hx => by
      rw [uIoc_of_le (by norm_num)] at hx
      have hx' : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2) := ⟨hx.1.le, hx.2⟩
      have hV := norm_VG_le_K hdet m hm hY
        (inK_of (abs_le.2 ⟨hx'.1, hx'.2⟩) (half_le_arcH_half.trans (arcH_ge hx'))
          ((arcH_le_one x).trans hY)) hL
      calc ‖(1 - I * (arcH' x : ℂ)) * VG g m (x + arcH x * I)‖
          = ‖1 - I * (arcH' x : ℂ)‖ * ‖VG g m (x + arcH x * I)‖ := norm_mul _ _
        _ ≤ 2 * (CV m Y * Eg (m + 1) g) :=
            mul_le_mul (norm_arc_factor_le hx') hV (norm_nonneg _) (by norm_num)
        _ = 2 * CV m Y * Eg (m + 1) g := by ring)
  refine h.trans_eq ?_
  norm_num

lemma inK_side {Y y : ℝ} {c : ℂ} (hc : c.im = 0) (hcre : |c.re| ≤ 1 / 2)
    (hy : y ∈ Set.uIoc (arcH (1 / 2)) Y) (hY : 1 ≤ Y) : InK Y (c + y * I) := by
  rw [uIoc_of_le ((arcH_le_one _).trans hY)] at hy
  have e : c + (y : ℂ) * I = ((c.re : ℝ) : ℂ) + y * I := by
    apply Complex.ext <;> simp [hc]
  rw [e]
  exact inK_of hcre (half_le_arcH_half.trans hy.1.le) hy.2

lemma norm_side_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) (hL : 8 * (g.det : ℝ) * Y ^ 2 * (144 * Y ^ 4) ≤ N g) {c : ℂ} (hc : c.im = 0)
    (hcre : |c.re| ≤ 1 / 2) :
    ‖∫ y in arcH (1 / 2)..Y, VG g m (c + y * I)‖ ≤ CV m Y * Y * Eg (m + 1) g := by
  have hB : 0 ≤ CV m Y * Eg (m + 1) g := mul_nonneg (CV_nonneg m (by linarith)) (Eg_nonneg _ _)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := arcH (1 / 2)) (b := Y)
    (C := CV m Y * Eg (m + 1) g) (f := fun y : ℝ => VG g m (c + y * I))
    (fun y hy => norm_VG_le_K hdet m hm hY (inK_side hc hcre hy hY) hL)
  have hlen : |Y - arcH (1 / 2)| ≤ Y := by
    have h1 := arcH_half_pos
    have h2 : arcH (1 / 2) ≤ Y := (arcH_le_one _).trans hY
    rw [abs_of_nonneg (by linarith)]; linarith
  calc _ ≤ _ := h
    _ ≤ CV m Y * Eg (m + 1) g * Y := mul_le_mul_of_nonneg_left hlen hB
    _ = CV m Y * Y * Eg (m + 1) g := by ring

lemma norm_sideA_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) (hL : 8 * (g.det : ℝ) * Y ^ 2 * (144 * Y ^ 4) ≤ N g) :
    ‖sideA g m Y‖ ≤ CV m Y * Y * Eg (m + 1) g :=
  norm_side_le hdet hm hY hL (c := 1 / 2) (by simp) (by norm_num [abs_le])

lemma norm_sideB_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) (hL : 8 * (g.det : ℝ) * Y ^ 2 * (144 * Y ^ 4) ≤ N g) :
    ‖sideB g m Y‖ ≤ CV m Y * Y * Eg (m + 1) g :=
  norm_side_le hdet hm hY hL (c := -(1 / 2)) (by simp) (by norm_num [abs_le])

/-! ## Part 5: summability of the weighted boundary terms -/

section Main

variable {M : ℕ} [NeZero M]

lemma R0_pos {n : ℤ} (hn : 0 < n) {Y : ℝ} (hY : 1 ≤ Y) : 0 < 8 * (n : ℝ) * Y ^ 2 * (144 * Y ^ 4) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hY0 : 0 < Y := by linarith
  exact mul_pos (mul_pos (mul_pos (by norm_num) hnR) (pow_pos hY0 2)) (mul_pos (by norm_num) (pow_pos hY0 4))

lemma summable_top {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wt M n δ' g * topI g m Y :=
  summable_wt_mul hn (k := m + 1) (by omega) δ' (T := fun g => topI g m Y) (CV_nonneg m (by linarith))
    (R0_pos hn hY) fun g hg _ hR =>
      norm_topI_le (by rw [hg]; exact hn) (by omega) hY (by rw [hg]; exact hR)

lemma summable_arc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wt M n δ' g * arcI g m :=
  summable_wt_mul hn (k := m + 1) (by omega) δ' (T := fun g => arcI g m) (C := 2 * CV m Y)
    (mul_nonneg (by norm_num) (CV_nonneg m (by linarith))) (R0_pos hn hY) fun g hg _ hR =>
      norm_arcI_le (by rw [hg]; exact hn) (by omega) hY (by rw [hg]; exact hR)

lemma summable_sideA {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wt M n δ' g * sideA g m Y :=
  summable_wt_mul hn (k := m + 1) (by omega) δ' (T := fun g => sideA g m Y) (C := CV m Y * Y)
    (mul_nonneg (CV_nonneg m (by linarith)) (by linarith)) (R0_pos hn hY) fun g hg _ hR =>
      norm_sideA_le (by rw [hg]; exact hn) (by omega) hY (by rw [hg]; exact hR)

lemma summable_sideB {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wt M n δ' g * sideB g m Y :=
  summable_wt_mul hn (k := m + 1) (by omega) δ' (T := fun g => sideB g m Y) (C := CV m Y * Y)
    (mul_nonneg (CV_nonneg m (by linarith)) (by linarith)) (R0_pos hn hY) fun g hg _ hR =>
      norm_sideB_le (by rw [hg]; exact hn) (by omega) hY (by rw [hg]; exact hR)

/-! ## Part 6: the terms of `Ktil / y²` in coordinates -/

/-- The `g`-th term of `Ktil / y²` on `regY`. -/
def Fg (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (m : ℕ) (g : S3.Conj.Mat) (p : ℝ × ℝ) : ℂ :=
  wt M n δ' g * (phiG (m + 1) g (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2))

lemma integrableOn_phiG_div {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (hq : GoodQ g) (m : ℕ)
    (hm : 1 ≤ m) (Y : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => phiG (m + 1) g (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2))
      (regY Y) := by
  have hcont : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I := by fun_prop
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) (regY Y) {z : ℂ | 0 < z.im} := by
    intro p hp; simpa using im_pos_of_mem_regY hp
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      -(Vy g m ((p.1 : ℂ) + p.2 * I) + I * Vx g m ((p.1 : ℂ) + p.2 * I))) (regY Y) :=
    (((contOn_Vy hdet hq m).comp hcont.continuousOn hmap).add
      (continuousOn_const.mul ((contOn_Vx hdet hq m).comp hcont.continuousOn hmap))).neg
  refine (hc.integrableOn_compact (isCompact_regY Y)).congr_fun (fun p hp => ?_)
    (isClosed_regY Y).measurableSet
  have hy : 0 < ((p.1 : ℂ) + p.2 * I).im := by simpa using im_pos_of_mem_regY hp
  have key : phiG (m + 1) g (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      -(Vy g m ((p.1 : ℂ) + p.2 * I) + I * Vx g m ((p.1 : ℂ) + p.2 * I)) := by
    rw [ofComplex_apply_of_im_pos hy]
    have := V_identity_phiG m hm hdet ⟨(p.1 : ℂ) + p.2 * I, hy⟩ (hq _ hy)
    have e2 : (⟨(p.1 : ℂ) + p.2 * I, hy⟩ : UpperHalfPlane).im = p.2 := by
      show ((p.1 : ℂ) + p.2 * I).im = p.2
      simp
    rw [e2] at this
    exact this.symm
  exact key.symm

lemma integrable_Fg {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 1 ≤ m) (Y : ℝ)
    (g : S3.Conj.Mat) : Integrable (Fg M n δ' m g) (volume.restrict (regY Y)) := by
  by_cases h : g.det = n ∧ IsRest g
  · exact Integrable.const_mul
      (integrableOn_phiG_div (by rw [h.1]; exact hn) (goodQ_of_rest h.2) m hm Y) _
  · have e : Fg M n δ' m g = fun _ => 0 := by
      funext p; unfold Fg; rw [wt_of_not h, zero_mul]
    rw [e]; exact integrable_zero _ _ _

lemma norm_phiG_div_le {g : Matrix (Fin 2) (Fin 2) ℤ} (hdet : 0 < g.det) (k : ℕ) {Y : ℝ} (hY : 1 ≤ Y)
    {p : ℝ × ℝ} (hp : p ∈ regY Y) :
    ‖phiG k g (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2)‖ ≤
      4 * (Y ^ k * (144 * Y ^ 4) ^ k * Eg k g) := by
  have hy := im_pos_of_mem_regY hp
  have hy' : 0 < ((p.1 : ℂ) + p.2 * I).im := by simpa using hy
  have hK := inK_of_regY hp
  have h1 := norm_phiG_le_K hdet k hY (ofComplex ((p.1 : ℂ) + p.2 * I))
    (by rw [ofComplex_apply_of_im_pos hy']; exact hK)
  have h2 : (1 / 2 : ℝ) ≤ p.2 := half_le_arcH_half.trans ((arcH_ge hp.1).trans hp.2.1)
  have hB : 0 ≤ Y ^ k * (144 * Y ^ 4) ^ k * Eg k g :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) k) (pow_nonneg (by positivity) k)) (Eg_nonneg k g)
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy.le, div_le_iff₀ (pow_pos hy 2)]
  have h3 : (1 : ℝ) ≤ 4 * p.2 ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hB]

lemma integral_norm_Fg_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (m : ℕ) {Y : ℝ} (hY : 1 ≤ Y)
    (g : S3.Conj.Mat) :
    ∫ p in regY Y, ‖Fg M n δ' m g p‖ ≤
      ((Fintype.card (Fin 2 → ZMod M) : ℝ) * (4 * (Y ^ (m + 1) * (144 * Y ^ 4) ^ (m + 1))) *
        volume.real (regY Y)) * {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (Eg (m + 1)) g := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  have hK : 0 ≤ Y ^ (m + 1) * (144 * Y ^ 4) ^ (m + 1) :=
    mul_nonneg (pow_nonneg hY0 _) (pow_nonneg (by positivity) _)
  by_cases h : g.det = n ∧ IsRest g
  · rw [indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from h.1)]
    have hdet : 0 < g.det := by rw [h.1]; exact hn
    have hb : ∀ p ∈ regY Y, ‖‖Fg M n δ' m g p‖‖ ≤
        (Fintype.card (Fin 2 → ZMod M) : ℝ) * (4 * (Y ^ (m + 1) * (144 * Y ^ 4) ^ (m + 1) * Eg (m + 1) g)) := by
      intro p hp
      rw [norm_norm]
      unfold Fg
      rw [norm_mul]
      exact mul_le_mul (norm_wt_le n δ' g) (norm_phiG_div_le hdet (m + 1) hY hp) (norm_nonneg _)
        (Nat.cast_nonneg _)
    have := norm_setIntegral_le_of_norm_le_const ((isCompact_regY Y).measure_lt_top (μ := volume)) hb
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · have e : ∀ p, ‖Fg M n δ' m g p‖ = 0 := fun p => by
      unfold Fg; rw [wt_of_not h, zero_mul, norm_zero]
    simp only [e, integral_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hK))
      measureReal_nonneg) (indicator_nonneg (fun g _ => Eg_nonneg _ g) g)

lemma summable_integral_norm_Fg {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) {Y : ℝ}
    (hY : 1 ≤ Y) : Summable fun g : S3.Conj.Mat => ∫ p in regY Y, ‖Fg M n δ' m g p‖ :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (integral_norm_Fg_le hn δ' m hY) ((summable_Eg hn (by omega : 3 ≤ m + 1)).mul_left _)

lemma integral_Fg {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 1 ≤ m) {Y : ℝ} (hY : 1 ≤ Y)
    (g : S3.Conj.Mat) :
    ∫ p in regY Y, Fg M n δ' m g p = -(wt M n δ' g * topI g m Y) + wt M n δ' g * arcI g m -
      I * (wt M n δ' g * sideA g m Y - wt M n δ' g * sideB g m Y) := by
  unfold Fg
  rw [integral_const_mul]
  by_cases h : g.det = n ∧ IsRest g
  · rw [stokes_g (by rw [h.1]; exact hn) (goodQ_of_rest h.2) m hm hY]; ring
  · rw [wt_of_not h]; ring

/-! ## Part 7: arcs cancel under `S`, sides under `T` -/

lemma tsum_arc_zero {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (m : ℕ) :
    ∑' g : S3.Conj.Mat, wt M n δ' g * arcI g m = 0 := by
  have hpt : ∀ g : S3.Conj.Mat, wt M n δ' (conjEquiv ModularGroup.S g) *
      arcI (conjEquiv ModularGroup.S g) m = -(wt M n δ' g * arcI g m) := by
    intro g
    show wt M n δ' (S3.Conj.conj ModularGroup.S g) * arcI (S3.Conj.conj ModularGroup.S g) m = _
    rw [wt_conj]
    by_cases h : g.det = n ∧ IsRest g
    · rw [arcI_S (by rw [h.1]; exact hn) (goodQ_of_rest h.2) m]; ring
    · rw [wt_of_not h]; ring
  have e : ∑' g : S3.Conj.Mat, wt M n δ' g * arcI g m = -∑' g : S3.Conj.Mat, wt M n δ' g * arcI g m :=
    ((conjEquiv ModularGroup.S).tsum_eq (fun g => wt M n δ' g * arcI g m)).symm.trans
      ((tsum_congr hpt).trans tsum_neg)
  linear_combination e / 2

lemma tsum_side_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (m : ℕ) {Y : ℝ} (hY : 0 < Y) :
    ∑' g : S3.Conj.Mat, wt M n δ' g * sideA g m Y = ∑' g : S3.Conj.Mat, wt M n δ' g * sideB g m Y := by
  have hpt : ∀ g : S3.Conj.Mat, wt M n δ' (conjEquiv ModularGroup.T g) *
      sideA (conjEquiv ModularGroup.T g) m Y = wt M n δ' g * sideB g m Y := by
    intro g
    show wt M n δ' (S3.Conj.conj ModularGroup.T g) * sideA (S3.Conj.conj ModularGroup.T g) m Y = _
    rw [wt_conj]
    by_cases h : g.det = n ∧ IsRest g
    · rw [sideA_T (by rw [h.1]; exact hn) (goodQ_of_rest h.2) m hY]
    · rw [wt_of_not h, zero_mul, zero_mul]
  exact ((conjEquiv ModularGroup.T).tsum_eq (fun g => wt M n δ' g * sideA g m Y)).symm.trans
    (tsum_congr hpt)

/-! ## Part 8: the truncated integral and its limit -/

/-- `∫_{𝒟 ∩ {im ≤ Y}} Ktil = -Σ' g, wt g * topI g m Y`. -/
theorem integral_trunc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, Ktil (m + 1) M n δ' z =
      -∑' g : S3.Conj.Mat, wt M n δ' g * topI g m Y := by
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have h1 : ∀ p ∈ regY Y, Ktil (m + 1) M n δ' (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      ∑' g : S3.Conj.Mat, Fg M n δ' m g p := by
    intro p _
    rw [Ktil_eq_wt, ← tsum_div_const]
    exact tsum_congr fun g => by unfold Fg; ring
  rw [setIntegral_H_eq _ (measurableSet_trunc Y) _ (isClosed_regY Y).measurableSet (coe_image_trunc Y),
    setIntegral_congr_fun (isClosed_regY Y).measurableSet h1,
    ← integral_tsum_of_summable_integral_norm (integrable_Fg hn δ' (by omega) Y)
      (summable_integral_norm_Fg hn δ' hm hY),
    tsum_congr (integral_Fg hn δ' (by omega) hY)]
  have hsum := ((summable_top hn δ' hm hY).hasSum.neg.add (summable_arc hn δ' hm hY).hasSum).sub
    (((summable_sideA hn δ' hm hY).hasSum.sub (summable_sideB hn δ' hm hY).hasSum).mul_left I)
  refine hsum.tsum_eq.trans ?_
  rw [tsum_arc_zero hn δ' m, tsum_side_eq hn δ' m (by linarith : (0 : ℝ) < Y)]
  ring

/-- The truncated integrals converge: `-Σ' g, wt g * topI g m Y → ∫_𝒟 Ktil` as `Y → ∞`. -/
theorem tendsto_trunc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {m : ℕ} (hm : 2 ≤ m)
    (hfi : IntegrableOn (Ktil (m + 1) M n δ') 𝒟) :
    Tendsto (fun Y : ℝ => -∑' g : S3.Conj.Mat, wt M n δ' g * topI g m Y) atTop
      (𝓝 (∫ z in 𝒟, Ktil (m + 1) M n δ' z)) := by
  have hmono : Monotone fun Y : ℝ => 𝒟 ∩ {z : ℍ | z.im ≤ Y} :=
    fun a b hab => inter_subset_inter_right _ fun z hz => le_trans hz hab
  have hU : ⋃ Y : ℝ, 𝒟 ∩ {z : ℍ | z.im ≤ Y} = 𝒟 := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨z.im, h, le_rfl⟩⟩
  have ht := tendsto_setIntegral_of_monotone (μ := volume) (f := Ktil (m + 1) M n δ')
    (fun Y => measurableSet_trunc Y) hmono (by rw [hU]; exact hfi)
  rw [hU] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  exact integral_trunc hn δ' hm hY

end Main

end RamanujanPetersson.HypPar


