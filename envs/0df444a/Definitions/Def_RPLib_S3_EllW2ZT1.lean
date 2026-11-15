-- Prove2me | Definitions.Def_RPLib_S3_EllW2ZT1
-- name    : RPLib_S3_EllW2ZT1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:28:17.345372+00:00
-- url     : https://prove2.me/theorems/54ef22ee-519c-47ad-82d7-e8a8576df51f
-- title:
--   The Eichler-Selberg trace formula in weight two: the `ℝ≥0∞` companion series `SNE` and the zero mode for every `y > 0`
-- statement:
--   The `ℝ≥0∞` companion series `SNE` and the zero mode for every `y > 0`.
--
--   * `SNE s z = Σ'_g ofReal (‖wtN g‖ R_g(z)^(-s-1))`; `measurable_SNE`; **`SNH_eq_toReal`**: `SNH = (SNE).toReal`.
--   * `Rc_smul`: `R_{h g h⁻¹}(h z) = R_g(z)`; **`SNE_smul`**: `SNE (h • z) = SNE z`.
--   * `im_smul_le_max`: `im (γ z) ≤ max (im z) (im z)⁻¹`.
--   * `CE s Y`, **`SNE_le_CE`**: `SNE z ≤ CE s (max y y⁻¹) < ∞` for every `z ∈ ℍ`.
--   * `lintegral_SNE_Ioc/Icc/Ico`: `∫⁻_{x} SNE(x + iy) = Σ' ofReal (zA g)` (`y > 0`); **`summable_zA'`** (`y > 0`).
--   * **`zA_eq'`** (`y > 0`); `ZS`; **`lintegral_SNE_Icc_ZS`**, `lintegral_SNE_Ico_ZS`: `= ofReal (ZS s y)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2RU4

/-!
# S3-ES-Wt2 (O6, file ZT1): the `ℝ≥0∞` companion series `SNE` and the zero mode for every `y > 0`

* `SNE s z = Σ'_g ofReal (‖wtN g‖ R_g(z)^(-s-1))`; `measurable_SNE`; **`SNH_eq_toReal`**: `SNH = (SNE).toReal`.
* `Rc_smul`: `R_{h g h⁻¹}(h z) = R_g(z)`; **`SNE_smul`**: `SNE (h • z) = SNE z`.
* `im_smul_le_max`: `im (γ z) ≤ max (im z) (im z)⁻¹`.
* `CE s Y`, **`SNE_le_CE`**: `SNE z ≤ CE s (max y y⁻¹) < ∞` for every `z ∈ ℍ`.
* `lintegral_SNE_Ioc/Icc/Ico`: `∫⁻_{x} SNE(x + iy) = Σ' ofReal (zA g)` (`y > 0`); **`summable_zA'`** (`y > 0`).
* **`zA_eq'`** (`y > 0`); `ZS`; **`lintegral_SNE_Icc_ZS`**, `lintegral_SNE_Ico_ZS`: `= ofReal (ZS s y)`.
-/

set_option autoImplicit false

open MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ENNReal ComplexConjugate Modular

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-! ## The series `SNE` -/

/-- The `ℝ≥0∞` companion series of `SNH`. -/
def SNE (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℝ≥0∞ :=
  ∑' g : S3.Conj.Mat, ENNReal.ofReal (‖wtN M n δ' g‖ * Rc g (z : ℂ).re (z : ℂ).im ^ (-s - 1))

lemma measurable_Rc_rpow (g : Matrix (Fin 2) (Fin 2) ℤ) (s : ℝ) :
    Measurable fun z : ℍ => Rc g (z : ℂ).re (z : ℂ).im ^ (-s - 1) := by
  have h2 : Measurable fun p : ℝ × ℝ => Rc g p.1 p.2 ^ (-s - 1) := by
    unfold Rc Pc trR; fun_prop
  have h3 : Measurable fun z : ℍ => ((z : ℂ).re, (z : ℂ).im) :=
    (Complex.measurable_re.comp measurable_coeH).prodMk (Complex.measurable_im.comp measurable_coeH)
  have h4 := h2.comp h3
  exact h4

lemma measurable_SNE (n : ℤ) (δ' : ZMod M) (s : ℝ) : Measurable (SNE M n δ' s) := by
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  unfold SNE
  exact Measurable.ennreal_tsum fun g =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_Rc_rpow g s))

/-- **`SNH` is the real part of `SNE`** (unconditionally). -/
lemma SNH_eq_toReal (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) :
    SNH M n δ' s z = (((SNE M n δ' s z).toReal : ℝ) : ℂ) := by
  unfold SNH SNE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), Complex.ofReal_tsum]
  refine tsum_congr fun g => ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Rc_nonneg' g _ _) _)),
    Complex.ofReal_mul, ← wtN_eq_norm]

/-! ## `SL₂(ℤ)` invariance -/

lemma Rc_smul (h : SL(2, ℤ)) (g : Matrix (Fin 2) (Fin 2) ℤ) (z : ℍ) :
    Rc (S3.Conj.conj h g) ((h • z : ℍ) : ℂ).re ((h • z : ℍ) : ℂ).im = Rc g (z : ℂ).re (z : ℂ).im := by
  have hz : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (z : ℂ) + (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ≠ 0 :=
    mobC_den_ne h z.im_pos
  have hw : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * conj (z : ℂ) +
      (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ≠ 0 := by
    intro h0
    apply hz
    have h1 := congrArg (starRingEnd ℂ) h0
    simpa using h1
  have e := Rc_mob g (h : Matrix (Fin 2) (Fin 2) ℤ) (Matrix.SpecialLinearGroup.det_coe h)
    z.im_pos.ne' hz hw
  rw [← HypPar.conj_coe] at e
  rw [coe_smul_eq_mobC]
  exact e

/-- **`SNE` is `SL₂(ℤ)`-invariant.** -/
lemma SNE_smul (n : ℤ) (δ' : ZMod M) (s : ℝ) (h : SL(2, ℤ)) (z : ℍ) :
    SNE M n δ' s (h • z) = SNE M n δ' s z := by
  unfold SNE
  rw [← (HypPar.conjEquiv h).tsum_eq]
  refine tsum_congr fun g => ?_
  show ENNReal.ofReal (‖wtN M n δ' (S3.Conj.conj h g)‖ *
      Rc (S3.Conj.conj h g) ((h • z : ℍ) : ℂ).re ((h • z : ℍ) : ℂ).im ^ (-s - 1)) = _
  rw [wtN_conj, Rc_smul]

lemma div_le_max_aux {y c d x : ℝ} (hy : 0 < y) (hcd : (c = 0 ∧ d ^ 2 = 1) ∨ 1 ≤ c ^ 2) :
    y / ((c * x + d) * (c * x + d) + c * y * (c * y)) ≤ max y y⁻¹ := by
  rcases hcd with ⟨hc, hd⟩ | hc
  · have e : (c * x + d) * (c * x + d) + c * y * (c * y) = 1 := by
      rw [hc]; linear_combination hd
    rw [e, div_one]; exact le_max_left _ _
  · have h1 : 1 * y ^ 2 ≤ c ^ 2 * y ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
    have hN : y ^ 2 ≤ (c * x + d) * (c * x + d) + c * y * (c * y) := by
      nlinarith [mul_self_nonneg (c * x + d)]
    have hy2 : 0 < y ^ 2 := by positivity
    calc y / ((c * x + d) * (c * x + d) + c * y * (c * y)) ≤ y / y ^ 2 :=
          div_le_div_of_nonneg_left hy.le hy2 hN
      _ = y⁻¹ := by field_simp
      _ ≤ max y y⁻¹ := le_max_right _ _

/-- `im (γ z) ≤ max (im z) (im z)⁻¹`. -/
lemma im_smul_le_max (γ : SL(2, ℤ)) (z : ℍ) : (γ • z).im ≤ max z.im z.im⁻¹ := by
  have hy := z.im_pos
  have hcd : (((γ 1 0 : ℤ) : ℝ) = 0 ∧ ((γ 1 1 : ℤ) : ℝ) ^ 2 = 1) ∨ 1 ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 := by
    by_cases h0 : γ 1 0 = 0
    · left
      have hdet : γ 0 0 * γ 1 1 = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two, h0, mul_zero, sub_zero] at h
        exact h
      refine ⟨by rw [h0, Int.cast_zero], ?_⟩
      have h2 : (γ 1 1) ^ 2 = 1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num
      exact_mod_cast h2
    · right
      have h3 : 0 < (γ 1 0) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
      have h2 : (1 : ℤ) ≤ (γ 1 0) ^ 2 := by linarith
      exact_mod_cast h2
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, add_zero]
  exact div_le_max_aux hy hcd

/-! ## The pointwise bound -/

/-- The bound `card · Σ'_{det g = n} ENs(s, max 1 Y)`. -/
def CE (M : ℕ) [NeZero M] (n : ℤ) (s Y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑' g : S3.Conj.Mat, (Fintype.card (Fin 2 → ZMod M) : ℝ) *
    {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s (max 1 Y)) g)

lemma CE_ne_top (n : ℤ) (s Y : ℝ) : CE M n s Y ≠ ∞ := ENNReal.ofReal_ne_top

lemma SNE_le_CE_of {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} {w : ℍ}
    (hre : |(w : ℂ).re| ≤ 1 / 2) (him : 1 / 2 ≤ (w : ℂ).im) (hY : (w : ℂ).im ≤ Y) :
    SNE M n δ' s w ≤ CE M n s Y := by
  have hsum := (summable_ENs hn hs (max 1 Y)).mul_left (Fintype.card (Fin 2 → ZMod M) : ℝ)
  have hnn : ∀ g : S3.Conj.Mat, 0 ≤ (Fintype.card (Fin 2 → ZMod M) : ℝ) *
      {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s (max 1 Y)) g := by
    intro g
    refine mul_nonneg (by positivity) (Set.indicator_nonneg (fun g hg => ?_) g)
    have hdet : 0 < g.det := by rw [show g.det = n from hg]; exact hn
    exact Real.rpow_nonneg (div_pos (N_pos hdet) (by positivity)).le _
  unfold SNE CE
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  refine ENNReal.tsum_le_tsum fun g => ENNReal.ofReal_le_ofReal ?_
  by_cases hd : g.det = n
  · rw [Set.indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from hd)]
    have hdet : 0 < g.det := hd ▸ hn
    have hz : HypPar.InK (max 1 Y) (w : ℂ) := ⟨hre, him, hY.trans (le_max_right 1 Y)⟩
    have hK := Rc_ge_K hdet (le_max_left 1 Y) hz
    have hR : Rc g (w : ℂ).re (w : ℂ).im ^ (-s - 1) ≤ ENs s (max 1 Y) g :=
      Real.rpow_le_rpow_of_nonpos (div_pos (N_pos hdet) (by positivity)) hK (by linarith)
    exact mul_le_mul (norm_wtN_le n δ' g) hR (Real.rpow_nonneg (Rc_nonneg' g _ _) _) (by positivity)
  · rw [Set.indicator_of_notMem (show g ∉ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from hd),
      mul_zero, wtN_det n δ' g hd, norm_zero, zero_mul]

/-- **The pointwise bound on all of `ℍ`** (via `SL₂(ℤ)` invariance). -/
theorem SNE_le_CE {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (z : ℍ) :
    SNE M n δ' s z ≤ CE M n s (max z.im z.im⁻¹) := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  rw [← SNE_smul n δ' s γ z]
  have h1 := fd_subset_stripC hγ
  have h2 : |(γ • z).re| ≤ 1 / 2 := hγ.2
  exact SNE_le_CE_of hn δ' hs h2 h1.2.2 (im_smul_le_max γ z)

/-! ## The zero mode for every `y > 0` -/

lemma SNE_ofC (n : ℤ) (δ' : ZMod M) (s : ℝ) {x y : ℝ} (hy : 0 < y) :
    SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) =
      ∑' g : S3.Conj.Mat, ENNReal.ofReal (‖wtN M n δ' g‖ * Rc g x y ^ (-s - 1)) := by
  obtain ⟨hre, him⟩ := re_im_ofC (p := (x, y)) hy
  dsimp only at hre him
  unfold SNE
  rw [hre, him]

lemma integrableOn_zterm {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y)
    (g : S3.Conj.Mat) :
    IntegrableOn (fun x : ℝ => ‖wtN M n δ' g‖ * Rc g x y ^ (-s - 1))
      (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
  by_cases hw : wtN M n δ' g = 0
  · simp only [hw, norm_zero, zero_mul]; exact integrableOn_zero
  · have hd : g.det = n := by
      by_contra hd; exact hw (wtN_det n δ' g hd)
    have hdet : 0 < g.det := hd ▸ hn
    have hcont : Continuous fun x : ℝ => ‖wtN M n δ' g‖ * Rc g x y ^ (-s - 1) := by
      refine continuous_const.mul ?_
      refine Continuous.rpow_const ?_ fun x => Or.inl ?_
      · unfold Rc Pc trR; fun_prop
      · have := Rc_pos hdet (z := (x : ℂ) + y * Complex.I) (by simpa using hy)
        simpa using this.ne'
    exact (hcont.intervalIntegrable _ _).1

theorem lintegral_SNE_Ioc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) =
      ∑' g, ENNReal.ofReal (zA M n δ' s y g) := by
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  simp_rw [SNE_ofC n δ' s hy]
  rw [lintegral_tsum fun g => ?_]
  · refine tsum_congr fun g => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_zterm hn δ' s hy g)
      (ae_of_all _ fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Rc_nonneg' g x y) _)),
      integral_const_mul, zA, intervalIntegral.integral_of_le (by norm_num)]
  · have hm : Measurable fun x : ℝ => Rc g x y ^ (-s - 1) := by
      unfold Rc Pc trR; fun_prop
    exact (ENNReal.measurable_ofReal.comp (measurable_const.mul hm)).aemeasurable

theorem lintegral_SNE_Icc {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) =
      ∑' g, ENNReal.ofReal (zA M n δ' s y g) := by
  rw [← lintegral_SNE_Ioc hn δ' s hy]
  exact setLIntegral_congr Ioc_ae_eq_Icc.symm

theorem lintegral_SNE_Ico {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x in Set.Ico (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) =
      ∑' g, ENNReal.ofReal (zA M n δ' s y g) := by
  rw [← lintegral_SNE_Ioc hn δ' s hy]
  exact setLIntegral_congr Ico_ae_eq_Ioc

/-- **`zA` is summable for every `y > 0`.** -/
theorem summable_zA' {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    Summable (zA M n δ' s y) := by
  have hle : ∑' g, ENNReal.ofReal (zA M n δ' s y g) ≤ CE M n s (max y y⁻¹) := by
    rw [← lintegral_SNE_Ioc hn δ' s hy]
    calc ∫⁻ x in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I))
        ≤ ∫⁻ _ in Set.Ioc (-(1 / 2 : ℝ)) (1 / 2), CE M n s (max y y⁻¹) := by
          refine lintegral_mono fun x => ?_
          have h := SNE_le_CE hn δ' hs (ofComplex ((x : ℂ) + y * Complex.I))
          have him : (ofComplex ((x : ℂ) + y * Complex.I)).im = y := (re_im_ofC (p := (x, y)) hy).2
          rwa [him] at h
      _ = CE M n s (max y y⁻¹) := by
          rw [setLIntegral_const, Real.volume_Ioc]; norm_num
  have hfin : ∑' g, ENNReal.ofReal (zA M n δ' s y g) ≠ ∞ := ne_top_of_le_ne_top (CE_ne_top n s _) hle
  exact (ENNReal.summable_toReal hfin).congr fun g => ENNReal.toReal_ofReal (zA_nonneg n δ' s y g)

/-! ## The zero mode in `(c, t)` form for every `y > 0` -/

/-- **The absolute zero mode in `(c, t)` form** (`y > 0`). -/
theorem zA_eq' {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy0 : 0 < y) :
    ∑' g, zA M n δ' s y g =
      ∑' ct : ℤ × ℤ, WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2 := by
  have hw : ∀ g, wZ M n δ' (tconj 1 g) = wZ M n δ' g := fun g => by
    unfold wZ; rw [wtN_tconj]
  have hw0 : ∀ g, g 1 0 = 0 → wZ M n δ' g = 0 := fun g h => by
    unfold wZ; rw [wtN_c0 n δ' g h, norm_zero, Complex.ofReal_zero]
  have hwd : ∀ g, g.det ≠ n → wZ M n δ' g = 0 := fun g h => by
    unfold wZ; rw [wtN_det n δ' g h, norm_zero, Complex.ofReal_zero]
  have hV : ∀ c t, Integrable (VZ n s y c t) := integrable_VZ hn.le hs.le hy0
  have hsum : Summable fun g => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), zmF (wZ M n δ') (VZ n s y) g x := by
    simp_rw [integral_zmF_eq]
    exact Complex.summable_ofReal.2 (summable_zA' hn δ' hs hy0)
  have hint : ∀ g, Integrable (zmF (wZ M n δ') (VZ n s y) g) := fun g =>
    ((hV _ _).comp_add_right _).const_mul (wZ M n δ' g)
  have h0 : ∀ g, g 1 0 = 0 → ∀ x, zmF (wZ M n δ') (VZ n s y) g x = 0 := by
    intro g hg x; unfold zmF; rw [hw0 g hg, zero_mul]
  have hsumR : Summable fun r : {g // IsRep g} =>
      wZ M n δ' r.1 * ∫ u, VZ n s y (r.1 1 0) (r.1 0 0 + r.1 1 1) u := by
    refine (summable_unfold_T _ (zmF_tconj _ _ hw hw0) h0 hint hsum).congr fun r => ?_
    unfold zmF; rw [integral_const_mul, integral_add_right_eq_self]
  have hZ := zero_mode_ct n (wZ M n δ') (VZ n s y) hw hw0 hwd hV hsum hsumR
  simp_rw [integral_zmF_eq] at hZ
  rw [← Complex.ofReal_tsum] at hZ
  apply Complex.ofReal_injective
  rw [hZ, Complex.ofReal_tsum]
  refine tsum_congr fun ct => ?_
  obtain ⟨c, t⟩ := ct
  dsimp only
  by_cases hc : c = 0
  · subst hc
    have e : VZ n s y 0 t = fun _ => (0 : ℂ) := by funext u; unfold VZ; rw [if_pos rfl]
    simp [e, WN, fib]
  · have e : VZ n s y c t = fun u => ((VS s c n u y t : ℝ) : ℂ) := by
      funext u; unfold VZ; rw [if_neg hc]
    simp only [e]
    rw [integral_complex_ofReal, Complex.ofReal_mul]
    congr 1
    unfold WN wZ
    rw [Complex.ofReal_sum]

/-- The absolute zero mode `Σ'_{(c,t)} WN(c,t) ∫_u VS(c,t,u)`. -/
def ZS (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s y : ℝ) : ℝ :=
  ∑' ct : ℤ × ℤ, WN M n δ' ct.1 ct.2 * ∫ u, VS s ct.1 n u y ct.2

lemma ZS_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    ZS M n δ' s y = ∑' g, zA M n δ' s y g := (zA_eq' hn δ' hs hy).symm

lemma ZS_nonneg {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ} (hy : 0 < y) :
    0 ≤ ZS M n δ' s y := by
  rw [ZS_eq hn δ' hs hy]; exact tsum_nonneg (zA_nonneg n δ' s y)

/-- **The `ℝ≥0∞` zero mode on the closed period interval.** -/
theorem lintegral_SNE_Icc_ZS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) =
      ENNReal.ofReal (ZS M n δ' s y) := by
  rw [lintegral_SNE_Icc hn δ' s hy, ZS_eq hn δ' hs hy,
    ENNReal.ofReal_tsum_of_nonneg (zA_nonneg n δ' s y) (summable_zA' hn δ' hs hy)]

theorem lintegral_SNE_Ico_ZS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {y : ℝ}
    (hy : 0 < y) :
    ∫⁻ x in Set.Ico (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) =
      ENNReal.ofReal (ZS M n δ' s y) := by
  rw [lintegral_SNE_Ico hn δ' s hy, ZS_eq hn δ' hs hy,
    ENNReal.ofReal_tsum_of_nonneg (zA_nonneg n δ' s y) (summable_zA' hn δ' hs hy)]

end RamanujanPetersson.EllW2


