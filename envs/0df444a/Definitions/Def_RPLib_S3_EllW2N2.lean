-- Prove2me | Definitions.Def_RPLib_S3_EllW2N2
-- name    : RPLib_S3_EllW2N2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:28:21.706197+00:00
-- url     : https://prove2.me/theorems/1e5c000e-ca03-43ad-a700-b4988b721f46
-- title:
--   The Eichler-Selberg trace formula in weight two: Stokes for the non-split hyperbolic part at `s > 0` on `𝒟_Y`
-- statement:
--   Stokes for the non-split hyperbolic part at `s > 0` on `𝒟_Y`.
--
--   * `GsI`: the `stokes_gs` integrand; `RD = R^(-s-1) / y²`; both are integrable on `regY` and bounded by
--     `8 ENs`, `4 ENs` (`norm_phiG_two`: `‖φ_g‖ = R⁻¹`).
--   * `integral_trunc_wtN`: a `wtN`-weighted series with uniformly `ENs`-bounded terms integrates termwise on `𝒟_Y`.
--   * `NHS_eq`: `NHS_s = Σ' wtN · φ_g · n^s R^(-s)`; `SNH s z = Σ' wtN · R^(-s-1)`.
--   * **`integral_truncN`**: `∫_{𝒟_Y} NHS_s = -n^s Σ' wtN · topIs - n^s (s/(1+s)) ∫_{𝒟_Y} SNH_s`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2N

/-!
# S3-ES-Wt2 (O6, file N2): Stokes for the non-split hyperbolic part at `s > 0` on `𝒟_Y`

* `GsI`: the `stokes_gs` integrand; `RD = R^(-s-1) / y²`; both are integrable on `regY` and bounded by
  `8 ENs`, `4 ENs` (`norm_phiG_two`: `‖φ_g‖ = R⁻¹`).
* `integral_trunc_wtN`: a `wtN`-weighted series with uniformly `ENs`-bounded terms integrates termwise on `𝒟_Y`.
* `NHS_eq`: `NHS_s = Σ' wtN · φ_g · n^s R^(-s)`; `SNH s z = Σ' wtN · R^(-s-1)`.
* **`integral_truncN`**: `∫_{𝒟_Y} NHS_s = -n^s Σ' wtN · topIs - n^s (s/(1+s)) ∫_{𝒟_Y} SNH_s`.
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups Modular Topology

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

/-- The integrand of `stokes_gs`. -/
def GsI (g : Matrix (Fin 2) (Fin 2) ℤ) (s : ℝ) (p : ℝ × ℝ) : ℂ :=
  (phiG 2 g (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * I)) *
    ((Rc g p.1 p.2 ^ (-s) : ℝ) : ℂ) + ((s / (1 + s) * Rc g p.1 p.2 ^ (-s - 1) : ℝ) : ℂ)) /
    ((p.2 : ℂ) ^ 2)

/-- `R^(-s-1) / y²`. -/
def RD (g : Matrix (Fin 2) (Fin 2) ℤ) (s : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((Rc g p.1 p.2 ^ (-s - 1) : ℝ) : ℂ) / ((p.2 : ℂ) ^ 2)

lemma re_im_ofC {p : ℝ × ℝ} (hy : 0 < p.2) :
    ((ofComplex ((p.1 : ℂ) + p.2 * I) : ℍ) : ℂ).re = p.1 ∧
      ((ofComplex ((p.1 : ℂ) + p.2 * I) : ℍ) : ℂ).im = p.2 := by
  have hy' : 0 < ((p.1 : ℂ) + p.2 * I).im := by simpa using hy
  have hc : ((ofComplex ((p.1 : ℂ) + p.2 * I) : ℍ) : ℂ) = (p.1 : ℂ) + p.2 * I := by
    rw [ofComplex_apply_of_im_pos hy']
    try rfl
  rw [hc]
  simp

variable {g : Matrix (Fin 2) (Fin 2) ℤ}

lemma norm_phiG_two (hdet : 0 < g.det) (z : ℍ) :
    ‖phiG 2 g z‖ = (Rc g (z : ℂ).re (z : ℂ).im)⁻¹ := by
  have hy : 0 < (z : ℂ).im := z.im_pos
  have h1 := Rc_mul g hy.ne'
  rw [HypPar.Cf_conj, Complex.normSq_conj] at h1
  have hR := Rc_pos hdet hy
  have e : ‖phiG 2 g z‖ = z.im ^ 2 / normSq (Q g (z : ℂ) (-conj (z : ℂ))) := by
    unfold phiG
    rw [norm_mul, Complex.norm_conj, norm_inv, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg z.im_pos.le, Complex.normSq_eq_norm_sq]
    ring
  rw [e, ← h1]
  rw [UpperHalfPlane.coe_im] at hR ⊢
  have h2 : z.im ≠ 0 := z.im_pos.ne'
  have h3 : Rc g (z : ℂ).re z.im ≠ 0 := hR.ne'
  field_simp

lemma regY_facts (hdet : 0 < g.det) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) {p : ℝ × ℝ}
    (hp : p ∈ HypPar.regY Y) :
    0 < Rc g p.1 p.2 ∧ Rc g p.1 p.2 ^ (-s - 1) ≤ ENs s Y g ∧ (1 / 4 : ℝ) ≤ p.2 ^ 2 := by
  have hK := HypPar.inK_of_regY hp
  have hy : 0 < p.2 := HypPar.im_pos_of_mem_regY hp
  have hre : ((p.1 : ℂ) + p.2 * I).re = p.1 := by simp
  have him : ((p.1 : ℂ) + p.2 * I).im = p.2 := by simp
  have hR := Rc_pos hdet (z := (p.1 : ℂ) + p.2 * I) (by rw [him]; exact hy)
  have hge := Rc_ge_K hdet hY hK
  have h2 : (1 / 2 : ℝ) ≤ p.2 := by have := hK.2.1; rwa [him] at this
  rw [hre, him] at hR hge
  have hNK : 0 < N g / (144 * Y ^ 6) := div_pos (N_pos hdet) (by positivity)
  exact ⟨hR, Real.rpow_le_rpow_of_nonpos hNK hge (by linarith), by nlinarith⟩

lemma norm_GsI_le (hdet : 0 < g.det) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) {p : ℝ × ℝ}
    (hp : p ∈ HypPar.regY Y) : ‖GsI g s p‖ ≤ 8 * ENs s Y g := by
  obtain ⟨hR, hE, hy2⟩ := regY_facts hdet hs hY hp
  have hy := HypPar.im_pos_of_mem_regY hp
  obtain ⟨hre, him⟩ := re_im_ofC hy
  have hphi : ‖phiG 2 g (ofComplex ((p.1 : ℂ) + p.2 * I))‖ = (Rc g p.1 p.2)⁻¹ := by
    rw [norm_phiG_two hdet, hre, him]
  have hc : s / (1 + s) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hc0 : 0 ≤ s / (1 + s) := div_nonneg hs (by linarith)
  have hRR : (Rc g p.1 p.2)⁻¹ * Rc g p.1 p.2 ^ (-s) = Rc g p.1 p.2 ^ (-s - 1) := by
    rw [Real.rpow_sub_one hR.ne', div_eq_mul_inv, mul_comm]
  have hP : 0 ≤ Rc g p.1 p.2 ^ (-s - 1) := Real.rpow_nonneg hR.le _
  have hnum : ‖phiG 2 g (ofComplex ((p.1 : ℂ) + p.2 * I)) * ((Rc g p.1 p.2 ^ (-s) : ℝ) : ℂ) +
      ((s / (1 + s) * Rc g p.1 p.2 ^ (-s - 1) : ℝ) : ℂ)‖ ≤ 2 * Rc g p.1 p.2 ^ (-s - 1) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hphi, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hR.le _), Real.norm_of_nonneg (mul_nonneg hc0 hP), hRR]
    nlinarith
  unfold GsI
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hy.le, div_le_iff₀ (pow_pos hy 2)]
  have hE0 := ENs_nonneg s Y g
  calc _ ≤ 2 * Rc g p.1 p.2 ^ (-s - 1) := hnum
    _ ≤ 2 * ENs s Y g := by linarith
    _ ≤ 8 * ENs s Y g * p.2 ^ 2 := by nlinarith

lemma norm_RD_le (hdet : 0 < g.det) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y) {p : ℝ × ℝ}
    (hp : p ∈ HypPar.regY Y) : ‖RD g s p‖ ≤ 4 * ENs s Y g := by
  obtain ⟨hR, hE, hy2⟩ := regY_facts hdet hs hY hp
  have hy := HypPar.im_pos_of_mem_regY hp
  have hE0 := ENs_nonneg s Y g
  unfold RD
  rw [norm_div, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hR.le _), Real.norm_of_nonneg hy.le, div_le_iff₀ (pow_pos hy 2)]
  nlinarith

lemma integrableOn_GsI (hdet : 0 < g.det) (hq : HypPar.GoodQ g) {s : ℝ} (hs : 0 ≤ s) (Y : ℝ) :
    IntegrableOn (GsI g s) (HypPar.regY Y) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      -(VsY g s ((p.1 : ℂ) + p.2 * I) + I * VsX g s ((p.1 : ℂ) + p.2 * I))) (HypPar.regY Y) :=
    ((HypPar.continuousOn_regY (contOn_VsY hdet hq s) Y).add
      (continuousOn_const.mul (HypPar.continuousOn_regY (contOn_VsX hdet hq s) Y))).neg
  refine (hc.integrableOn_compact (HypPar.isCompact_regY Y)).congr_fun (fun p hp => ?_)
    (HypPar.isClosed_regY Y).measurableSet
  exact Vs_identity hdet hq s hs p.1 p.2 (HypPar.im_pos_of_mem_regY hp)

lemma integrableOn_RD (hdet : 0 < g.det) (s Y : ℝ) : IntegrableOn (RD g s) (HypPar.regY Y) := by
  have hW : ContinuousOn (fun z : ℂ => ((Rc g z.re z.im ^ (-s - 1) : ℝ) : ℂ) / ((z.im : ℂ) ^ 2))
      {z : ℂ | 0 < z.im} :=
    (continuous_ofReal.comp_continuousOn (contOn_rpow hdet (-s - 1))).div
      ((continuous_ofReal.comp Complex.continuous_im).pow 2).continuousOn
      (fun z hz => pow_ne_zero _ (ofReal_ne_zero.2 (ne_of_gt hz)))
  refine ((HypPar.continuousOn_regY hW Y).congr fun p _ => ?_).integrableOn_compact
    (HypPar.isCompact_regY Y)
  simp [RD]

lemma norm_setIntegral_regY_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E} {Y B : ℝ} (hf : ∀ p ∈ HypPar.regY Y, ‖f p‖ ≤ B) :
    ‖∫ p in HypPar.regY Y, f p‖ ≤ B * volume.real (HypPar.regY Y) :=
  norm_setIntegral_le_of_norm_le_const ((HypPar.isCompact_regY Y).measure_lt_top (μ := volume)) hf

/-! ## Termwise integration of `wtN`-weighted series -/

section Generic

variable {n : ℤ} {G : S3.Conj.Mat → ℝ × ℝ → ℂ} {s Y C : ℝ}

lemma integrable_wtN_mul (δ' : ZMod M)
    (hI : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g → IntegrableOn (G g) (HypPar.regY Y))
    (g : S3.Conj.Mat) :
    Integrable (fun p => wtN M n δ' g * G g p) (volume.restrict (HypPar.regY Y)) := by
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
  · exact Integrable.const_mul (hI g h.1 h.2.1 h.2.2) _
  · simp only [wtN_of_not h, zero_mul]
    exact integrable_zero _ _ _

lemma integral_norm_wtN_le (δ' : ZMod M) (hC : 0 ≤ C)
    (hG : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      ∀ p ∈ HypPar.regY Y, ‖G g p‖ ≤ C * ENs s Y g)
    (g : S3.Conj.Mat) :
    ∫ p in HypPar.regY Y, ‖wtN M n δ' g * G g p‖ ≤
      ((Fintype.card (Fin 2 → ZMod M) : ℝ) * C * volume.real (HypPar.regY Y)) *
        {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n}.indicator (ENs s Y) g := by
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
  · rw [indicator_of_mem (show g ∈ {g : Matrix (Fin 2) (Fin 2) ℤ | g.det = n} from h.1)]
    have hb : ∀ p ∈ HypPar.regY Y, ‖‖wtN M n δ' g * G g p‖‖ ≤
        (Fintype.card (Fin 2 → ZMod M) : ℝ) * (C * ENs s Y g) := by
      intro p hp
      rw [norm_norm, norm_mul]
      exact mul_le_mul (norm_wtN_le n δ' g) (hG g h.1 h.2.1 h.2.2 p hp) (norm_nonneg _)
        (Nat.cast_nonneg _)
    have := norm_setIntegral_regY_le hb
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at this
    calc _ ≤ _ := this
      _ = _ := by ring
  · have e : ∀ p, ‖wtN M n δ' g * G g p‖ = 0 := fun p => by
      rw [wtN_of_not h, zero_mul, norm_zero]
    simp only [e, integral_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC) measureReal_nonneg)
      (indicator_nonneg (fun g _ => ENs_nonneg s Y g) g)

/-- A `wtN`-weighted series with uniformly `ENs`-bounded integrable terms integrates termwise on `𝒟_Y`. -/
lemma integral_trunc_wtN (hn : 0 < n) (δ' : ZMod M) (hs : 0 < s) (F : ℍ → ℂ) (hC : 0 ≤ C)
    (hF : ∀ p ∈ HypPar.regY Y, F (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      ∑' g : S3.Conj.Mat, wtN M n δ' g * G g p)
    (hI : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g → IntegrableOn (G g) (HypPar.regY Y))
    (hG : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      ∀ p ∈ HypPar.regY Y, ‖G g p‖ ≤ C * ENs s Y g) :
    ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, F z =
      ∑' g : S3.Conj.Mat, wtN M n δ' g * ∫ p in HypPar.regY Y, G g p := by
  have : Countable S3.Conj.Mat := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have hsum : Summable fun g : S3.Conj.Mat => ∫ p in HypPar.regY Y, ‖wtN M n δ' g * G g p‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (integral_norm_wtN_le δ' hC hG) ((summable_ENs hn hs Y).mul_left _)
  rw [HypPar.setIntegral_H_eq _ (HypPar.measurableSet_trunc Y) _ (HypPar.isClosed_regY Y).measurableSet
      (HypPar.coe_image_trunc Y),
    setIntegral_congr_fun (HypPar.isClosed_regY Y).measurableSet hF,
    ← integral_tsum_of_summable_integral_norm (integrable_wtN_mul δ' hI) hsum]
  exact tsum_congr fun g => integral_const_mul _ _

end Generic

/-! ## The non-split part -/

lemma integral_wtN_GsI {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 ≤ s) {Y : ℝ} (hY : 1 ≤ Y)
    (g : S3.Conj.Mat) :
    wtN M n δ' g * ∫ p in HypPar.regY Y, GsI g s p =
      -(wtN M n δ' g * topIs g s Y) + wtN M n δ' g * arcIs g s -
        I * (wtN M n δ' g * sideAs g s Y - wtN M n δ' g * sideBs g s Y) := by
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
  · unfold GsI
    rw [stokes_gs (by rw [h.1]; exact hn) (HypPar.goodQ_of_rest h.2.1) hs hY]; ring
  · rw [wtN_of_not h]; ring

lemma summable_wtN_GsI {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtN M n δ' g * ∫ p in HypPar.regY Y, GsI g s p :=
  summable_wtN_mul hn δ' hs Y (T := fun g => ∫ p in HypPar.regY Y, GsI g s p)
    (C := 8 * volume.real (HypPar.regY Y)) (mul_nonneg (by norm_num) measureReal_nonneg)
    fun g hg _ _ => (norm_setIntegral_regY_le fun p hp =>
      norm_GsI_le (by rw [hg]; exact hn) hs.le hY hp).trans_eq (by ring)

lemma summable_wtN_RD {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable fun g : S3.Conj.Mat => wtN M n δ' g * ∫ p in HypPar.regY Y, RD g s p :=
  summable_wtN_mul hn δ' hs Y (T := fun g => ∫ p in HypPar.regY Y, RD g s p)
    (C := 4 * volume.real (HypPar.regY Y)) (mul_nonneg (by norm_num) measureReal_nonneg)
    fun g hg _ _ => (norm_setIntegral_regY_le fun p hp =>
      norm_RD_le (by rw [hg]; exact hn) hs.le hY hp).trans_eq (by ring)

lemma tsum_GsI {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    ∑' g : S3.Conj.Mat, wtN M n δ' g * ∫ p in HypPar.regY Y, GsI g s p =
      -∑' g : S3.Conj.Mat, wtN M n δ' g * topIs g s Y := by
  rw [tsum_congr (integral_wtN_GsI hn δ' hs.le hY)]
  have hsum := ((summable_topN hn δ' hs hY).hasSum.neg.add (summable_arcN hn δ' hs hY).hasSum).sub
    (((summable_sideAN hn δ' hs hY).hasSum.sub (summable_sideBN hn δ' hs hY).hasSum).mul_left I)
  refine hsum.tsum_eq.trans ?_
  rw [tsum_arc_zeroN hn δ' s, tsum_side_eqN hn δ' s (by linarith : (0 : ℝ) < Y)]
  ring

lemma NHS_eq {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (s : ℝ) (z : ℍ) :
    NHS M n δ' s z = ∑' g : S3.Conj.Mat,
      wtN M n δ' g * (phiG 2 g z * (((n : ℝ) ^ s * Rc g (z : ℂ).re (z : ℂ).im ^ (-s) : ℝ) : ℂ)) := by
  unfold NHS
  refine tsum_congr fun g => ?_
  unfold termP wtN HypPar.wt
  by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
  · rw [if_pos h, if_neg h.2.2, if_pos (And.intro h.1 h.2.1), phiGS_eq 2 (by rw [h.1]; exact hn) s z, h.1]
  · rw [if_neg h]
    by_cases hs : IsSP g
    · rw [if_pos hs, zero_mul]
    · rw [if_neg hs, if_neg (fun h' => h ⟨h'.1, h'.2, hs⟩), zero_mul]

/-- The `R^(-s-1)` companion series. -/
def SNH (M : ℕ) [NeZero M] (n : ℤ) (δ' : ZMod M) (s : ℝ) (z : ℍ) : ℂ :=
  ∑' g : S3.Conj.Mat, wtN M n δ' g * ((Rc g (z : ℂ).re (z : ℂ).im ^ (-s - 1) : ℝ) : ℂ)

/-- **Stokes for the non-split hyperbolic part at `s > 0`.** -/
theorem integral_truncN {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z =
      -(((n : ℝ) ^ s : ℝ) : ℂ) * ∑' g : S3.Conj.Mat, wtN M n δ' g * topIs g s Y -
        (((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) *
          ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SNH M n δ' s z := by
  set K : ℂ := (((n : ℝ) ^ s : ℝ) : ℂ) with hK
  set c : ℂ := ((s / (1 + s) : ℝ) : ℂ) with hc
  have h1 : ∀ p ∈ HypPar.regY Y, NHS M n δ' s (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      ∑' g : S3.Conj.Mat, wtN M n δ' g * (K * GsI g s p - K * c * RD g s p) := by
    intro p hp
    obtain ⟨hre, him⟩ := re_im_ofC (HypPar.im_pos_of_mem_regY hp)
    rw [NHS_eq hn δ' s, ← tsum_div_const]
    refine tsum_congr fun g => ?_
    rw [hre, him]
    unfold GsI RD
    rw [hK, hc]
    simp only [Complex.ofReal_mul]
    ring
  have h2 : ∀ p ∈ HypPar.regY Y, SNH M n δ' s (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2) =
      ∑' g : S3.Conj.Mat, wtN M n δ' g * RD g s p := by
    intro p hp
    obtain ⟨hre, him⟩ := re_im_ofC (HypPar.im_pos_of_mem_regY hp)
    unfold SNH
    rw [← tsum_div_const]
    refine tsum_congr fun g => ?_
    rw [hre, him]
    unfold RD
    ring
  have hI1 : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      IntegrableOn (fun p => K * GsI g s p - K * c * RD g s p) (HypPar.regY Y) := by
    intro g hg hr _
    have hdet : 0 < g.det := by rw [hg]; exact hn
    exact Integrable.sub (Integrable.const_mul (integrableOn_GsI hdet (HypPar.goodQ_of_rest hr) hs.le Y) K)
      (Integrable.const_mul (integrableOn_RD hdet s Y) (K * c))
  have hB1 : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      ∀ p ∈ HypPar.regY Y, ‖K * GsI g s p - K * c * RD g s p‖ ≤ (‖K‖ * 8 + ‖K * c‖ * 4) * ENs s Y g := by
    intro g hg _ _ p hp
    have hdet : 0 < g.det := by rw [hg]; exact hn
    have e1 := norm_GsI_le hdet hs.le hY hp
    have e2 := norm_RD_le hdet hs.le hY hp
    calc ‖K * GsI g s p - K * c * RD g s p‖ ≤ ‖K‖ * ‖GsI g s p‖ + ‖K * c‖ * ‖RD g s p‖ :=
          (norm_sub_le _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ ‖K‖ * (8 * ENs s Y g) + ‖K * c‖ * (4 * ENs s Y g) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
      _ = _ := by ring
  have hI2 : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      IntegrableOn (fun p => RD g s p) (HypPar.regY Y) := fun g hg _ _ =>
    integrableOn_RD (by rw [hg]; exact hn) s Y
  have hB2 : ∀ g : S3.Conj.Mat, g.det = n → HypPar.IsRest g → ¬IsSP g →
      ∀ p ∈ HypPar.regY Y, ‖RD g s p‖ ≤ 4 * ENs s Y g := fun g hg _ _ p hp =>
    norm_RD_le (by rw [hg]; exact hn) hs.le hY hp
  rw [integral_trunc_wtN hn δ' hs (NHS M n δ' s) (by positivity) h1 hI1 hB1,
    integral_trunc_wtN hn δ' hs (SNH M n δ' s) (by norm_num) h2 hI2 hB2]
  have e : ∀ g : S3.Conj.Mat, wtN M n δ' g * ∫ p in HypPar.regY Y, (K * GsI g s p - K * c * RD g s p) =
      K * (wtN M n δ' g * ∫ p in HypPar.regY Y, GsI g s p) -
        K * c * (wtN M n δ' g * ∫ p in HypPar.regY Y, RD g s p) := by
    intro g
    by_cases h : g.det = n ∧ HypPar.IsRest g ∧ ¬IsSP g
    · have hdet : 0 < g.det := by rw [h.1]; exact hn
      rw [integral_sub (Integrable.const_mul (integrableOn_GsI hdet (HypPar.goodQ_of_rest h.2.1) hs.le Y) K)
        (Integrable.const_mul (integrableOn_RD hdet s Y) (K * c)), integral_const_mul, integral_const_mul]
      ring
    · rw [wtN_of_not h]; ring
  rw [tsum_congr e, ((summable_wtN_GsI hn δ' hs hY).mul_left K).tsum_sub
      ((summable_wtN_RD hn δ' hs hY).mul_left (K * c)), tsum_mul_left, tsum_mul_left, tsum_GsI hn δ' hs hY]
  ring

end RamanujanPetersson.EllW2


