-- Prove2me | Definitions.Def_RPLib_S3_EllW2P7
-- name    : RPLib_S3_EllW2P7
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:22:57.924329+00:00
-- url     : https://prove2.me/theorems/788a9722-fc57-4f42-9af9-60e529f803f0
-- title:
--   The Eichler-Selberg trace formula in weight two: the truncated NHS integral is uniformly close to its full-domain value
-- statement:
--   The truncated NHS integral is uniformly close to its full-domain value.
--
--   * `measurable_ofComplex`, `measurable_NHS`, `measurable_phiG`, `measurable_GsI`.
--   * `integrableOn_pullF_NHS`: `pullF NHS_s` is integrable on `regY Y` (`s > 0`, `Y ≥ 1`).
--   * `norm_tail_NHS_le`: `‖∫_{Y}^{Y₂} a₀(NHS_s, y)/y² dy‖ ≤ CNA/Y`.
--   * **`norm_INS_add_le`**: for `0 < s ≤ 1`, `1 ≤ Y`:
--     `‖∫_{𝒟_Y} NHS_s + n^s (s/(1+s)) LS(s)‖ ≤ CNA M n / Y` (uniform in `s`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2NA4

/-!
# S3-ES-Wt2 (O6, file P7): the truncated NHS integral is uniformly close to its full-domain value

* `measurable_ofComplex`, `measurable_NHS`, `measurable_phiG`, `measurable_GsI`.
* `integrableOn_pullF_NHS`: `pullF NHS_s` is integrable on `regY Y` (`s > 0`, `Y ≥ 1`).
* `norm_tail_NHS_le`: `‖∫_{Y}^{Y₂} a₀(NHS_s, y)/y² dy‖ ≤ CNA/Y`.
* **`norm_INS_add_le`**: for `0 < s ≤ 1`, `1 ≤ Y`:
  `‖∫_{𝒟_Y} NHS_s + n^s (s/(1+s)) LS(s)‖ ≤ CNA M n / Y` (uniform in `s`).
-/

open MeasureTheory Set Filter Complex
open UpperHalfPlane hiding I
open scoped Real Topology Modular

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma measurable_ofComplex : Measurable (ofComplex : ℂ → ℍ) := by
  rw [measurable_iff_comap_le]
  show MeasurableSpace.comap ofComplex (MeasurableSpace.comap UpperHalfPlane.coe inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
  have e : (UpperHalfPlane.coe ∘ ofComplex) = fun w : ℂ =>
      if 0 < w.im then w else ((Classical.choice inferInstance : ℍ) : ℂ) := by
    funext w
    simp only [Function.comp_apply]
    rw [ofComplex_apply_eq_ite]
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id
    measurable_const

lemma measurable_NHS {s : ℝ} (hs : 0 < s) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) :
    Measurable (NHS M n δ' s) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  show Measurable fun z => ∑' g : S3.Conj.Mat, termP M n δ' (fun g => ¬ IsSP g) s z g
  refine measurable_tsum_of_summable (f := fun g z => termP M n δ' (fun g => ¬ IsSP g) s z g)
    (fun g => ?_) (fun z => summable_termP hs hn δ' _ z)
  unfold termP
  exact Measurable.ite (MeasurableSet.const _) ((measurable_phiGS 2 s g).const_mul _) measurable_const

lemma measurable_phiG (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Measurable (phiG k g) := by
  have hQ := measurable_Qdiag g
  have hy : Measurable fun z : ℍ => z.im := Complex.measurable_im.comp measurable_coeH
  exact (Complex.continuous_conj.measurable.comp (hQ.pow_const k).inv).mul
    ((Complex.measurable_ofReal.comp hy).pow_const k)

lemma measurable_GsI (g : S3.Conj.Mat) (s : ℝ) : Measurable (GsI g s) := by
  have h0 : Measurable fun p : ℝ × ℝ => ((p.1 : ℂ) + p.2 * I) := by fun_prop
  have h1 : Measurable fun p : ℝ × ℝ => phiG 2 g (ofComplex ((p.1 : ℂ) + p.2 * I)) :=
    (measurable_phiG 2 g).comp (measurable_ofComplex.comp h0)
  unfold GsI Rc Pc trR
  fun_prop

lemma integrableOn_pullF_NHS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) {Y : ℝ}
    (hY : 1 ≤ Y) : IntegrableOn (pullF (NHS M n δ' s)) (HypPar.regY Y) := by
  set K : ℂ := (((n : ℝ) ^ s : ℝ) : ℂ) with hK
  set c : ℂ := ((s / (1 + s) : ℝ) : ℂ) with hc
  have h := integrableOn_tsum_wtN (M := M) hn δ' hs
    (by positivity : (0 : ℝ) ≤ ‖K‖ * 8 + ‖K * c‖ * 4)
    (G := fun g p => K * GsI g s p - K * c * RD g s p)
    (fun g => ((measurable_GsI g s).const_mul K).sub ((measurable_RD g s).const_mul (K * c)))
    (fun g hg _ _ p hp => by
      have hdet : 0 < g.det := by rw [hg]; exact hn
      have e1 := norm_GsI_le hdet hs.le hY hp
      have e2 := norm_RD_le hdet hs.le hY hp
      calc ‖K * GsI g s p - K * c * RD g s p‖ ≤ ‖K‖ * ‖GsI g s p‖ + ‖K * c‖ * ‖RD g s p‖ :=
            (norm_sub_le _ _).trans (le_of_eq (by simp only [norm_mul]))
        _ ≤ ‖K‖ * (8 * ENs s Y g) + ‖K * c‖ * (4 * ENs s Y g) :=
            add_le_add (mul_le_mul_of_nonneg_left e1 (norm_nonneg _))
              (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
        _ = _ := by ring)
  refine h.congr_fun (fun p hp => ?_) (HypPar.isClosed_regY Y).measurableSet
  obtain ⟨hre, him⟩ := re_im_ofC (HypPar.im_pos_of_mem_regY hp)
  show _ = NHS M n δ' s (ofComplex ((p.1 : ℂ) + p.2 * I)) / ((p.2 : ℂ) ^ 2)
  rw [NHS_eq hn δ' s, ← tsum_div_const]
  refine tsum_congr fun g => ?_
  rw [hre, him]
  unfold GsI RD
  rw [hK, hc]
  simp only [Complex.ofReal_mul]
  ring

lemma CNA_nonneg' {n : ℤ} (hn : 0 < n) (δ' : ZMod M) : 0 ≤ CNA M n :=
  (norm_nonneg _).trans (norm_zeroMode_NHS_le hn δ' one_pos le_rfl le_rfl)

lemma integral_C_div_sq {C Y Y2 : ℝ} (hY : 1 ≤ Y) (hY2 : Y ≤ Y2) :
    ∫ y in Y..Y2, C / y ^ 2 = C / Y - C / Y2 := by
  have hpos : ∀ x ∈ uIcc Y Y2, x ≠ 0 := fun x hx => by
    rw [uIcc_of_le hY2] at hx
    exact (lt_of_lt_of_le one_pos (hY.trans hx.1)).ne'
  have hd : ∀ x ∈ uIcc Y Y2, HasDerivAt (fun y : ℝ => -(C * y⁻¹)) (C / x ^ 2) x := by
    intro x hx
    exact (((hasDerivAt_inv (hpos x hx)).const_mul C).neg).congr_deriv (by ring)
  have hc : ContinuousOn (fun y : ℝ => C / y ^ 2) (uIcc Y Y2) :=
    continuousOn_const.div (continuousOn_pow 2) fun x hx => pow_ne_zero 2 (hpos x hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp only [div_eq_mul_inv]
  ring

lemma norm_tail_NHS_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {Y Y2 : ℝ} (hY : 1 ≤ Y) (hY2 : Y ≤ Y2) :
    ‖∫ y in Y..Y2, (∫ x in (-(1 / 2 : ℝ))..(1 / 2), NHS M n δ' s (ofComplex ((x : ℂ) + y * I))) /
        ((y : ℂ) ^ 2)‖ ≤ CNA M n / Y := by
  have hb : ∀ y ∈ uIcc Y Y2, ‖(∫ x in (-(1 / 2 : ℝ))..(1 / 2),
      NHS M n δ' s (ofComplex ((x : ℂ) + y * I))) / ((y : ℂ) ^ 2)‖ ≤ CNA M n / y ^ 2 := by
    intro y hy
    rw [uIcc_of_le hY2] at hy
    have hy1 : 1 ≤ y := hY.trans hy.1
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact div_le_div_of_nonneg_right (norm_zeroMode_NHS_le hn δ' hs hs1 hy1) (by positivity)
  have hc : ContinuousOn (fun y : ℝ => CNA M n / y ^ 2) (uIcc Y Y2) :=
    continuousOn_const.div (continuousOn_pow 2) fun x hx => by
      rw [uIcc_of_le hY2] at hx
      exact pow_ne_zero 2 (lt_of_lt_of_le one_pos (hY.trans hx.1)).ne'
  refine (intervalIntegral.norm_integral_le_of_norm_le hY2
    (Eventually.of_forall fun y hy => hb y (Ioc_subset_Icc_self.trans (uIcc_of_le hY2).symm.subset hy))
    hc.intervalIntegrable).trans ?_
  rw [integral_C_div_sq hY hY2]
  have h0 := CNA_nonneg' hn δ' (M := M)
  have : 0 ≤ CNA M n / Y2 := div_nonneg h0 (by linarith)
  linarith

/-- **Uniform truncation estimate**: `‖∫_{𝒟_Y} NHS_s + n^s (s/(1+s)) LS(s)‖ ≤ CNA/Y` for `0 < s ≤ 1`. -/
theorem norm_INS_add_le {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ‖(∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z) +
      (((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s‖ ≤ CNA M n / Y := by
  have hb : ∀ Y2 : ℝ, Y ≤ Y2 → ‖(∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y2}, NHS M n δ' s z) -
      ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z‖ ≤ CNA M n / Y := fun Y2 hY2 => by
    rw [integral_trunc_sub _ hY hY2 (integrableOn_pullF_NHS hn δ' hs (hY.trans hY2))]
    exact norm_tail_NHS_le hn δ' hs hs1 hY hY2
  have ht := ((tendsto_INS hn δ' hs).sub_const
    (∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z)).norm
  have h := le_of_tendsto ht (eventually_atTop.2 ⟨Y, hb⟩)
  have e : -(((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s -
      ∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z =
      -((∫ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, NHS M n δ' s z) +
        (((n : ℝ) ^ s : ℝ) : ℂ) * ((s / (1 + s) : ℝ) : ℂ) * LS M n δ' s) := by ring
  rwa [e, norm_neg] at h

end RamanujanPetersson.EllW2


