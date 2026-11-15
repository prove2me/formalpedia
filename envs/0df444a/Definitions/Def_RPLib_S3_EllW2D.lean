-- Prove2me | Definitions.Def_RPLib_S3_EllW2D
-- name    : RPLib_S3_EllW2D
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T13:08:01.787184+00:00
-- url     : https://prove2.me/theorems/20ebdd83-2132-4c95-8d7f-ef9191a3fa78
-- title:
--   The Eichler-Selberg trace formula in weight two: measurability and the uniform bound of the regularised diagonal
-- statement:
--   Measurability and the uniform bound of the regularised diagonal.
--
--   * `measurable_tsum_of_summable`, `measurable_phiGS`, `measurable_restPartS` (`s > 0`).
--   * `continuousAt_CKG`, `continuousAt_Bk`, `mobC`, `coe_smul_eq_mobC`, `continuousAt_Gd`.
--   * **`diag_bound_trunc`**: on `ρ • (𝒟 ∩ {Im ≤ Y})` the regularised diagonal `conj ω_s(z, -z̄) y²` is bounded
--     uniformly in `0 < s ≤ 1/2`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224

import Mathlib
import Definitions.Def_RPLib_S3_EllW2C

/-!
# S3-ES-Wt2 (O6, part D, P1): measurability and the uniform bound of the regularised diagonal

* `measurable_tsum_of_summable`, `measurable_phiGS`, `measurable_restPartS` (`s > 0`).
* `continuousAt_CKG`, `continuousAt_Bk`, `mobC`, `coe_smul_eq_mobC`, `continuousAt_Gd`.
* **`diag_bound_trunc`**: on `ρ • (𝒟 ∩ {Im ≤ Y})` the regularised diagonal `conj ω_s(z, -z̄) y²` is bounded
  uniformly in `0 < s ≤ 1/2`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal ENNReal Manifold MatrixGroups Topology Modular

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson
  RamanujanPetersson.EllTerm RamanujanPetersson.KernelSD RamanujanPetersson.GSA

variable {M : ℕ}

/-! ## Part 1: measurability -/

theorem measurable_tsum_of_summable {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i)) (hs : ∀ a, Summable fun i => f i a) :
    Measurable fun a => ∑' i, f i a :=
  measurable_of_tendsto_metrizable' (SummationFilter.unconditional ι).filter
    (f := fun S a => ∑ i ∈ S, f i a) (fun S => Finset.measurable_sum S fun i _ => hf i)
    (tendsto_pi_nhds.2 fun a => (hs a).hasSum)

lemma measurable_coeH : Measurable fun z : ℍ => (z : ℂ) := UpperHalfPlane.continuous_coe.measurable

lemma measurable_Qdiag (g : Matrix (Fin 2) (Fin 2) ℤ) :
    Measurable fun z : ℍ => Q g (z : ℂ) (-conj (z : ℂ)) := by
  have hz := measurable_coeH
  have hw : Measurable fun z : ℍ => -conj (z : ℂ) := (Complex.continuous_conj.measurable.comp hz).neg
  unfold Q
  exact (((measurable_const.mul hz).mul hw).add (measurable_const.mul hw)).add
    (measurable_const.mul hz) |>.add measurable_const

lemma measurable_phiGS (k : ℕ) (s : ℝ) (g : Matrix (Fin 2) (Fin 2) ℤ) : Measurable (phiGS k s g) := by
  have hQ := measurable_Qdiag g
  have hy : Measurable fun z : ℍ => z.im := Complex.measurable_im.comp measurable_coeH
  have hy' : Measurable fun z : ℍ => (-conj (z : ℂ)).im :=
    Complex.measurable_im.comp (Complex.continuous_conj.measurable.comp measurable_coeH).neg
  have hphi : Measurable (phiG k g) :=
    (Complex.continuous_conj.measurable.comp (hQ.pow_const k).inv).mul
      ((Complex.measurable_ofReal.comp hy).pow_const k)
  have hr : Measurable fun z : ℍ => KernelS.ratQ g z (-conj (z : ℂ)) :=
    ((measurable_const.mul hy).mul hy').div (hQ.norm.pow_const 2)
  exact hphi.mul (Complex.measurable_ofReal.comp (hr.pow_const s))

theorem measurable_restPartS {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s) :
    Measurable (restPartS 2 M n δ' s) := by
  have hσ : 1 < ((2 : ℕ) : ℝ) / 2 + s := by norm_num; linarith
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  have h3 := fun z => summable_iteS 2 hσ hn δ' z (fun g : S3.Conj.Mat => ¬ ((g 1 0 = 0 ∧ g 0 1 = 0 ∧
      g 0 0 = g 1 1) ∨ (g 0 0 + g 1 1) ^ 2 < 4 * g.det))
  exact measurable_tsum_of_summable
    (fun g => Measurable.ite (MeasurableSet.const _) (measurable_phiGS 2 s _) measurable_const) h3

/-! ## Part 2: continuity of the kernel constant -/

lemma continuousAt_rho' {y : ℝ} (hy : y ≠ 0) : ContinuousAt (fun y => rho y) y := by
  unfold rho
  exact continuousAt_const.add ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hy))

lemma continuousAt_Bnd {y : ℝ} (hy : y ≠ 0) : ContinuousAt (fun y => Bnd y) y := by
  unfold Bnd
  exact (continuousAt_const.mul ((continuousAt_rho' hy).pow 2)).div continuousAt_id hy

lemma continuousAt_Kerr {t : ℝ} (ht : t ≠ 0) : ContinuousAt (fun t => Kerr t) t := by
  have hi : ContinuousAt (fun t : ℝ => t⁻¹) t := continuousAt_id.inv₀ ht
  have hm : ContinuousAt (fun t : ℝ => max 1 t⁻¹) t := continuousAt_const.max hi
  unfold Kerr
  exact (continuousAt_const.add (continuousAt_const.mul hm)).add (continuousAt_const.mul
    (((continuousAt_const.mul continuousAt_id).inv₀ (mul_ne_zero two_ne_zero ht)).add
      (hm.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht))))

lemma continuousAt_Kv {v : ℝ} (hv : 0 < v) : ContinuousAt (fun v => Kv v) v := by
  have hmin : 0 < min v (1 / 2) := lt_min hv (by norm_num)
  unfold Kv
  exact (((continuousAt_id.min continuousAt_const).pow 2).rpow_const
    (Or.inl (pow_ne_zero 2 hmin.ne'))).mul continuousAt_const

lemma continuousAt_CKG (M : ℕ) [NeZero M] {y0 v : ℝ} (hy0 : 0 < y0) (hv : 0 < v) :
    ContinuousAt (fun v => CKG M y0 v) v := by
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have h1 : ContinuousAt (fun v : ℝ => v ^ (1 / 2 : ℝ)) v :=
    continuousAt_id.rpow_const (Or.inr (by norm_num))
  have hB : ContinuousAt (fun v : ℝ => Bnd (v / M)) v :=
    (continuousAt_Bnd (div_pos hv hM).ne').comp (f := fun v : ℝ => v / M) (continuousAt_id.div_const _)
  have hK : ContinuousAt (fun v : ℝ => Kerr (y0 * v)) v :=
    (continuousAt_Kerr (mul_pos hy0 hv).ne').comp (f := fun v : ℝ => y0 * v)
      (continuousAt_const.mul continuousAt_id)
  have hp : ContinuousAt (fun v : ℝ => (v ^ 2) ^ (-(3 / 4 : ℝ))) v :=
    (continuousAt_id.pow 2).rpow_const (Or.inl (pow_ne_zero 2 hv.ne'))
  unfold CKG
  exact ((continuousAt_const.add h1).mul (continuousAt_const.add
    ((continuousAt_const.mul hB).mul continuousAt_const))).add
      (hK.mul (((continuousAt_Kv hv).mul hp).mul continuousAt_const))

lemma continuous_denW (h : Matrix (Fin 2) (Fin 2) ℤ) : Continuous fun w => denW h w := by
  unfold denW
  exact continuous_const.add (continuous_const.mul continuous_id)

lemma continuousAt_natPt {h : Matrix (Fin 2) (Fin 2) ℤ} {W : ℂ} (hD : denW h W ≠ 0) :
    ContinuousAt (fun w => natPt h w) W := by
  unfold natPt
  exact (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).div
    (continuous_denW h).continuousAt hD

theorem continuousAt_Bk [NeZero M] {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    (ρ : SL(2, ℤ)) {W : ℂ} (hW : 0 < W.im) : ContinuousAt (fun W => Bk M n u ρ W) W := by
  unfold Bk
  refine tendsto_finsetSum _ (fun x _ => ?_)
  have hdx := det_hX_pos hn hnM u x
  have hD1 : denW (hX n u x) W ≠ 0 := denW_ne_zero hdx.ne' hW
  have hN1 : ContinuousAt (fun W => natPt (hX n u x) W) W := continuousAt_natPt hD1
  have hv1 : 0 < (natPt (hX n u x) W).im := im_natPt_pos hdx hW
  have hD2 : denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W) ≠ 0 := denW_ne_zero (det_SL_ne ρ) hv1
  have hc2 : ContinuousAt (fun W => denW (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W)) W :=
    (continuous_denW _).continuousAt.comp (f := fun W => natPt (hX n u x) W) hN1
  have hN2 : ContinuousAt (fun W => natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W)) W :=
    (continuousAt_natPt hD2).comp (f := fun W => natPt (hX n u x) W) hN1
  have hv2 := im_natPt_SL_pos ρ hv1
  have hC : ContinuousAt (fun W => CKG M (1 / 2) (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ)
      (natPt (hX n u x) W)).im) W :=
    (continuousAt_CKG M (by norm_num) hv2).comp
      (f := fun W => (natPt (ρ : Matrix (Fin 2) (Fin 2) ℤ) (natPt (hX n u x) W)).im)
      (Complex.continuous_im.continuousAt.comp hN2)
  exact ((((continuous_denW _).continuousAt.pow 2).inv₀ (pow_ne_zero 2 hD1)).norm.mul
    ((hc2.pow 2).inv₀ (pow_ne_zero 2 hD2)).norm).mul hC

/-! ## Part 3: the bound on a truncated translate of `𝒟` -/

/-- The Möbius action of `ρ ∈ SL₂(ℤ)` on `ℂ`. -/
def mobC (ρ : SL(2, ℤ)) (w : ℂ) : ℂ := ((ρ 0 0 : ℂ) * w + ρ 0 1) / ((ρ 1 0 : ℂ) * w + ρ 1 1)

lemma coe_smul_eq_mobC (ρ : SL(2, ℤ)) (τ : ℍ) : ((ρ • τ : ℍ) : ℂ) = mobC ρ τ := by
  rw [coe_specialLinearGroup_apply, mobC]
  simp

lemma mobC_den_ne (ρ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) : (ρ 1 0 : ℂ) * w + ρ 1 1 ≠ 0 := by
  intro h0
  have him : ((ρ 1 0 : ℂ) * w + ρ 1 1).im = (ρ 1 0 : ℝ) * w.im := by simp
  have hre : ((ρ 1 0 : ℂ) * w + ρ 1 1).re = (ρ 1 0 : ℝ) * w.re + ρ 1 1 := by simp
  rw [h0, Complex.zero_im] at him
  have h10 : (ρ 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.1 him.symm with h | h
    · exact h
    · exact absurd h hw.ne'
  rw [h0, Complex.zero_re, h10, zero_mul, zero_add] at hre
  have h10' : ρ 1 0 = 0 := by exact_mod_cast h10
  have h11' : ρ 1 1 = 0 := by exact_mod_cast hre.symm
  have hdet : (ρ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := ρ.2
  rw [Matrix.det_fin_two, h10', h11'] at hdet
  simp at hdet

lemma continuousAt_mobC (ρ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) : ContinuousAt (mobC ρ) w := by
  unfold mobC
  exact (continuousAt_const.mul continuousAt_id |>.add continuousAt_const).div
    (continuousAt_const.mul continuousAt_id |>.add continuousAt_const) (mobC_den_ne ρ hw)

lemma im_mobC_pos (ρ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) : 0 < (mobC ρ w).im := by
  have h := (ρ • (⟨w, hw⟩ : ℍ)).im_pos
  rwa [UpperHalfPlane.im, coe_smul_eq_mobC] at h

/-- The majorant `Bk(ρ, -conj(ρ w)) (Im w)^(1/2) Im(ρ w)` of the diagonal on `ρ • 𝒟`. -/
def Gd (M : ℕ) [NeZero M] (n : ℕ) (u : (ZMod M)ˣ) (ρ : SL(2, ℤ)) (w : ℂ) : ℝ :=
  Bk M n u ρ (-conj (mobC ρ w)) * w.im ^ (1 / 2 : ℝ) * (mobC ρ w).im

lemma continuousAt_Gd [NeZero M] {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (u : (ZMod M)ˣ)
    (ρ : SL(2, ℤ)) {w : ℂ} (hw : 0 < w.im) : ContinuousAt (Gd M n u ρ) w := by
  have hm := continuousAt_mobC ρ hw
  have hW : ContinuousAt (fun w => -conj (mobC ρ w)) w :=
    (Complex.continuous_conj.continuousAt.comp (f := mobC ρ) hm).neg
  have hW0 : 0 < (-conj (mobC ρ w)).im := by simpa using im_mobC_pos ρ hw
  have hB : ContinuousAt (fun w => Bk M n u ρ (-conj (mobC ρ w))) w :=
    (continuousAt_Bk hn hnM u ρ hW0).comp (f := fun w => -conj (mobC ρ w)) hW
  unfold Gd
  exact (hB.mul (Complex.continuous_im.continuousAt.rpow_const (Or.inr (by norm_num)))).mul
    (Complex.continuous_im.continuousAt.comp (f := mobC ρ) hm)

/-- The compact truncated strip `{|Re w| ≤ 1/2, 1/2 ≤ Im w ≤ Y}`. -/
def stripY (Y : ℝ) : Set ℂ := {w : ℂ | |w.re| ≤ 1 / 2 ∧ 1 / 2 ≤ w.im ∧ w.im ≤ Y}

lemma isCompact_stripY (Y : ℝ) : IsCompact (stripY Y) := by
  have hc : IsClosed (stripY Y) :=
    (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  refine Metric.isCompact_of_isClosed_isBounded hc (isBounded_iff_forall_norm_le.2 ⟨1 / 2 + |Y|, ?_⟩)
  intro w hw
  have h1 : |w.im| ≤ |Y| := by
    rw [abs_of_pos (by linarith [hw.2.1] : (0 : ℝ) < w.im)]
    exact hw.2.2.trans (le_abs_self Y)
  exact (Complex.norm_le_abs_re_add_abs_im w).trans (add_le_add hw.1 h1)

/-- **P1.** The regularised diagonal is bounded on `ρ • (𝒟 ∩ {Im ≤ Y})`, uniformly in `0 < s ≤ 1/2`. -/
theorem diag_bound_trunc [NeZero M] (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (u : (ZMod M)ˣ) (ρ : SL(2, ℤ)) (Y : ℝ) :
    ∃ B : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 / 2 → ∀ τ : ℍ, τ ∈ 𝒟 → τ.im ≤ Y →
      ‖conj (KernelS.omegaS M 2 n (u : ZMod M) s ((ρ • τ : ℍ) : ℂ) (-conj ((ρ • τ : ℍ) : ℂ))) *
        (((ρ • τ : ℍ).im : ℂ) ^ 2)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_stripY Y).exists_bound_of_continuousOn
    (fun w hw => (continuousAt_Gd hn hnM u ρ (by linarith [hw.2.1] : (0 : ℝ) < w.im)).continuousWithinAt)
  refine ⟨B, fun s hs hs1 τ hτ hY => ?_⟩
  have hstrip := fd_subset_strip hτ
  have hmem : (τ : ℂ) ∈ stripY Y := ⟨hstrip.1, hstrip.2, hY⟩
  have hW : 0 < (-conj ((ρ • τ : ℍ) : ℂ)).im := by simpa using (ρ • τ).im_pos
  have h1 := norm_omegaS_smul_le hM hn hnM u hW ρ hs hs1 hstrip.2
  have h2 : Gd M n u ρ τ ≤ B := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB _ hmem)
  have e : Gd M n u ρ τ = Bk M n u ρ (-conj ((ρ • τ : ℍ) : ℂ)) * τ.im ^ (1 / 2 : ℝ) * (ρ • τ).im := by
    rw [Gd, ← coe_smul_eq_mobC]
    rfl
  have hy := (ρ • τ).im_pos
  calc ‖conj (KernelS.omegaS M 2 n (u : ZMod M) s ((ρ • τ : ℍ) : ℂ) (-conj ((ρ • τ : ℍ) : ℂ))) *
        (((ρ • τ : ℍ).im : ℂ) ^ 2)‖
      = (‖KernelS.omegaS M 2 n (u : ZMod M) s ((ρ • τ : ℍ) : ℂ) (-conj ((ρ • τ : ℍ) : ℂ))‖ *
          (ρ • τ).im) * (ρ • τ).im := by
        rw [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
        ring
    _ ≤ (Bk M n u ρ (-conj ((ρ • τ : ℍ) : ℂ)) * τ.im ^ (1 / 2 : ℝ)) * (ρ • τ).im :=
        mul_le_mul_of_nonneg_right h1 hy.le
    _ = Gd M n u ρ τ := e.symm
    _ ≤ B := h2

end RamanujanPetersson.EllW2


