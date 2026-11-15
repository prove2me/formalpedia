-- Prove2me | Definitions.Def_RPLib_S3_EllW2AS3
-- name    : RPLib_S3_EllW2AS3
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:01:12.041139+00:00
-- url     : https://prove2.me/theorems/2e1ecc5b-629f-4117-a521-2e0f20b3888d
-- title:
--   The Eichler-Selberg trace formula in weight two: `LS` as a lower integral, the weighted bound and the lattice sandwich
-- statement:
--   `LS` as a lower integral, the weighted bound and the lattice sandwich.
--
--   * **`LS_eq_toReal`**: `LS(s) = (∫⁻_𝒟 SNE).toReal` when that lower integral is finite (monotone convergence).
--   * `im_ofC`; **`B_bound`**: eventually `ofReal s · ∫⁻_𝒟 SNE (1 + √y) ≤ CB < ∞`.
--   * **`fd_eCnt_le`**: `π A ≤ y0 E + 6√y0 B` and `y0 E ≤ π A + 6√y0 B` (`0 < y0 ≤ 1`), from LC1.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2AS2

/-!
# S3-ES-Wt2 (O6, file AS3): `LS` as a lower integral, the weighted bound and the lattice sandwich

* **`LS_eq_toReal`**: `LS(s) = (∫⁻_𝒟 SNE).toReal` when that lower integral is finite (monotone convergence).
* `im_ofC`; **`B_bound`**: eventually `ofReal s · ∫⁻_𝒟 SNE (1 + √y) ≤ CB < ∞`.
* **`fd_eCnt_le`**: `π A ≤ y0 E + 6√y0 B` and `y0 E ≤ π A + 6√y0 B` (`0 < y0 ≤ 1`), from LC1.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ENNReal Modular Real

noncomputable section

namespace RamanujanPetersson.EllW2

open RamanujanPetersson.Kernel RamanujanPetersson.EllTerm

variable {M : ℕ} [NeZero M]

lemma measurableSet_fdY (Y : ℝ) : MeasurableSet (𝒟 ∩ {z : ℍ | z.im ≤ Y}) :=
  (ModularGroup.isClosed_fd.inter
    (isClosed_le UpperHalfPlane.continuous_im continuous_const)).measurableSet

theorem LS_eq_toReal {n : ℤ} (hn : 0 < n) (δ' : ZMod M) {s : ℝ} (hs : 0 < s)
    (hA : ∫⁻ z in 𝒟, SNE M n δ' s z ≠ ∞) :
    LS M n δ' s = (((∫⁻ z in 𝒟, SNE M n δ' s z).toReal : ℝ) : ℂ) := by
  have hlt : ∀ z, SNE M n δ' s z < ∞ := fun z =>
    lt_of_le_of_lt (SNE_le_CE hn δ' hs z) (CE_ne_top n s _).lt_top
  have hIS : ∀ Y : ℝ, IS M n δ' s Y =
      (((∫⁻ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SNE M n δ' s z).toReal : ℝ) : ℂ) := by
    intro Y
    unfold IS
    simp_rw [SNH_eq_toReal]
    rw [integral_complex_ofReal,
      integral_toReal (measurable_SNE n δ' s).aemeasurable (ae_of_all _ hlt)]
  have hmono : Monotone fun Y : ℝ => 𝒟 ∩ {z : ℍ | z.im ≤ Y} := fun a b hab =>
    inter_subset_inter_right _ fun z (hz : z.im ≤ a) => show z.im ≤ b from hz.trans hab
  have hU : volume.withDensity (SNE M n δ' s) (⋃ Y : ℝ, 𝒟 ∩ {z : ℍ | z.im ≤ Y}) =
      ∫⁻ z in 𝒟, SNE M n δ' s z := by
    have e : (⋃ Y : ℝ, 𝒟 ∩ {z : ℍ | z.im ≤ Y}) = 𝒟 := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨z.im, h, le_rfl⟩⟩
    rw [e, withDensity_apply _ ModularGroup.isClosed_fd.measurableSet]
  have hT := tendsto_measure_iUnion_atTop (μ := volume.withDensity (SNE M n δ' s)) hmono
  rw [hU] at hT
  have hT' : Tendsto (fun Y : ℝ => ∫⁻ z in 𝒟 ∩ {z : ℍ | z.im ≤ Y}, SNE M n δ' s z) atTop
      (𝓝 (∫⁻ z in 𝒟, SNE M n δ' s z)) :=
    hT.congr fun Y => withDensity_apply _ (measurableSet_fdY Y)
  have h2 := ((Complex.continuous_ofReal.tendsto _).comp (ENNReal.tendsto_toReal hA)).comp hT'
  have h3 : Tendsto (IS M n δ' s) atTop (𝓝 (((∫⁻ z in 𝒟, SNE M n δ' s z).toReal : ℝ) : ℂ)) :=
    h2.congr fun Y => (hIS Y).symm
  exact tendsto_nhds_unique (tendsto_IS hn δ' hs).1 h3

lemma im_ofC {x y : ℝ} (hy : 0 < y) : (ofComplex ((x : ℂ) + y * Complex.I)).im = y :=
  (re_im_ofC (p := (x, y)) hy).2

lemma rpow_neg_three_halves {y : ℝ} (hy : 0 < y) : y ^ (-(3 / 2) : ℝ) = (y ^ 2)⁻¹ * √y := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
  norm_num

theorem B_bound {n : ℤ} (hn : 0 < n) (hnM : Nat.Coprime n.natAbs M) {δ' : ZMod M}
    (hδ : IsUnit δ') :
    ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧ ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal s * ∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) ≤ CB := by
  obtain ⟨c1, c2, hc1, hc2, hev⟩ := exists_dom hn hnM hδ
  have hK := Kb_nonneg hc1 hc2 (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨∫⁻ y in Ici (1 / 2 : ℝ), ENNReal.ofReal (3 * Kb c1 c2 (1 / 2) * y ^ (-(3 / 2) : ℝ)), ?_, ?_⟩
  · rw [← setLIntegral_congr Ioi_ae_eq_Ici]
    have hi := (integrableOn_Ioi_rpow_of_lt (show (-(3 / 2) : ℝ) < -1 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul (3 * Kb c1 c2 (1 / 2))
    exact hi.lintegral_lt_top.ne
  filter_upwards [hev] with s hs
  have hm : Measurable fun z : ℍ => SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) :=
    (measurable_SNE n δ' s).mul (ENNReal.measurable_ofReal.comp (by fun_prop))
  calc ENNReal.ofReal s * ∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)
      ≤ ENNReal.ofReal s * ∫⁻ z in stripC (1 / 2), SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) := by
        gcongr ENNReal.ofReal s * ?_
        exact lintegral_mono_set fd_subset_stripC
    _ = ∫⁻ y in Ici (1 / 2 : ℝ), ENNReal.ofReal s * (ENNReal.ofReal ((y ^ 2)⁻¹) *
          ∫⁻ x in Icc (-(1 / 2 : ℝ)) (1 / 2), SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) *
            ENNReal.ofReal (1 + √(ofComplex ((x : ℂ) + y * Complex.I)).im)) := by
        rw [setLIntegral_stripC (by norm_num) hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y in Ici (1 / 2 : ℝ), ENNReal.ofReal (3 * Kb c1 c2 (1 / 2) * y ^ (-(3 / 2) : ℝ)) := by
        refine setLIntegral_mono' measurableSet_Ici fun y (hy : 1 / 2 ≤ y) => ?_
        have hy0 : 0 < y := by linarith
        have e0 : EqOn (fun x : ℝ => SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) *
              ENNReal.ofReal (1 + √(ofComplex ((x : ℂ) + y * Complex.I)).im))
            (fun x : ℝ => SNE M n δ' s (ofComplex ((x : ℂ) + y * Complex.I)) * ENNReal.ofReal (1 + √y))
            (Icc (-(1 / 2 : ℝ)) (1 / 2)) := fun x _ => by
          simp only
          rw [im_ofC hy0]
        rw [setLIntegral_congr_fun measurableSet_Icc e0, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_SNE_Icc_ZS hn δ' hs.1 hy0, ← ENNReal.ofReal_mul (ZS_nonneg hn δ' hs.1 hy0),
          ← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg y)), ← ENNReal.ofReal_mul hs.1.le]
        refine ENNReal.ofReal_le_ofReal ?_
        have hZ : s * ZS M n δ' s y ≤ Kb c1 c2 (1 / 2) :=
          (hs.2.2 y hy0).trans (Kb_anti hc1 hc2 (by norm_num) hy)
        have hsq : 1 + √y ≤ 3 * √y := by
          have h4 : √(1 / 4) ≤ √y := Real.sqrt_le_sqrt (by linarith)
          have h5 : √(1 / 4 : ℝ) = 1 / 2 := by
            rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          linarith
        rw [rpow_neg_three_halves hy0]
        have hy2 : 0 ≤ (y ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg y)
        calc s * ((y ^ 2)⁻¹ * (ZS M n δ' s y * (1 + √y)))
            = (y ^ 2)⁻¹ * ((s * ZS M n δ' s y) * (1 + √y)) := by ring
          _ ≤ (y ^ 2)⁻¹ * (Kb c1 c2 (1 / 2) * (3 * √y)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hZ hsq (by positivity) hK) hy2
          _ = 3 * Kb c1 c2 (1 / 2) * ((y ^ 2)⁻¹ * √y) := by ring

theorem fd_eCnt_le (n : ℤ) (δ' : ZMod M) (s : ℝ) {y0 : ℝ} (hy0 : 0 < y0) (hy01 : y0 ≤ 1) :
    ENNReal.ofReal π * ∫⁻ z in 𝒟, SNE M n δ' s z ≤
        ENNReal.ofReal y0 * (∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z) +
          ENNReal.ofReal (6 * √y0) * ∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) ∧
      ENNReal.ofReal y0 * ∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z ≤
        ENNReal.ofReal π * (∫⁻ z in 𝒟, SNE M n δ' s z) +
          ENNReal.ofReal (6 * √y0) * ∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) := by
  have hm : Measurable fun z : ℍ =>
      ENNReal.ofReal (6 * √y0) * (SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) :=
    measurable_const.mul ((measurable_SNE n δ' s).mul (ENNReal.measurable_ofReal.comp (by fun_prop)))
  have hfd := ModularGroup.isClosed_fd.measurableSet
  have hpt : ∀ z ∈ 𝒟, ENNReal.ofReal π ≤
        ENNReal.ofReal y0 * eCnt y0 z + ENNReal.ofReal (6 * √y0) * ENNReal.ofReal (1 + √z.im) ∧
      ENNReal.ofReal y0 * eCnt y0 z ≤
        ENNReal.ofReal π + ENNReal.ofReal (6 * √y0) * ENNReal.ofReal (1 + √z.im) := by
    intro z hz
    have hz2 : 1 / 2 ≤ z.im := (fd_subset_stripC hz).2.2
    have h := abs_le.1 (abs_y0_eCnt_sub_pi_le' hy0 hy01 z hz2)
    have he : ENNReal.ofReal (eCnt y0 z).toReal = eCnt y0 z := ENNReal.ofReal_toReal (eCnt_ne_top hy0 z)
    have hr0 : 0 ≤ (eCnt y0 z).toReal := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ 6 * √y0 * (1 + √z.im) := by positivity
    rw [← he, ← ENNReal.ofReal_mul hy0.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 6 * √y0)]
    constructor
    · rw [← ENNReal.ofReal_add (by positivity) hb0]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [← ENNReal.ofReal_add Real.pi_pos.le hb0]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  have eA : ∫⁻ z in 𝒟, ENNReal.ofReal π * SNE M n δ' s z = ENNReal.ofReal π * ∫⁻ z in 𝒟, SNE M n δ' s z :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have eE : ∫⁻ z in 𝒟, ENNReal.ofReal y0 * (SNE M n δ' s z * eCnt y0 z) =
      ENNReal.ofReal y0 * ∫⁻ z in 𝒟, SNE M n δ' s z * eCnt y0 z :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have eB : ∫⁻ z in 𝒟, ENNReal.ofReal (6 * √y0) * (SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) =
      ENNReal.ofReal (6 * √y0) * ∫⁻ z in 𝒟, SNE M n δ' s z * ENNReal.ofReal (1 + √z.im) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have eEB : ∫⁻ z in 𝒟, (ENNReal.ofReal y0 * (SNE M n δ' s z * eCnt y0 z) +
      ENNReal.ofReal (6 * √y0) * (SNE M n δ' s z * ENNReal.ofReal (1 + √z.im))) =
      (∫⁻ z in 𝒟, ENNReal.ofReal y0 * (SNE M n δ' s z * eCnt y0 z)) +
        ∫⁻ z in 𝒟, ENNReal.ofReal (6 * √y0) * (SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) :=
    lintegral_add_right _ hm
  have eAB : ∫⁻ z in 𝒟, (ENNReal.ofReal π * SNE M n δ' s z +
      ENNReal.ofReal (6 * √y0) * (SNE M n δ' s z * ENNReal.ofReal (1 + √z.im))) =
      (∫⁻ z in 𝒟, ENNReal.ofReal π * SNE M n δ' s z) +
        ∫⁻ z in 𝒟, ENNReal.ofReal (6 * √y0) * (SNE M n δ' s z * ENNReal.ofReal (1 + √z.im)) :=
    lintegral_add_right _ hm
  constructor
  · rw [← eA, ← eE, ← eB, ← eEB]
    refine setLIntegral_mono' hfd fun z hz => ?_
    calc ENNReal.ofReal π * SNE M n δ' s z
        ≤ (ENNReal.ofReal y0 * eCnt y0 z + ENNReal.ofReal (6 * √y0) * ENNReal.ofReal (1 + √z.im)) *
            SNE M n δ' s z := by
          gcongr ?_ * SNE M n δ' s z
          exact (hpt z hz).1
      _ = _ := by ring
  · rw [← eA, ← eE, ← eB, ← eAB]
    refine setLIntegral_mono' hfd fun z hz => ?_
    calc ENNReal.ofReal y0 * (SNE M n δ' s z * eCnt y0 z)
        = (ENNReal.ofReal y0 * eCnt y0 z) * SNE M n δ' s z := by ring
      _ ≤ (ENNReal.ofReal π + ENNReal.ofReal (6 * √y0) * ENNReal.ofReal (1 + √z.im)) *
            SNE M n δ' s z := by
          gcongr ?_ * SNE M n δ' s z
          exact (hpt z hz).2
      _ = _ := by ring

end RamanujanPetersson.EllW2


