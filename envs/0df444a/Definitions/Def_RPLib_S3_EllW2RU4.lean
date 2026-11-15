-- Prove2me | Definitions.Def_RPLib_S3_EllW2RU4
-- name    : RPLib_S3_EllW2RU4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T14:26:31.612697+00:00
-- url     : https://prove2.me/theorems/9728d7c8-8c5f-4847-bcd8-0901d3f0edf5
-- title:
--   The Eichler-Selberg trace formula in weight two: lower integrals on `ℍ` as integrals over `ℝ²`, and the strip
-- statement:
--   Lower integrals on `ℍ` as integrals over `ℝ²`, and the strip.
--
--   * `dens_eq`: the hyperbolic density is `ofReal ((im z)²)⁻¹`.
--   * **`setLIntegral_H_eq`** (`f` measurable, `coe '' S = e⁻¹' R`):
--     `∫⁻_S f = ∫⁻_{(x,y) ∈ R} ofReal (y²)⁻¹ · f (x + iy)`.
--   * `stripP Y = [-1/2, 1/2) × [Y, ∞)`, `coe_image_stripH` (`0 < Y`), `measurableSet_stripP`.
--   * **`setLIntegral_stripH`** (`0 < Y`, `f` measurable):
--     `∫⁻_{S_Y} f = ∫⁻_{y ≥ Y} ofReal (y²)⁻¹ · ∫⁻_{x ∈ [-1/2,1/2)} f (x + iy)`.
--   * `stripC Y = {|re| ≤ 1/2, Y ≤ im}`, `fd_subset_stripC` (`𝒟 ⊆ stripC (1/2)`), **`setLIntegral_stripC`**.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; H. Iwaniec, Spectral Methods of Automorphic Forms, 2nd ed., Graduate Studies in Mathematics 53, AMS 2002, Chapter 2

import Mathlib
import Definitions.Def_RPLib_S3_EllW2RU3
import Definitions.Def_RPLib_S3_EllW2Z4
import Definitions.Def_RPLib_S3_EllW2P7

/-!
# S3-ES-Wt2 (RU4): lower integrals on `ℍ` as integrals over `ℝ²`, and the strip

* `dens_eq`: the hyperbolic density is `ofReal ((im z)²)⁻¹`.
* **`setLIntegral_H_eq`** (`f` measurable, `coe '' S = e⁻¹' R`):
  `∫⁻_S f = ∫⁻_{(x,y) ∈ R} ofReal (y²)⁻¹ · f (x + iy)`.
* `stripP Y = [-1/2, 1/2) × [Y, ∞)`, `coe_image_stripH` (`0 < Y`), `measurableSet_stripP`.
* **`setLIntegral_stripH`** (`0 < Y`, `f` measurable):
  `∫⁻_{S_Y} f = ∫⁻_{y ≥ Y} ofReal (y²)⁻¹ · ∫⁻_{x ∈ [-1/2,1/2)} f (x + iy)`.
* `stripC Y = {|re| ≤ 1/2, Y ≤ im}`, `fd_subset_stripC` (`𝒟 ⊆ stripC (1/2)`), **`setLIntegral_stripC`**.
-/

set_option autoImplicit false

open MeasureTheory UpperHalfPlane ModularGroup Function
open scoped MatrixGroups ENNReal NNReal Modular

noncomputable section

namespace RamanujanPetersson.EllW2

lemma dens_eq (z : ℍ) :
    (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (((z : ℂ).im ^ 2)⁻¹) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [one_div, inv_pow]

/-- **Lower integrals on `ℍ` in `(x, y)` coordinates.** -/
theorem setLIntegral_H_eq {S : Set ℍ} (hS : MeasurableSet S) {R : Set (ℝ × ℝ)}
    (hSR : UpperHalfPlane.coe '' S = Complex.measurableEquivRealProd ⁻¹' R) {f : ℍ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z in S, f z =
      ∫⁻ p in R, ENNReal.ofReal ((p.2 ^ 2)⁻¹) * f (ofComplex ((p.1 : ℂ) + p.2 * Complex.I)) := by
  have hP : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hd : Measurable fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
    Bergman.measurable_density.coe_nnreal_ennreal
  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ((w.im ^ 2)⁻¹) * f (ofComplex w) with hG
  rw [volume_def, setLIntegral_withDensity_eq_setLIntegral_mul _ hd hf hS]
  have e1 : ∫⁻ z in S, ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞)) * f) z
      ∂(volume.comap UpperHalfPlane.coe) = ∫⁻ z in S, G (z : ℂ) ∂(volume.comap UpperHalfPlane.coe) := by
    refine lintegral_congr fun z => ?_
    simp only [Pi.mul_apply, hG]
    rw [dens_eq, ofComplex_apply]
  rw [e1, hP.setLIntegral_comp_emb measurableEmbedding_coe,
    Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _), hSR,
    ← Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding]
  refine setLIntegral_congr_fun (Complex.measurableEquivRealProd.measurable
    (by
      have h := measurableEmbedding_coe.measurableSet_image.2 hS
      rw [hSR] at h
      exact (Complex.measurableEquivRealProd.measurableSet_preimage).1 h)) fun w _ => ?_
  simp only [hG, Complex.measurableEquivRealProd_apply, Complex.re_add_im]

/-- The half-open strip `[-1/2, 1/2) × [Y, ∞)` in `ℝ²`. -/
def stripP (Y : ℝ) : Set (ℝ × ℝ) := Set.Ico (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici Y

lemma measurableSet_stripP (Y : ℝ) : MeasurableSet (stripP Y) :=
  measurableSet_Ico.prod measurableSet_Ici

lemma coe_image_stripH {Y : ℝ} (hY : 0 < Y) :
    UpperHalfPlane.coe '' stripH Y = Complex.measurableEquivRealProd ⁻¹' stripP Y := by
  ext w
  simp only [Set.mem_image, Set.mem_preimage, Complex.measurableEquivRealProd_apply, stripP,
    Set.mem_prod, Set.mem_Ico, Set.mem_Ici]
  constructor
  · rintro ⟨z, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hw : 0 < w.im := lt_of_lt_of_le hY h3
    exact ⟨UpperHalfPlane.mk w hw, ⟨h1, h2, h3⟩, rfl⟩

/-- **The strip in `(x, y)` coordinates** (Tonelli). -/
theorem setLIntegral_stripH {Y : ℝ} (hY : 0 < Y) {f : ℍ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in stripH Y, f z = ∫⁻ y in Set.Ici Y, ENNReal.ofReal ((y ^ 2)⁻¹) *
      ∫⁻ x in Set.Ico (-(1 / 2 : ℝ)) (1 / 2), f (ofComplex ((x : ℂ) + y * Complex.I)) := by
  rw [setLIntegral_H_eq (measurableSet_stripH Y) (coe_image_stripH hY) hf]
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.2 ^ 2)⁻¹) * f (ofComplex ((p.1 : ℂ) + p.2 * Complex.I)) := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hf.comp ?_)
    exact measurable_ofComplex.comp (by fun_prop)
  have hprod : (volume.restrict (stripP Y) : Measure (ℝ × ℝ)) =
      (volume.restrict (Set.Ico (-(1 / 2 : ℝ)) (1 / 2))).prod (volume.restrict (Set.Ici Y)) := by
    rw [stripP, Measure.prod_restrict]; rfl
  rw [hprod, lintegral_prod_symm _ hm.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact lintegral_const_mul' (ENNReal.ofReal ((y ^ 2)⁻¹))
    (fun x : ℝ => f (ofComplex ((x : ℂ) + y * Complex.I))) ENNReal.ofReal_ne_top

/-- The closed strip `{|re| ≤ 1/2, Y ≤ im}`. -/
def stripC (Y : ℝ) : Set ℍ := {w | -(1 / 2 : ℝ) ≤ w.re ∧ w.re ≤ 1 / 2 ∧ Y ≤ w.im}

lemma measurableSet_stripC (Y : ℝ) : MeasurableSet (stripC Y) := by
  have hre : Measurable fun w : ℍ => w.re := UpperHalfPlane.continuous_re.measurable
  have him : Measurable fun w : ℍ => w.im := UpperHalfPlane.continuous_im.measurable
  exact (measurableSet_le measurable_const hre).inter
    ((measurableSet_le hre measurable_const).inter (measurableSet_le measurable_const him))

lemma fd_subset_stripC : 𝒟 ⊆ stripC (1 / 2) := by
  intro z hz
  have h2 : |z.re| ≤ 1 / 2 := hz.2
  have h3 : 3 ≤ 4 * z.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hp := z.im_pos
  refine ⟨(abs_le.1 h2).1, (abs_le.1 h2).2, ?_⟩
  nlinarith

lemma coe_image_stripC {Y : ℝ} (hY : 0 < Y) :
    UpperHalfPlane.coe '' stripC Y = Complex.measurableEquivRealProd ⁻¹'
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici Y) := by
  ext w
  simp only [Set.mem_image, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
    Set.mem_prod, Set.mem_Icc, Set.mem_Ici]
  constructor
  · rintro ⟨z, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hw : 0 < w.im := lt_of_lt_of_le hY h3
    exact ⟨UpperHalfPlane.mk w hw, ⟨h1, h2, h3⟩, rfl⟩

/-- **The closed strip in `(x, y)` coordinates.** -/
theorem setLIntegral_stripC {Y : ℝ} (hY : 0 < Y) {f : ℍ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in stripC Y, f z = ∫⁻ y in Set.Ici Y, ENNReal.ofReal ((y ^ 2)⁻¹) *
      ∫⁻ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), f (ofComplex ((x : ℂ) + y * Complex.I)) := by
  rw [setLIntegral_H_eq (measurableSet_stripC Y) (coe_image_stripC hY) hf]
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.2 ^ 2)⁻¹) * f (ofComplex ((p.1 : ℂ) + p.2 * Complex.I)) := by
    refine (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hf.comp ?_)
    exact measurable_ofComplex.comp (by fun_prop)
  have hprod : (volume.restrict (Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Set.Ici Y) : Measure (ℝ × ℝ)) =
      (volume.restrict (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))).prod (volume.restrict (Set.Ici Y)) := by
    rw [Measure.prod_restrict]; rfl
  rw [hprod, lintegral_prod_symm _ hm.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact lintegral_const_mul' (ENNReal.ofReal ((y ^ 2)⁻¹))
    (fun x : ℝ => f (ofComplex ((x : ℂ) + y * Complex.I))) ENNReal.ofReal_ne_top

end RamanujanPetersson.EllW2


