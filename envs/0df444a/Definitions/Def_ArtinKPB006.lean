-- Prove2me | Definitions.Def_ArtinKPB006
-- name    : ArtinKPB006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:18:46.152025+00:00
-- url     : https://prove2.me/theorems/d23eb7e7-8bef-4987-8e85-2fd8072c737c
-- title:
--   Definitions bundle ArtinKPB006 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 99 declarations of that development: 40 definitions, 2 inductive types or structures, 6 instances and 51 theorems. The definitions and types are `ArtinKP.X.E3`, `ArtinKP.X.H3.coe`, `ArtinKP.X.H3.vol`, `ArtinKP.X.Iso1`, `ArtinKP.X.IsoHalf`, `ArtinKP.X.Jmap`, `ArtinKP.X.Lk`, `ArtinKP.X.Ls`, `ArtinKP.X.Lw`, `ArtinKP.X.X.Smooth`, `ArtinKP.X.X.avg`, `ArtinKP.X.X.core`, `ArtinKP.X.X.lap`, `ArtinKP.X.X.vol`, `ArtinKP.X.acoef`, `ArtinKP.X.actE`, `ArtinKP.X.amb`, `ArtinKP.X.bvec`, `ArtinKP.X.cco`, `ArtinKP.X.dens`, `ArtinKP.X.e1`, `ArtinKP.X.gamE`, `ArtinKP.X.gin`, `ArtinKP.X.inv3`, `ArtinKP.X.inv3Deriv`, `ArtinKP.X.iso1Submonoid`, `ArtinKP.X.lapE`, `ArtinKP.X.mC`, `ArtinKP.X.mu1`, `ArtinKP.X.muE`, `ArtinKP.X.nMat`, `ArtinKP.X.nsq`, `ArtinKP.X.pd`, `ArtinKP.X.phi`, `ArtinKP.X.reflEquiv`, `ArtinKP.X.rho`, `ArtinKP.X.rho1`, `ArtinKP.X.rhoJ`, `ArtinKP.X.sJ`, `ArtinKP.X.transEquiv` and 2 more.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X2_Calc`, `KP.X2_Chart`, `KP.X2_Core`, `KP.X2_H1`, `KP.X2_Isom`, `KP.X_H3`, `KP.X_Meas`, `KP.X_Space`.
--
--   **Imports.** It imports the bundle `ArtinKPB005` of this split; the published statement `ArtinKP.X.X.summable_comp_smul_of_hasCompactSupport`.
--
--   **Imported by** (directly, in this split): the bundles `ArtinKPB007`, `ArtinKPB008`, `ArtinKPB013` and `ArtinKPB014`; the statements `ArtinKP.X.X.lap_mem_core` and `ArtinKP.X.X.smooth_of_mem_core`; the proofs of `ArtinKP.X.X.lap_mem_core` and `ArtinKP.X.X.smooth_of_mem_core`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB005
import Theorems.Thm_ArtinKP_X_X_summable_comp_smul_of_hasCompactSupport

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

namespace H3

instance instMeasurableSpace : MeasurableSpace H3 := inferInstanceAs (MeasurableSpace {p : ℂ × ℝ // 0 < p.2})
instance instBorelSpace : BorelSpace H3 := inferInstanceAs (BorelSpace {p : ℂ × ℝ // 0 < p.2})
instance instSecondCountableTopology : SecondCountableTopology H3 :=
  inferInstanceAs (SecondCountableTopology {p : ℂ × ℝ // 0 < p.2})

/-- The underlying point of `ℂ × ℝ`. -/
def coe (P : H3) : ℂ × ℝ := P.1

lemma range_coe : Set.range coe = {p : ℂ × ℝ | 0 < p.2} := Subtype.range_coe
lemma measurableEmbedding_coe : MeasurableEmbedding coe :=
  MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const measurable_snd)

end H3

open H3

lemma smul_x (g : SL(2, ℂ)) (P : H3) :
    (g • P).x = rowNum (g 0 0) (g 0 1) (g 1 0) (g 1 1) P / (den g P : ℂ) := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Meas
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x
/-! # WP-X, file 2: the invariant measure `dx dv / v³` on `H3`

`H3.vol` is the comap to `H3` of `(volume.restrict {v > 0}).withDensity v⁻³` on `ℂ × ℝ`.
Invariance under `SL(2,ℂ)` is proved on the generators `n(b)` and `w` (the Weyl element acts by
the Euclidean inversion followed by `x ↦ -conj x`), and `SL(2,ℂ)` is generated by them.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set

namespace ArtinKP.X

noncomputable section

/-- The open upper half of `ℂ × ℝ`. -/
def upper : Set (ℂ × ℝ) := {p | 0 < p.2}

/-- The density `v⁻³`. -/
def dens (p : ℂ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((p.2 ^ 3)⁻¹)

/-- The measure `dx dv / v³` on the ambient space `ℂ × ℝ`, concentrated on the upper half. -/
def amb : Measure (ℂ × ℝ) := (volume.restrict upper).withDensity dens

lemma measurableSet_upper : MeasurableSet upper := measurableSet_lt measurable_const measurable_snd

instance instSigmaFiniteProdComplexRealAmb : SigmaFinite amb := by unfold amb dens; infer_instance

lemma amb_ae_upper : ∀ᵐ p ∂amb, p ∈ upper :=
  (ae_restrict_mem measurableSet_upper).filter_mono
    (withDensity_absolutelyContinuous (volume.restrict upper) dens).ae_le

lemma amb_apply {s : Set (ℂ × ℝ)} (hs : MeasurableSet s) :
    amb s = ∫⁻ p in upper, s.indicator dens p := by
  unfold amb
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]

/-- A volume-preserving measurable equivalence that keeps the height preserves `amb`. -/
lemma amb_map_of_measurePreserving (e : ℂ × ℝ ≃ᵐ ℂ × ℝ)
    (he : MeasurePreserving e volume volume) (hv : ∀ p, (e p).2 = p.2) :
    Measure.map e amb = amb := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, amb_apply hs, amb_apply (e.measurable hs)]
  have h1 : ∀ p, (upper.indicator (s.indicator dens)) (e p) =
      upper.indicator ((e ⁻¹' s).indicator dens) p := by
    intro p
    have hd : dens (e p) = dens p := by simp [dens, hv]
    have hu : e p ∈ upper ↔ p ∈ upper := by simp [upper, hv]
    by_cases hp : p ∈ upper
    · rw [indicator_of_mem (hu.mpr hp), indicator_of_mem hp]
      by_cases hps : e p ∈ s
      · rw [indicator_of_mem hps, indicator_of_mem (show p ∈ e ⁻¹' s from hps), hd]
      · rw [indicator_of_notMem hps, indicator_of_notMem (show p ∉ e ⁻¹' s from hps)]
    · rw [indicator_of_notMem (fun h => hp (hu.mp h)), indicator_of_notMem hp]
  rw [← lintegral_indicator measurableSet_upper, ← lintegral_indicator measurableSet_upper]
  calc ∫⁻ p, upper.indicator ((e ⁻¹' s).indicator dens) p
      = ∫⁻ p, upper.indicator (s.indicator dens) (e p) := lintegral_congr fun p => (h1 p).symm
    _ = ∫⁻ p, upper.indicator (s.indicator dens) p :=
        he.lintegral_comp_emb e.measurableEmbedding _

theorem instIsAddHaarMeasureProdComplexRealVolume_solutions :
    (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure

/-- Jacobian criterion for preserving `amb`. -/
lemma amb_map_of_jacobian (f : ℂ × ℝ → ℂ × ℝ) (df : ℂ × ℝ → (ℂ × ℝ) →L[ℝ] (ℂ × ℝ))
    (hf : Measurable f) (hderiv : ∀ p ∈ upper, HasFDerivAt f (df p) p)
    (hinj : InjOn f upper) (himage : f '' upper = upper)
    (hjac : ∀ p ∈ upper, ENNReal.ofReal |(df p).det| * dens (f p) = dens p) :
    Measure.map f amb = amb := by
  haveI _iHCR := ArtinKP.X.instIsAddHaarMeasureProdComplexRealVolume_solutions
  ext s hs
  rw [Measure.map_apply hf hs, amb_apply hs, amb_apply (hf hs)]
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    measurableSet_upper (fun p hp => (hderiv p hp).hasFDerivWithinAt) hinj (s.indicator dens)
  rw [himage] at hc
  rw [hc]
  apply setLIntegral_congr_fun measurableSet_upper
  intro p hp
  change (f ⁻¹' s).indicator dens p = ENNReal.ofReal |(df p).det| * s.indicator dens (f p)
  by_cases hsfp : f p ∈ s
  · rw [indicator_of_mem hsfp, indicator_of_mem (show p ∈ f ⁻¹' s from hsfp)]
    exact (hjac p hp).symm
  · rw [indicator_of_notMem hsfp, indicator_of_notMem (show p ∉ f ⁻¹' s from hsfp), mul_zero]

/-! ### The Euclidean inversion -/

/-- The `L²` model of `ℂ × ℝ`. -/
abbrev E3 : Type := WithLp 2 (ℂ × ℝ)

/-- The identification of `ℂ × ℝ` with its `L²` model. -/
def phi : E3 ≃L[ℝ] ℂ × ℝ := WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℝ

/-- The inversion in the unit sphere, on `ℂ × ℝ`. -/
def inv3 (p : ℂ × ℝ) : ℂ × ℝ := phi (EuclideanGeometry.inversion 0 1 (phi.symm p))

/-- `|x|² + v²`. -/
def nsq (p : ℂ × ℝ) : ℝ := Complex.normSq p.1 + p.2 ^ 2

lemma norm_phi_symm_sq (p : ℂ × ℝ) : ‖phi.symm p‖ ^ 2 = nsq p := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [phi, nsq, Complex.sq_norm]

lemma nsq_pos {p : ℂ × ℝ} (hp : p ∈ upper) : 0 < nsq p := by
  have : 0 < p.2 ^ 2 := pow_pos hp 2
  have := Complex.normSq_nonneg p.1
  unfold nsq; linarith

lemma phi_symm_ne_zero {p : ℂ × ℝ} (hp : p ∈ upper) : phi.symm p ≠ 0 := by
  intro h
  have := norm_phi_symm_sq p
  rw [h, norm_zero] at this
  have := nsq_pos hp
  nlinarith

lemma inv3_apply (p : ℂ × ℝ) : inv3 p = ((nsq p)⁻¹ : ℝ) • p := by
  unfold inv3
  simp only [EuclideanGeometry.inversion, dist_zero_right, vsub_eq_sub, sub_zero, vadd_eq_add,
    add_zero, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  rw [div_pow, one_pow, norm_phi_symm_sq, one_div]

lemma inv3_snd (p : ℂ × ℝ) : (inv3 p).2 = p.2 / nsq p := by
  rw [inv3_apply]; simp [div_eq_inv_mul]

lemma inv3_fst (p : ℂ × ℝ) : (inv3 p).1 = p.1 / (nsq p : ℂ) := by
  rw [inv3_apply]; simp [div_eq_inv_mul]

lemma inv3_mem {p : ℂ × ℝ} (hp : p ∈ upper) : inv3 p ∈ upper := by
  change 0 < (inv3 p).2
  rw [inv3_snd]
  exact div_pos hp (nsq_pos hp)

lemma inv3_inv3 (p : ℂ × ℝ) : inv3 (inv3 p) = p := by
  unfold inv3
  rw [ContinuousLinearEquiv.symm_apply_apply,
    EuclideanGeometry.inversion_inversion 0 (by norm_num : (1 : ℝ) ≠ 0),
    ContinuousLinearEquiv.apply_symm_apply]

lemma measurable_inv3 : Measurable inv3 := by
  have : inv3 = fun p => ((nsq p)⁻¹ : ℝ) • p := funext inv3_apply
  rw [this]
  unfold nsq
  have h1 : Measurable fun p : ℂ × ℝ => Complex.normSq p.1 :=
    Complex.continuous_normSq.measurable.comp measurable_fst
  fun_prop

/-- The derivative of the inversion. -/
def inv3Deriv (p : ℂ × ℝ) : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) :=
  (phi : E3 →L[ℝ] ℂ × ℝ).comp
    (((1 / ‖phi.symm p‖) ^ 2 • (((ℝ ∙ phi.symm p)ᗮ).reflection : E3 →L[ℝ] E3)).comp
      (phi.symm : (ℂ × ℝ) →L[ℝ] E3))

lemma hasFDerivAt_inv3 {p : ℂ × ℝ} (hp : p ∈ upper) : HasFDerivAt inv3 (inv3Deriv p) p := by
  have h1 : HasFDerivAt (EuclideanGeometry.inversion (0 : E3) 1)
      ((1 / ‖phi.symm p‖) ^ 2 • (((ℝ ∙ phi.symm p)ᗮ).reflection : E3 →L[ℝ] E3)) (phi.symm p) := by
    simpa [dist_zero_right] using
      (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E3)) (R := (1 : ℝ))
        (phi_symm_ne_zero hp))
  exact (phi : E3 →L[ℝ] ℂ × ℝ).hasFDerivAt.comp p (h1.comp p phi.symm.hasFDerivAt)

lemma finrank_E3 : Module.finrank ℝ E3 = 3 := by
  rw [phi.toLinearEquiv.finrank_eq, Module.finrank_prod, Complex.finrank_real_complex,
    Module.finrank_self]

lemma abs_det_inv3Deriv (p : ℂ × ℝ) : |(inv3Deriv p).det| = ((1 / ‖phi.symm p‖) ^ 2) ^ 3 := by
  have h : (inv3Deriv p).det = LinearMap.det
      ((1 / ‖phi.symm p‖) ^ 2 • ((ℝ ∙ phi.symm p)ᗮ).reflection.toLinearMap) := by
    change LinearMap.det ((phi.toLinearEquiv : E3 →ₗ[ℝ] ℂ × ℝ) ∘ₗ
      ((1 / ‖phi.symm p‖) ^ 2 • ((ℝ ∙ phi.symm p)ᗮ).reflection.toLinearMap) ∘ₗ
      (phi.toLinearEquiv.symm : (ℂ × ℝ) →ₗ[ℝ] E3)) = _
    rw [LinearMap.det_conj]
  rw [h, LinearMap.det_smul, Submodule.det_reflection, finrank_E3]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  rw [abs_of_nonneg (one_div_nonneg.mpr (norm_nonneg _))]

lemma amb_map_inv3 : Measure.map inv3 amb = amb := by
  apply amb_map_of_jacobian inv3 inv3Deriv measurable_inv3
  · exact fun p hp => hasFDerivAt_inv3 hp
  · exact fun p _ q _ h => by rw [← inv3_inv3 p, h, inv3_inv3]
  · apply Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact inv3_mem hq
    · intro p hp
      exact ⟨inv3 p, inv3_mem hp, inv3_inv3 p⟩
  · intro p hp
    rw [abs_det_inv3Deriv, dens, dens, inv3_snd, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hn := (nsq_pos hp).ne'
    have hv : p.2 ≠ 0 := (show 0 < p.2 from hp).ne'
    rw [one_div, inv_pow, norm_phi_symm_sq]
    field_simp

/-! ### The measure on `H3` -/

/-- The invariant measure `dx dv / v³` on `H3`. -/
def H3.vol : Measure H3 := amb.comap H3.coe

lemma map_val_vol : Measure.map H3.coe H3.vol = amb := by
  unfold H3.vol
  rw [H3.measurableEmbedding_coe.map_comap]
  have : range H3.coe = upper := H3.range_coe
  rw [this]
  exact Measure.restrict_eq_self_of_ae_mem amb_ae_upper

instance instSigmaFiniteH3Vol : SigmaFinite H3.vol :=
  SigmaFinite.of_map H3.vol H3.measurableEmbedding_coe.measurable.aemeasurable
    (by rw [map_val_vol]; infer_instance)

/-- Transport of invariance from the ambient space to `H3`. -/
lemma vol_map_of_amb {f : ℂ × ℝ → ℂ × ℝ} (hf : Measurable f) (hfa : Measure.map f amb = amb)
    {g : H3 → H3} (hg : Measurable g) (hgf : ∀ P : H3, (g P).coe = f P.coe) :
    Measure.map g H3.vol = H3.vol := by
  have h1 : Measure.map H3.coe (Measure.map g H3.vol) = amb := by
    rw [Measure.map_map H3.measurableEmbedding_coe.measurable hg]
    have : H3.coe ∘ g = f ∘ H3.coe := funext hgf
    rw [this, ← Measure.map_map hf H3.measurableEmbedding_coe.measurable, map_val_vol, hfa]
  rw [← H3.measurableEmbedding_coe.comap_map (Measure.map g H3.vol), h1]
  rfl

/-! ### Regularity of the action -/

lemma continuous_den (g : SL(2, ℂ)) : Continuous (den g) := by
  unfold den H3.rowDen
  have := H3.continuous_x
  have := H3.continuous_v
  have h3 : Continuous Complex.normSq := Complex.continuous_normSq
  fun_prop

lemma continuous_mob (g : SL(2, ℂ)) : Continuous (fun P : H3 => g • P) := by
  have hx := H3.continuous_x
  have hv := H3.continuous_v
  have hd := continuous_den g
  have hconj : Continuous (conj : ℂ → ℂ) := Complex.continuous_conj
  have hne : ∀ P : H3, (den g P : ℂ) ≠ 0 := fun P => by exact_mod_cast (den_pos g P).ne'
  refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
  · refine Continuous.div ?_ (Complex.continuous_ofReal.comp hd) hne
    unfold H3.rowNum
    have h1 : Continuous fun P : H3 => conj (g 1 0 * P.x + g 1 1) :=
      hconj.comp (by fun_prop)
    have h2 : Continuous fun P : H3 => ((P.v : ℝ) : ℂ) := Complex.continuous_ofReal.comp hv
    fun_prop
  · exact hv.div hd fun P => (den_pos g P).ne'

instance instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 : MeasurableConstSMul (SL(2, ℂ)) H3 := ⟨fun g => (continuous_mob g).measurable⟩

/-! ### Generators -/

/-- The translation `n(b)`. -/
def nMat (b : ℂ) : SL(2, ℂ) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

lemma nMat_coe (b : ℂ) : (nMat b : Matrix (Fin 2) (Fin 2) ℂ) = !![1, b; 0, 1] := rfl
lemma wMat_inv_coe : ((wMat⁻¹ : SL(2, ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, wMat_coe, Matrix.adjugate_fin_two]
  simp

lemma nMat_smul (b : ℂ) (P : H3) : (nMat b • P).coe = (P.x + b, P.v) := by
  have hd : den (nMat b) P = 1 := by simp [den, H3.rowDen, nMat]
  apply Prod.ext
  · change (nMat b • P).x = _
    rw [smul_x, hd]
    simp [H3.rowNum, nMat]
  · change (nMat b • P).v = _
    rw [smul_v, hd, div_one]

lemma wMat_smul (P : H3) :
    (wMat • P).coe = (-conj (inv3 P.coe).1, (inv3 P.coe).2) := by
  have hd : den wMat P = nsq P.coe := by
    simp [den, H3.rowDen, wMat, nsq]; rfl
  apply Prod.ext
  · change (wMat • P).x = _
    rw [smul_x, hd, inv3_fst]
    simp only [H3.rowNum, wMat, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp only [map_div₀, Complex.conj_ofReal]
    change _ = -(conj P.x / _)
    ring_nf
  · change (wMat • P).v = _
    rw [smul_v, hd, inv3_snd]; rfl

/-- Translation by `b` in the horizontal coordinate, as a measurable equivalence. -/
def transEquiv (b : ℂ) : ℂ × ℝ ≃ᵐ ℂ × ℝ :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.addRight b) (MeasurableEquiv.refl ℝ)

/-- `(x, v) ↦ (-conj x, v)` as a measurable equivalence. -/
def reflEquiv : ℂ × ℝ ≃ᵐ ℂ × ℝ :=
  MeasurableEquiv.prodCongr
    (Complex.conjLIE.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.neg ℂ))
    (MeasurableEquiv.refl ℝ)

lemma vol_map_nMat (b : ℂ) : Measure.map (fun P : H3 => nMat b • P) H3.vol = H3.vol := by
  refine vol_map_of_amb (transEquiv b).measurable ?_ (measurable_const_smul _)
    (fun P => nMat_smul b P)
  refine amb_map_of_measurePreserving _ ?_ (fun p => rfl)
  exact (measurePreserving_add_right volume b).prod (MeasurePreserving.id volume)

lemma vol_map_wMat : Measure.map (fun P : H3 => wMat • P) H3.vol = H3.vol := by
  have hf : Measurable (reflEquiv ∘ inv3) := reflEquiv.measurable.comp measurable_inv3
  refine vol_map_of_amb hf ?_ (measurable_const_smul _) (fun P => wMat_smul P)
  rw [← Measure.map_map reflEquiv.measurable measurable_inv3, amb_map_inv3]
  refine amb_map_of_measurePreserving _ ?_ (fun p => rfl)
  refine MeasurePreserving.prod ?_ (MeasurePreserving.id volume)
  exact (Complex.conjLIE.measurePreserving).trans (Measure.measurePreserving_neg volume)

/-- The subgroup of elements preserving the measure. -/
def volStab : Subgroup (SL(2, ℂ)) where
  carrier := {g | Measure.map (fun P : H3 => g • P) H3.vol = H3.vol}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change Measure.map (fun P : H3 => (g * h) • P) H3.vol = H3.vol
    have : (fun P : H3 => (g * h) • P) = (fun P => g • P) ∘ (fun P => h • P) := by
      funext P; exact mul_smul g h P
    rw [this, ← Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
    rw [show Measure.map (fun P : H3 => h • P) H3.vol = H3.vol from hh]
    exact hg
  inv_mem' := by
    intro g hg
    change Measure.map (fun P : H3 => g⁻¹ • P) H3.vol = H3.vol
    have hg' : Measure.map (fun P : H3 => g • P) H3.vol = H3.vol := hg
    conv_lhs => rw [← hg']
    rw [Measure.map_map (measurable_const_smul g⁻¹) (measurable_const_smul g)]
    have : (fun P : H3 => g⁻¹ • P) ∘ (fun P => g • P) = id := by
      funext P; simp
    rw [this, Measure.map_id]

lemma bruhat_of_ne {g : SL(2, ℂ)} (hc : g 1 0 ≠ 0) :
    g = nMat (g 0 0 / g 1 0) * nMat (-1 / g 1 0) * wMat⁻¹ * nMat (-g 1 0) * wMat *
      nMat (-1 / g 1 0) * nMat (g 1 1 / g 1 0) := by
  have hd := det_eq g
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, nMat_coe, wMat_coe, wMat_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    first | ring1 | linear_combination hd | linear_combination -hd

theorem mem_volStab (g : SL(2, ℂ)) : g ∈ volStab := by
  have hn : ∀ b, nMat b ∈ volStab := vol_map_nMat
  have hw : wMat ∈ volStab := vol_map_wMat
  have key : ∀ g : SL(2, ℂ), g 1 0 ≠ 0 → g ∈ volStab := by
    intro g hc
    rw [bruhat_of_ne hc]
    exact volStab.mul_mem (volStab.mul_mem (volStab.mul_mem (volStab.mul_mem (volStab.mul_mem
      (volStab.mul_mem (hn _) (hn _)) (volStab.inv_mem hw)) (hn _)) hw) (hn _)) (hn _)
  by_cases hc : g 1 0 = 0
  · have h1 : (g * wMat) 1 0 ≠ 0 := by
      have hd := det_eq g
      have : (g * wMat) 1 0 = g 1 1 := by
        rw [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this]
      intro h
      rw [hc, h] at hd
      simp at hd
    have : g = (g * wMat) * wMat⁻¹ := by group
    rw [this]
    exact volStab.mul_mem (key _ h1) (volStab.inv_mem hw)
  · exact key g hc

/-- **Invariance of the hyperbolic measure.** -/
theorem vol_map_smul (g : SL(2, ℂ)) : Measure.map (fun P : H3 => g • P) H3.vol = H3.vol :=
  mem_volStab g

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

variable {F}

/-! ### Topology and measure -/

variable (F) in
/-- The invariant measure `∏_w dx_w dv_w / v_w³` on `X`. -/
def X.vol : Measure (X F) := Measure.pi fun _ => H3.vol

/-- `G∞` preserves the measure. -/
theorem measurePreserving_Ginf_smul (g : Ginf F) :
    MeasurePreserving (fun P : X F => g • P) (X.vol F) (X.vol F) :=
  measurePreserving_pi (fun _ => H3.vol) (fun _ => H3.vol)
    (fun w => ⟨measurable_const_smul (g w), vol_map_smul (g w)⟩)

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

/-! ### One factor -/

/-- The density of `H3.vol` in the chart: `exp (-2t)`. -/
def rho1 (p : E1) : ℝ := Real.exp (-2 * p.2)

/-- `H3.vol` in the chart. -/
def mu1 : Measure E1 := volume.withDensity fun p => ENNReal.ofReal (rho1 p)

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

@[simp] lemma chart_apply (y : Coord F) (w : InfinitePlace F) : chart F y w = chart1 (y w) := rfl
@[simp] lemma chart_symm_apply (P : X F) (w : InfinitePlace F) :
    (chart F).symm P w = chart1.symm (P w) := rfl

/-- The density of `X.vol` in the chart. -/
def rho (y : Coord F) : ℝ := Real.exp (-2 * ∑ w, (y w).2)

variable (F)

/-- `X.vol` in the chart. -/
def muE : Measure (Coord F) := volume.withDensity fun y => ENNReal.ofReal (rho y)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Calc
/-! # WP-X2, file 2: calculus in the logarithmic chart

On `Coord F = InfinitePlace F → ℂ × ℝ` (coordinates `(x_w, t_w)`, `v_w = exp t_w`):

* `pd w k U` — partial derivative in the direction `bvec w k` (`k = 0, 1`: real and imaginary
  part of `x_w`; `k = 2`: `t_w`);
* `lapE U = ∑_w (-(e^{2t_w}(∂₀² + ∂₁²) + ∂₂²) U + 2 ∂₂ U)` — the Laplacian
  `∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` in the chart;
* `gamE U W = ∑_w (e^{2t_w}(∂₀U ∂₀W + ∂₁U ∂₁W) + ∂₂U ∂₂W)` — the (bilinear) carré du champ
  `∑_w v_w² ∇_w U · ∇_w W`;
* `green_E`: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` when one of `T`, `U` has compact support;
* Leibniz rules, compatibility with conjugation.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-- The three coordinate directions of one factor: `Re x`, `Im x`, `t`. -/
def e1 : Fin 3 → E1 := ![(1, 0), (Complex.I, 0), (0, 1)]

@[simp] lemma e1_zero : e1 0 = (1, 0) := rfl
@[simp] lemma e1_one : e1 1 = (Complex.I, 0) := rfl
@[simp] lemma e1_two : e1 2 = (0, 1) := rfl

/-- The coordinate directions of `Coord F`. -/
def bvec (w : InfinitePlace F) (k : Fin 3) : Coord F := Pi.single w (e1 k)

/-- The coefficients of the hyperbolic metric in the chart. -/
def acoef (k : Fin 3) (p : E1) : ℝ := if k = 2 then 1 else Real.exp (2 * p.2)

/-- Partial derivative. -/
def pd (w : InfinitePlace F) (k : Fin 3) (U : Coord F → ℂ) (y : Coord F) : ℂ :=
  fderiv ℝ U y (bvec w k)

/-- The Laplacian in the chart. -/
def lapE (U : Coord F → ℂ) (y : Coord F) : ℂ :=
  ∑ w, ((∑ k, -((acoef k (y w) : ℂ) * pd w k (pd w k U) y)) + 2 * pd w 2 U y)

/-- The bilinear carré du champ in the chart. -/
def gamE (U W : Coord F → ℂ) (y : Coord F) : ℂ :=
  ∑ w, ∑ k, (acoef k (y w) : ℂ) * (pd w k U y * pd w k W y)

/-! ### Regularity -/

lemma contDiff_pd {U : Coord F → ℂ} {n m : WithTop ℕ∞} (h : ContDiff ℝ n U) (hmn : m + 1 ≤ n)
    (w : InfinitePlace F) (k : Fin 3) : ContDiff ℝ m (pd w k U) :=
  (h.fderiv_right hmn).clm_apply contDiff_const

/-! ### Algebraic rules -/

lemma pd_add {U W : Coord F → ℂ} {y : Coord F} (hU : DifferentiableAt ℝ U y)
    (hW : DifferentiableAt ℝ W y) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun y => U y + W y) y = pd w k U y + pd w k W y := by
  unfold pd
  rw [fderiv_fun_add hU hW]
  rfl

lemma lapE_add {U W : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (hW : ContDiff ℝ 2 W) (y : Coord F) :
    lapE (fun y => U y + W y) y = lapE U y + lapE W y := by
  have hd : ∀ {V : Coord F → ℂ}, ContDiff ℝ 2 V → Differentiable ℝ V :=
    fun h => h.differentiable (by simp)
  have hpd : ∀ {V : Coord F → ℂ}, ContDiff ℝ 2 V → ∀ w k, Differentiable ℝ (pd w k V) :=
    fun h w k => (contDiff_pd (m := 1) h (by norm_num) w k).differentiable (by simp)
  unfold lapE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : ∀ k, pd w k (fun y => U y + W y) = fun y => pd w k U y + pd w k W y :=
    fun k => funext fun z => pd_add (hd hU z) (hd hW z) w k
  simp_rw [h1]
  have h2 : ∀ k, pd w k (fun y => pd w k U y + pd w k W y) y =
      pd w k (pd w k U) y + pd w k (pd w k W) y :=
    fun k => pd_add (hpd hU w k y) (hpd hW w k y) w k
  simp_rw [h2, mul_add, neg_add, Finset.sum_add_distrib]
  ring

/-! ### The weights `ρ · a_k` -/

/-- `∑_w t_w` as a continuous linear form. -/
def Ls : Coord F →L[ℝ] ℝ :=
  ∑ w, (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj w)

/-- `t_w` as a continuous linear form. -/
def Lw (w : InfinitePlace F) : Coord F →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℂ ℝ).comp (ContinuousLinearMap.proj w)

/-- The exponent of `ρ · a_k`. -/
def Lk (w : InfinitePlace F) (k : Fin 3) : Coord F →L[ℝ] ℝ :=
  if k = 2 then (-2 : ℝ) • Ls else (-2 : ℝ) • Ls + (2 : ℝ) • Lw w

/-- The weight `ρ(y) a_k(y_w)`. -/
def mC (w : InfinitePlace F) (k : Fin 3) (y : Coord F) : ℂ :=
  ((rho y * acoef k (y w) : ℝ) : ℂ)

/-- The logarithmic derivative of `ρ a_k` in its own direction. -/
def cco (k : Fin 3) : ℂ := if k = 2 then -2 else 0

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X2, file 3: the group acts by isometries; the Laplacian commutes with it

* `Iso1 φ`: a smooth self-map of one factor (in the chart) whose derivative is conformal for the
  hyperbolic metric; translations and the inversion `Jmap` (the chart form of the Weyl element)
  are such, hence every element of `SL(2,ℂ)` acts by one (`mem_iso1`).
* `IsoHalf Φ`: a smooth self-map of `Coord F` preserving the carré du champ.
* `lapE_comp_of_iso`: a measure-preserving `IsoHalf` bijection with `IsoHalf` inverse commutes
  with the Laplacian.  The proof is weak: test against `C_c^∞`, use Green twice — no second
  derivative of the Möbius action is ever computed.
* On `X`: `X.Smooth`, `X.lap`, `X.gam`, and their invariance under `G∞ = SL(2,ℂ)^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

/-! ### One factor -/

/-- A smooth self-map of the chart of one factor that is conformal for the hyperbolic metric. -/
structure Iso1 (φ : E1 → E1) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ
  conf : ∀ (p : E1) (α β : E1 →L[ℝ] ℂ),
    ∑ k, (acoef k p : ℂ) * (α (fderiv ℝ φ p (e1 k)) * β (fderiv ℝ φ p (e1 k))) =
      ∑ k, (acoef k (φ p) : ℂ) * (α (e1 k) * β (e1 k))

lemma Iso1.id : Iso1 (fun p => p) where
  smooth := contDiff_id
  conf p α β := by
    have : fderiv ℝ (fun p : E1 => p) p = ContinuousLinearMap.id ℝ E1 := fderiv_id'
    simp [this]

lemma Iso1.comp {φ ψ : E1 → E1} (hφ : Iso1 φ) (hψ : Iso1 ψ) : Iso1 (fun p => φ (ψ p)) where
  smooth := hφ.smooth.comp hψ.smooth
  conf p α β := by
    have hd : fderiv ℝ (fun p => φ (ψ p)) p = (fderiv ℝ φ (ψ p)).comp (fderiv ℝ ψ p) :=
      fderiv_comp p (hφ.smooth.differentiable (by simp) _) (hψ.smooth.differentiable (by simp) _)
    rw [hd]
    have h1 := hψ.conf p (α.comp (fderiv ℝ φ (ψ p))) (β.comp (fderiv ℝ φ (ψ p)))
    simp only [ContinuousLinearMap.comp_apply] at h1 ⊢
    rw [h1]
    exact hφ.conf (ψ p) α β

/-- `|x|² + e^{2t}`. -/
def rhoJ (p : E1) : ℝ := p.1.re ^ 2 + p.1.im ^ 2 + Real.exp (2 * p.2)

/-- The Weyl element in the chart: `(x, t) ↦ (-conj x / ρ, t - log ρ)`, `ρ = |x|² + e^{2t}`. -/
def Jmap (p : E1) : E1 :=
  (((-p.1.re * (rhoJ p)⁻¹ : ℝ) : ℂ) + ((p.1.im * (rhoJ p)⁻¹ : ℝ) : ℂ) * Complex.I,
    p.2 - Real.log (rhoJ p))

/-- The derivative of `ρ` at `p` applied to `h`. -/
def sJ (p h : E1) : ℝ :=
  2 * p.1.re * h.1.re + 2 * p.1.im * h.1.im + 2 * Real.exp (2 * p.2) * h.2

/-! ### Every element of `SL(2,ℂ)` acts by an `Iso1` -/

/-- The elements of `SL(2,ℂ)` whose action in the chart is an `Iso1`. -/
def iso1Submonoid : Submonoid (SL(2, ℂ)) where
  carrier := {g | ∃ φ : E1 → E1, Iso1 φ ∧ ∀ p, g • chart1 p = chart1 (φ p)}
  one_mem' := ⟨fun p => p, Iso1.id, fun p => one_smul _ _⟩
  mul_mem' := by
    rintro g h ⟨φ, hφ, hg⟩ ⟨ψ, hψ, hh⟩
    exact ⟨fun p => φ (ψ p), hφ.comp hψ, fun p => by rw [mul_smul, hh, hg]⟩

/-! ### Isometries of the chart -/

variable {F : Type*} [Field F] [NumberField F]

/-- A smooth self-map of the chart preserving the carré du champ. -/
structure IsoHalf (Φ : Coord F → Coord F) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) Φ
  gam_comp : ∀ (U W : Coord F → ℂ) (y : Coord F), DifferentiableAt ℝ U (Φ y) →
    DifferentiableAt ℝ W (Φ y) →
    gamE (fun z => U (Φ z)) (fun z => W (Φ z)) y = gamE U W (Φ y)

/-! ### The action of `G∞` in the chart -/

/-- The action of `G∞` read in the chart. -/
def actE (g : Ginf F) (y : Coord F) : Coord F := (chart F).symm (g • chart F y)

/-! ### Calculus on `X` -/

/-- Smoothness of a function on `X` (in the logarithmic chart, equivalently in the coordinates
`(x_w, v_w)`). -/
def X.Smooth (u : X F → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y)

/-- The Laplacian `Δ = ∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` on `X`. -/
def X.lap (u : X F → ℂ) (P : X F) : ℂ := lapE (fun y => u (chart F y)) ((chart F).symm P)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
/-! # WP-X2, file 4: Green's identity on `X` and averaging over `Γ`

* `X.green`: `∫_X φ Δu = ∫_X Γ(φ, u)` when `φ` or `u` has compact support;
* `X.avg Γ φ = ∑_{γ ∈ Γ} φ ∘ γ` for compactly supported `φ`: locally finite, smooth,
  `Δ (avg φ) = avg (Δ φ)`, `Γ(avg φ, u) = avg Γ(φ, u)` for `Γ`-invariant `u`;
* unfolding `∫ η · avg φ · g = ∫_X φ g` for invariant `g` (`integral_avg_mul`);
* **Green's identity on `Γ \ X`** for `w = avg φ` and any smooth invariant `u`
  (`X.qgreen`, `X.qgreen'`): `∫ η w Δu = ∫ η Γ(w, u) = ∫ η u Δw`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### Measure-theoretic instances -/

/-! ### Calculus on `X`: basic rules -/

lemma X.Smooth.contDiff {u : X F → ℂ} (hu : X.Smooth u) :
    ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu

lemma X.Smooth.add {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) :
    X.Smooth fun P => u P + w P := ContDiff.add hu.contDiff hw.contDiff

lemma X.Smooth.const_mul {u : X F → ℂ} (hu : X.Smooth u) (c : ℂ) :
    X.Smooth fun P => c * u P := ContDiff.mul contDiff_const hu.contDiff

lemma X.smooth_const (c : ℂ) : X.Smooth fun _ : X F => c := contDiff_const

lemma two_le_top : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top

/-! ### Invariance -/

/-- The element of `G∞` attached to an integral matrix. -/
def gin (γ : SL(2, 𝓞 F)) : Ginf F := sigma F (intSL F γ)

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Local finiteness and averaging -/

/-- The sum over `Γ` of the translates of a function. -/
def X.avg (Γ : Subgroup (SL(2, 𝓞 F))) (φ : X F → ℂ) (P : X F) : ℂ := ∑' γ : Γ, φ (γ • P)

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

/-- **The geometric core**: sums over `Γ` of smooth compactly supported functions. -/
def X.core : Submodule ℂ (X F → ℂ) where
  carrier := {w | ∃ φ : X F → ℂ, X.Smooth φ ∧ HasCompactSupport φ ∧ w = X.avg Γ φ}
  add_mem' := by
    rintro _ _ ⟨φ, hφ, hc, rfl⟩ ⟨φ', hφ', hc', rfl⟩
    refine ⟨fun P => φ P + φ' P, hφ.add hφ', hc.add hc', ?_⟩
    funext P
    exact ((X.summable_comp_smul_of_hasCompactSupport Γ hc P).tsum_add (X.summable_comp_smul_of_hasCompactSupport Γ hc' P)).symm
  zero_mem' := ⟨fun _ => 0, X.smooth_const 0, HasCompactSupport.zero, by
    funext P; simp [X.avg]⟩
  smul_mem' := by
    rintro c _ ⟨φ, hφ, hc, rfl⟩
    refine ⟨fun P => c * φ P, hφ.const_mul c, hc.mul_left (f := fun _ => c), ?_⟩
    funext P
    simp only [Pi.smul_apply, smul_eq_mul, X.avg]
    rw [tsum_mul_left]

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end


