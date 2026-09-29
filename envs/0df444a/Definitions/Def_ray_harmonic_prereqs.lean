-- Prove2me | Definitions.Def_ray_harmonic_prereqs
-- name    : ray_harmonic_prereqs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T20:55:55.977579+00:00
-- url     : https://prove2.me/theorems/0a8b9281-cae3-47b3-a4f7-eb31b905068c
-- title:
--   ray (3/12): prerequisites for subharmonic functions
-- statement:
--   Auxiliary material for the proof of Hartogs' theorem. It covers the function $\max(b, \log x)$, measure-theoretic lemmas on circle and ball averages, countable families of dual vectors that norm a separable Banach space, connectedness lemmas, annuli and circles in $\mathbb{C}$, Fubini on balls (disk averages as iterated circle averages), and continuity of partial suprema.
--
--   This file is part 3 of 12 of a verbatim flattening of Geoffrey Irving's Lean 4 formalization *ray* (https://github.com/girving/ray, Apache License 2.0). Together the 12 files prove that the Mandelbrot set is connected. Each original ray module is wrapped in its own `section`, and module-system keywords are removed. A few mechanical edits avoid clashes with the full Mathlib import and avoid syntax extensions: a duplicated private definition is dropped, `ContinuousOn.partialSups` is renamed to `ContinuousOn.rayPartialSups`, `Finset.antidiagonal` is written as `Finset.HasAntidiagonal.antidiagonal`, the `bound_destruct` attribute macro is inlined, and the notation `𝕊` is replaced by `(OnePoint ℂ)`. The files are split only because of the compile-time limit. Declaration names are ray's own.
-- source:
--   Geoffrey Irving, ray: The Mandelbrot set is connected (Lean 4 formalization), https://github.com/girving/ray (Apache License 2.0), commit of 2026-08-16; module list in the file header. Mathematical background: A. Douady and J. H. Hubbard, Itération des polynômes quadratiques complexes, C. R. Acad. Sci. Paris 294 (1982); J. Milnor, Dynamics in One Complex Variable, 3rd ed., Section 9 and Appendix; Carleson–Gamelin, Complex Dynamics, Ch. VIII.

import Definitions.Def_ray_osgood_series

/-!
# ray (3/12): prerequisites for subharmonic functions

Part 3 of 12 of a flattened copy of Geoffrey Irving's Lean 4 formalization *ray*
(https://github.com/girving/ray, Apache License 2.0, Copyright Geoffrey Irving), which proves that
the Mandelbrot set is connected. Each original module is wrapped in its own `section`;
module-system keywords are removed, and a few names are adjusted to avoid clashes with Mathlib.

Original modules in this file:
* `Ray.Hartogs.MaxLog`
* `Ray.Misc.Measure`
* `Ray.Hartogs.Duals`
* `Ray.Misc.Set`
* `Ray.Misc.Connected`
* `Ray.Misc.Annuli`
* `Ray.Misc.Complex`
* `Ray.Misc.Circle`
* `Ray.Misc.Prod`
* `Ray.Hartogs.FubiniBall`
* `Ray.Misc.Max`
-/

-- ===== Ray.Hartogs.MaxLog =====
section Ray_Ray_Hartogs_MaxLog
/-!
## `x ↦ max b (log x)`

We define `maxLog b x = max b (log x)` and enumerate its properties.  This function is useful in
proving properties of analytic functions using subharmonic functions, as it lets us avoid working
over the extended reals.  `log (f z)` is subharmonic if `f z` is analytic, but `= -∞` at zeroes of
`f`.  `maxLog b (f z)` is similarly subharmonic, but stays finite.
-/

open scoped Real
open Set
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F]

theorem max_exp_pos {b x : ℝ} : 0 < max b.exp x := by
  bound

@[simp, bound] lemma le_maxLog (b x : ℝ) : b ≤ maxLog b x := by
  rw [maxLog, Real.le_log_iff_exp_le max_exp_pos]; bound

theorem maxLog_eq_b {b x : ℝ} (h : x ≤ b.exp) : maxLog b x = b := by
  simp [maxLog, max_eq_left h]

theorem maxLog_eq_log {b x : ℝ} (h : b.exp ≤ x) : maxLog b x = x.log := by
  simp [maxLog, max_eq_right h]

theorem maxLog_le {b x y : ℝ} (yb : b ≤ y) (xy : x ≤ y.exp) : maxLog b x ≤ y := by
  rw [maxLog, Real.log_le_iff_le_exp max_exp_pos]; apply max_le
  apply Real.exp_le_exp.mpr yb; exact xy

@[bound] lemma le_exp_maxLog (b x : ℝ) : x ≤ (maxLog b x).exp := by
  rw [maxLog, Real.exp_log max_exp_pos]; bound

/-- Extract underlying bounds from `maxLog` bounds -/
theorem le_of_maxLog_le {b x y : ℝ} (m : maxLog b x ≤ y) : x ≤ y.exp := by
  rw [maxLog, Real.log_le_iff_le_exp max_exp_pos] at m; exact le_of_max_le_right m

/-- `maxLog` is increasing -/
theorem monotone_maxLog (b : ℝ) : Monotone fun x ↦ maxLog b x := by
  simp_rw [maxLog]; intro x y xy
  simp only; rw [Real.log_le_log_iff max_exp_pos max_exp_pos]
  apply max_le_max (le_refl _) xy

/-- `maxLog` is continuous -/
theorem continuous_maxLog (b : ℝ) : Continuous fun x ↦ maxLog b x := by
  simp_rw [maxLog]; rw [continuous_iff_continuousAt]; intro x
  refine (ContinuousAt.log ?_ max_exp_pos.ne').comp ?_
  · apply Continuous.continuousAt; apply Continuous.max; exact continuous_const; exact continuous_id
  · exact continuousAt_id

/-- `max b (log ‖f z‖)` is continuous for continuous `f` -/
theorem ContinuousOn.maxLog_norm {f : ℂ → F} {s : Set ℂ} (fc : ContinuousOn f s) (b : ℝ) :
    ContinuousOn (fun z ↦ maxLog b ‖f z‖) s :=
  (continuous_maxLog b).comp_continuousOn fc.norm

/-- `log` is Lipschitz away from 0 -/
theorem LipschitzOnWith.log (b : ℝ) : LipschitzOnWith (-b).exp.toNNReal Real.log (Ici b.exp) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  have half : ∀ x y : ℝ, b.exp ≤ y → y ≤ x → |x.log - y.log| ≤ (-b).exp * |x - y| := by
    intro x y yb xy
    have yp : y > 0 := lt_of_lt_of_le (Real.exp_pos _) yb
    have xp : x > 0 := lt_of_lt_of_le yp xy
    have yi : y⁻¹ ≤ (-b).exp := by rw [Real.exp_neg]; bound
    rw [abs_of_nonneg (sub_nonneg.mpr xy)]
    rw [abs_of_nonneg (sub_nonneg.mpr ((Real.log_le_log_iff yp xp).mpr xy))]
    rw [← Real.log_div xp.ne' yp.ne']
    rw [Real.log_le_iff_le_exp (div_pos xp yp)]
    trans (y⁻¹ * (x - y)).exp; swap; bound
    have e : y⁻¹ * (x - y) = x / y - 1 := by field_simp [yp.ne']
    rw [e]
    have e1 := Real.add_one_le_exp (x / y - 1)
    simp at e1; exact e1
  intro x xs y ys
  simp at xs ys ⊢
  rw [max_eq_left (Real.exp_pos _).le]
  simp_rw [Real.dist_eq]
  by_cases xy : x ≥ y; · exact half x y ys xy
  simp at xy
  rw [← neg_sub y x, abs_neg]
  rw [← neg_sub y.log x.log, abs_neg]
  exact half y x xs xy.le

/-- `maxLog` is Lipschitz -/
theorem LipschitzWith.maxLog (b : ℝ) : LipschitzWith (-b).exp.toNNReal (maxLog b) := by
  rw [← lipschitzOnWith_univ]
  have h := (LipschitzOnWith.log b).comp ((LipschitzWith.id.const_max b.exp).lipschitzOnWith
    (s := univ)) (by simp only [id_eq, Set.mapsTo_univ_iff, Set.mem_Ici, le_max_iff, le_refl,
      true_or, forall_const])
  have e : Real.log ∘ max (Real.exp b) = _root_.maxLog b := by funext x; simp [_root_.maxLog]
  simpa only [e, mul_one, id_eq, ge_iff_le, lipschitzOnWith_univ] using h

end
end Ray_Ray_Hartogs_MaxLog

-- ===== Ray.Misc.Measure =====
section Ray_Ray_Misc_Measure
/-!
## Miscellaneous measure theory lemmas
-/

open Filter (liminf limsup atTop Tendsto)
open Function (curry uncurry)
open MeasureTheory
open Metric (ball closedBall sphere)
open Set (Ioc Icc)
open scoped Real ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {V : Type} [NormedAddCommGroup V]
variable [SecondCountableTopology E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {X : Type} [MeasureSpace X] [MetricSpace X] [BorelSpace X]
variable {Y : Type} [MeasureSpace Y] [MetricSpace Y] [BorelSpace Y]
variable {A : Type} [TopologicalSpace A]
variable {M : Type} [MeasureSpace M]
variable {μ : Measure M}

/-- Removing a null set isn't significant measure-wise -/
theorem ae_minus_null {s t : Set M} (tz : volume t = 0) : s =ᵐ[volume] s \ t := by
  simp only [Filter.EventuallyEq, Pi.sdiff_apply, eq_iff_iff]
  have e : ∀ x, x ∉ t → (x ∈ s ↔ x ∈ s \ t) := by
    intro x h; simp only [Set.mem_sdiff, h, not_false_iff, and_true]
  refine Filter.Eventually.mono ?_ e
  exact measure_eq_zero_iff_ae_notMem.mp tz

/-- Removing a point isn't significant measure-wise (if there are no atoms) -/
theorem ae_minus_point [NullSingletonClass (volume : Measure M)] {s : Set M} {x : M} :
    s =ᵐ[volume] (s \ {x} : Set M) :=
  ae_minus_null (measure_singleton x)

/-- `ℝ × ℝ` has additive Haar measure.
    Lean fails to infer this, so I'm caching it for easy access. -/
instance ProdRealReal.isAddHaarMeasure_volume :
    (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

/-- `ℂ` has additive Haar measure -/
instance Complex.isAddHaarMeasure_volume : (volume : Measure ℂ).IsAddHaarMeasure := by
  have v : (volume : Measure ℂ) = volume.map Complex.equivRealProdAddHom.symm := by
    have e : (⇑Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) =
        ⇑Complex.equivRealProdAddHom.symm := by
      funext x
      simp only [measurableEquivRealProd, Homeomorph.toMeasurableEquiv_symm_coe,
        ContinuousLinearEquiv.coe_symm_toHomeomorph, Complex.ext_iff,
        equivRealProdCLM_symm_apply_re, equivRealProdAddHom_symm_apply_re,
        equivRealProdCLM_symm_apply_im, equivRealProdAddHom_symm_apply_im, and_self]
    rw [← e]; clear e
    exact (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).map_eq.symm
  rw [v]
  have e : (⇑Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) =
      ⇑Complex.equivRealProdAddHom.symm.toAddMonoidHom := by
    funext x
    simp only [Complex.ext_iff, AddEquiv.coe_toAddMonoidHom, Complex.equivRealProdCLM_symm_apply_re,
      Complex.equivRealProdAddHom_symm_apply_re, Complex.equivRealProdCLM_symm_apply_im,
      Complex.equivRealProdAddHom_symm_apply_im, and_self_iff]
  apply Measure.isAddHaarMeasure_map (volume : Measure (ℝ × ℝ))
    Complex.equivRealProdAddHom.symm.toAddMonoidHom
  · rw [←e]; apply ContinuousLinearEquiv.continuous
  · apply AddEquiv.surjective
  · rw [←e]; exact Complex.equivRealProdCLM.symm.toHomeomorph.toCocompactMap.cocompact_tendsto'

/-- `ℂ` has no atoms -/
instance Complex.noAtoms_volume : NullSingletonClass (volume : Measure ℂ) where
  measure_singleton := by
    intro z
    rw [← (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).measure_preimage]
    · rw [← MeasurableEquiv.image_eq_preimage_symm, Set.image_singleton,
        MeasureTheory.measure_singleton]
    · apply MeasurableSet.singleton

/-- The property that a set has finite, positive measure.
    This means that multiplication and division by the measure are invertible operations. -/
structure NiceVolume (s : Set M) : Prop where
  measurable : MeasurableSet s
  finite : volume s < ∞
  pos : volume s > 0

-- Useful lemmas about NiceVolume
lemma NiceVolume.ne_zero {s : Set M} (sn : NiceVolume s) : volume s ≠ 0 := sn.pos.ne'
lemma NiceVolume.ne_top {s : Set M} (sn : NiceVolume s) : volume s ≠ ⊤ := sn.finite.ne
lemma NiceVolume.real_pos {s : Set M} (sn : NiceVolume s) : 0 < volume.real s :=
  ENNReal.toReal_pos_iff.mpr ⟨sn.pos, sn.finite⟩
lemma NiceVolume.real_nonneg {s : Set M} (sn : NiceVolume s) : volume.real s ≠ 0 :=
  sn.real_pos.ne'

/-- Constants are integrable on NiceVolume sets -/
theorem NiceVolume.integrableOn_const {s : Set M} (sn : NiceVolume s) (c : ℝ) :
    IntegrableOn (fun _ : M ↦ c) s :=
  MeasureTheory.integrableOn_const (ne_top sn) enorm_ne_top

/-- Uniform limits of continuous functions and integrals commute -/
theorem TendstoUniformlyOn.integral_tendsto {f : ℕ → X → G} {g : X → G} {s : Set X}
    [SecondCountableTopology G] [IsLocallyFiniteMeasure (volume : Measure X)]
    (u : TendstoUniformlyOn f g atTop s)
    (fc : ∀ n, ContinuousOn (f n) s) (sc : IsCompact s) :
    Tendsto (fun n ↦ ∫ x in s, f n x) atTop (nhds (∫ x in s, g x)) := by
  rcases u.uniformCauchySeqOn.bounded fc sc with ⟨b, _, bh⟩
  apply tendsto_integral_of_dominated_convergence (F := f) (f := g) (fun _ ↦ b)
  · intro n; exact (fc n).aestronglyMeasurable sc.measurableSet
  · exact continuousOn_const.integrableOn_compact sc
  · intro n; specialize bh n; rw [ae_restrict_iff' sc.measurableSet]
    exact ae_of_all _ bh
  · rw [ae_restrict_iff' sc.measurableSet]; apply ae_of_all; intro x xs; exact u.tendsto_at xs

/-- An abbreviation for Ioc 0 (2*π) -/
def itau := Ioc 0 (2 * π)

-- Lemmas about Itau
theorem itau_volume : volume itau = ENNReal.ofReal (2 * π) := by
  simp only [itau, Real.volume_Ioc, sub_zero]
theorem itau_real_volume : volume.real itau = 2 * π := by
  simp only [Measure.real, itau_volume, ENNReal.toReal_ofReal Real.two_pi_pos.le]
theorem NiceVolume.itau : NiceVolume itau :=
  { measurable := by simp only [_root_.itau, measurableSet_Ioc]
    finite := by simp only [itau_volume, ENNReal.ofReal_lt_top]
    pos := by simp only [itau_volume, gt_iff_lt, ENNReal.ofReal_pos, zero_lt_two,
      mul_pos_iff_of_pos_left, Real.pi_pos] }
theorem measurableSet_itau : MeasurableSet itau := by
  simp only [itau, measurableSet_Ioc]
theorem tau_mem_itau : 2*π ∈ itau := by
  simp only [itau, Set.mem_Ioc, zero_lt_two, mul_pos_iff_of_pos_left, Real.pi_pos, le_refl,
    and_self]

/-- Continuous functions are integrable on spheres -/
theorem ContinuousOn.integrableOn_sphere {f : ℂ → V} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (closedBall c r)) (rp : 0 < r) :
    IntegrableOn (fun t ↦ f (circleMap c r t)) itau := by
  apply Continuous.integrableOn_Ioc; apply fc.comp_continuous (continuous_circleMap _ _)
  intro t; simp only [Metric.mem_closedBall, Complex.dist_eq, circleMap_sub_center,
    norm_circleMap_zero, abs_of_pos rp, le_refl]

/-- Continuous functions are integrable on `closedBall` -/
theorem ContinuousOn.integrableOn_closedBall {f : ℂ → V} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (closedBall c r)) : IntegrableOn f (closedBall c r) :=
  fc.integrableOn_compact (isCompact_closedBall _ _)

/-- Averages add -/
theorem Average.add {f g : M → G} {s : Set M} (fi : IntegrableOn f s)
    (gi : IntegrableOn g s) :
    ⨍ z in s, f z + g z = (⨍ z in s, f z) + ⨍ z in s, g z := by
  simp_rw [average_eq, integral_add fi gi, smul_add]

/-- Averages subtract -/
theorem Average.sub {f g : M → G} {s : Set M} (fi : IntegrableOn f s)
    (gi : IntegrableOn g s) :
    ⨍ z in s, f z - g z = (⨍ z in s, f z) - ⨍ z in s, g z := by
  simp_rw [average_eq, integral_sub fi gi, smul_sub]

/-- Averages commute with linear maps -/
theorem average_linear_comm [CompleteSpace G] {f : M → G} {s : Set M} (fi : IntegrableOn f s)
    (g : G →L[ℝ] F) : ⨍ x in s, g (f x) = g (⨍ x in s, f x) := by
  simp only [average_eq, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, map_smul]
  apply congr_arg₂ _ rfl
  exact ContinuousLinearMap.integral_comp_comm _ fi

/-- Averages on a set depend only on ae values within the set -/
theorem average_congr_on {f g : M → G} {s : Set M} (sn : NiceVolume s)
    (h : ∀ᵐ x, x ∈ s → f x = g x) : ⨍ x in s, f x = ⨍ x in s, g x := by
  simp only [← ae_restrict_iff' sn.measurable] at h; exact average_congr h

/-- Means are at most the values of the function -/
theorem mean_bound {f : M → ℝ} {s : Set M} {b : ℝ} (sn : NiceVolume s) (fi : IntegrableOn f s)
    (fb : ∀ z, z ∈ s → f z ≤ b) : ⨍ x in s, f x ≤ b := by
  rw [average_eq, smul_eq_mul]
  have bi := sn.integrableOn_const b
  have ib := setIntegral_mono_on fi bi sn.measurable fb
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
    smul_eq_mul, ge_iff_le] at ib ⊢
  trans (volume.real s)⁻¹ * ((volume.real s) * b)
  · gcongr
  · rw [← mul_assoc _ _ b, inv_mul_cancel₀ sn.real_nonneg, one_mul]

/-- Sets where each point is near positive volume -/
def LocalVolumeSet (s : Set X) :=
  ∀ x r, x ∈ s → 0 < r → 0 < volume (s ∩ ball x r)

/-- Sets in the closure of their interior have local volume -/
theorem LocalVolume.closure_interior {M : Type} [MetricSpace M] [MeasureSpace M] (s : Set M)
    (bp : ∀ (x : M) (r), r > 0 → volume (ball x r) > 0)
    (ci : s ⊆ closure (interior s)) : LocalVolumeSet s := by
  intro x r xs rp
  have xci := ci xs
  rcases Metric.mem_closure_iff.mp xci r rp with ⟨y, ys, xy⟩
  rcases Metric.isOpen_iff.mp isOpen_interior y ys with ⟨e, ep, ye⟩
  set t := min e (r - dist x y)
  have es : ball y t ⊆ s ∩ ball x r := by
    simp only [Set.subset_inter_iff]; constructor
    exact _root_.trans (Metric.ball_subset_ball (by bound)) (_root_.trans ye interior_subset)
    apply Metric.ball_subset_ball'
    trans r - dist x y + dist y x; bound; simp [dist_comm]
  exact lt_of_lt_of_le (bp y t (by bound)) (measure_mono es)

/-- Ioc has local volume -/
theorem LocalVolume.Ioc {a b : ℝ} : LocalVolumeSet (Set.Ioc a b) := by
  apply LocalVolume.closure_interior
  · intro x r rp
    simp only [Real.volume_ball, gt_iff_lt, ENNReal.ofReal_pos]
    bound
  · by_cases ab : a = b; · simp only [ab, Set.Ioc_self, Set.empty_subset]
    simp only [interior_Ioc, closure_Ioo ab, Set.Ioc_subset_Icc_self]

/-- itau has local volume -/
theorem LocalVolume.itau : LocalVolumeSet itau := LocalVolume.Ioc

/-- If an interval mean is above b, and each value is below b, then each value is exactly b -/
theorem mean_squeeze {f : X → ℝ} {s : Set X} {b : ℝ} (sn : NiceVolume s)
    (lv : LocalVolumeSet s) (fc : ContinuousOn f s) (fi : IntegrableOn f s) (lo : b ≤ ⨍ x in s, f x)
    (hi : ∀ x, x ∈ s → f x ≤ b) : ∀ x, x ∈ s → f x = b := by
  contrapose lo; rw [average_eq]
  simp only [smul_eq_mul, not_le]
  simp only [not_forall] at lo
  rcases lo with ⟨x, xs, fx'⟩
  have fx := lt_of_le_of_ne (hi x xs) fx'; clear fx'
  rcases Metric.continuousOn_iff.mp fc x xs ((b - f x) / 2) (by linarith) with ⟨e, ep, he⟩
  have vtp' := lv x e xs ep
  generalize ht : s ∩ ball x e = t; rw [ht] at vtp'
  have ts : t ⊆ s := by rw [← ht]; exact Set.inter_subset_left
  have tf : volume t < ⊤ := lt_of_le_of_lt (measure_mono ts) sn.finite
  have tm : MeasurableSet t := by
    rw [← ht]; exact MeasurableSet.inter sn.measurable measurableSet_ball
  have sc : s \ t ∪ t = s := Set.sdiff_union_of_subset ts
  nth_rw 2 [← sc]
  rw [setIntegral_union]
  simp only [MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter, gt_iff_lt]
  · set m := (b + f x) / 2
    set vs := volume.real s
    set vt := volume.real t
    have vsp : vs > 0 := sn.real_pos
    have vtp : vt > 0 := ENNReal.toReal_pos (vtp'.ne') (lt_top_iff_ne_top.mp tf)
    rw [inv_mul_lt_iff₀' vsp]
    have mb : m < b := by
      calc (b + f x) / 2
        _ < (b + b) / 2 := (div_lt_div_iff_of_pos_right (by norm_num)).mpr (by bound)
        _ = b := by ring
    have i0 : ∫ x in s \ t, f x ≤ (vs - vt) * b := by
      have df : volume (s \ t) < ⊤ := lt_of_le_of_lt (measure_mono Set.sdiff_subset) sn.finite
      have dm : MeasurableSet (s \ t) := MeasurableSet.diff sn.measurable tm
      have fb := setIntegral_mono_on (μ := volume) (f := f) (g := fun _ ↦ b) (s := s \ t)
        (fi.mono Set.sdiff_subset (le_refl _)) (integrableOn_const df.ne_top) dm ?_
      · simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
          MeasureTheory.measureReal_sdiff ts tm sn.ne_top, smul_eq_mul] at fb
        exact fb
      · intro y yd; simp at yd; exact hi y yd.left
    have i1 : ∫ x in t, f x ≤ vt * m := by
      have fm := setIntegral_mono_on (μ := volume) (f := f) (g := fun _ ↦ m) (s := t)
        (fi.mono ts (le_refl _)) (integrableOn_const tf.ne_top) tm ?_
      simp at fm; exact fm
      intro y yt
      rw [← ht] at yt; simp at ht yt
      specialize he y yt.left yt.right
      simp [Real.dist_eq] at he
      calc f y
        _ = f x + (f y - f x) := by ring
        _ ≤ f x + |f y - f x| := by bound
        _ ≤ f x + (b - f x) / 2 := by bound
        _ = (b + f x) / 2 := by ring
    calc (∫ x : X in s \ t, f x) + ∫ x : X in t, f x
      _ ≤ (vs - vt) * b + vt * m := by bound
      _ = vs * b - vt * (b - m) := by ring
      _ < vs * b - 0 := (sub_lt_sub_left (by bound) _)
      _ = b * vs := by ring
  · rw [disjoint_comm]; exact Set.disjoint_sdiff_right
  · exact tm
  · exact fi.mono Set.sdiff_subset (le_refl _)
  · exact fi.mono ts (le_refl _)

theorem ContinuousOn.intervalIntegral {M : Type} [TopologicalSpace M]
    [FirstCountableTopology M] {f : M → ℝ → G} {s : Set M} {a b : ℝ}
    (fc : ContinuousOn (uncurry f) (s ×ˢ Icc a b)) (sc : IsCompact s) (ab : a ≤ b) :
    ContinuousOn (fun x ↦ ∫ t in a..b, f x t) s := by
  rcases ((sc.prod isCompact_Icc).bddAbove_image fc.norm).exists_ge 0 with ⟨c, _, fb⟩
  simp only [Set.forall_mem_image] at fb
  simp only [Set.forall_prod_set, uncurry] at fb
  have e : ∀ x t, f x t = (uncurry f) (x, t) := by
    simp only [Function.uncurry_apply_pair, forall_const, imp_true_iff]
  intro x xs
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ ↦ c)
  · apply eventually_nhdsWithin_of_forall; intro y ys
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    rw [Set.uIoc_of_le ab, (by rfl : f y = fun x ↦ f y x)]; simp_rw [e]; apply fc.comp
    · apply Continuous.continuousOn; exact Continuous.prodMk_right y
    · intro t ts; exact Set.mk_mem_prod ys (Set.Ioc_subset_Icc_self ts)
  · apply eventually_nhdsWithin_of_forall; intro y ys; rw [Set.uIoc_of_le ab]
    apply ae_of_all; intro t ts; apply fb _ ys _ (Set.Ioc_subset_Icc_self ts)
  · exact intervalIntegrable_const
  · apply ae_of_all; intro t ts; simp_rw [e]; apply fc.comp
    · apply Continuous.continuousOn; exact Continuous.prodMk_left t
    · rw [Set.uIoc_of_le ab] at ts
      intro y ys; exact Set.mk_mem_prod ys (Set.Ioc_subset_Icc_self ts)
    · assumption

/-- `liminf` preserves ae measurability, general filter version -/
theorem aEMeasurable_liminf' {I I' : Type} {u : Filter I} {f : I → M → ENNReal} {μ : Measure M}
    {p : I' → Prop} {s : I' → Set I} (fm : ∀ n, AEMeasurable (f n) μ) (uc : u.HasCountableBasis p s)
    (sc : ∀ i, (s i).Countable) : AEMeasurable (fun x ↦ u.liminf fun n ↦ f n x) μ := by
  simp_rw [uc.toHasBasis.liminf_eq_iSup_iInf]
  refine AEMeasurable.biSup _ uc.countable ?_
  intro i _; exact AEMeasurable.biInf _ (sc i) (fun n _ ↦ fm n)

/-- `liminf` preserves ae measurability, `ℕ` version -/
theorem aEMeasurable_liminf {f : ℕ → M → ENNReal} {μ : Measure M} (fm : ∀ n, AEMeasurable (f n) μ) :
    AEMeasurable (fun x ↦ atTop.liminf fun n ↦ f n x) μ :=
  aEMeasurable_liminf' fm Filter.atTop_countable_basis fun _ ↦ Set.to_countable _

theorem set_lintegral_mono_aEMeasurable {s : Set M} {f g : M → ENNReal}
    (sm : MeasurableSet s) (fg : ∀ x, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ≤ ∫⁻ x in s, g x := by
  apply lintegral_mono_ae; rw [ae_restrict_iff' sm]; exact ae_of_all _ fg

lemma measure_union_eq_left {s t : Set M} (t0 : μ t = 0) : μ (s ∪ t) = μ s := by
  have tm := NullMeasurableSet.of_null t0
  have r := MeasureTheory.measure_union_add_inter₀ (μ := μ) s tm
  have i0 : μ (s ∩ t) = 0 := by
    rw [← le_zero_iff] at t0 ⊢
    exact le_trans (MeasureTheory.measure_mono Set.inter_subset_right) t0
  simpa only [t0, i0, add_zero] using r

lemma measure_union_eq_right {s t : Set M} (s0 : μ s = 0) : μ (s ∪ t) = μ t := by
  rw [Set.union_comm]
  exact measure_union_eq_left s0

/-- Commute two interval integrals -/
lemma intervalIntegral.integral_integral_comm {f : ℝ × ℝ → G} {a0 a1 b0 b1 : ℝ} {μ ν : Measure ℝ}
    (a01 : a0 ≤ a1) (b01 : b0 ≤ b1) (i : IntegrableOn f (Ioc a0 a1 ×ˢ Ioc b0 b1) (μ.prod ν))
    [SFinite μ] [SFinite ν] :
    ∫ x in a0..a1, ∫ y in b0..b1, f (x,y) ∂ν ∂μ = ∫ y in b0..b1, ∫ x in a0..a1, f (x,y) ∂μ ∂ν := by
  simp only [intervalIntegral.integral_of_le, a01, b01]
  rw [← MeasureTheory.setIntegral_prod _ i, ← MeasureTheory.setIntegral_prod_swap,
    MeasureTheory.setIntegral_prod]
  · rfl
  · exact i.swap

end
end Ray_Ray_Misc_Measure

-- ===== Ray.Hartogs.Duals =====
section Ray_Ray_Hartogs_Duals
/-!
## Norms in a separable metric space as countable sups of linear functionals

In `Subharmonic.lean`, we want to show that `log ‖f z‖` is subharmonic when `f : ℂ → E` is
analytic, where `E` is any separable normed space.  Since countable suprema of subharmonic
functions are subharmonic, we can do this by showing `log (g (f z))` is subharmonic where
`g : E → ℂ` is any linear functional, then expressing `‖f z‖` as a countable suprema over
linear functions.

This file chooses a countable set of linear functions `duals n : E →L[ℂ] ℂ` for this purpose,
such that `‖x‖ = ⨆ n, ‖duals n x‖`.
-/

open Classical
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere)
open Set (range univ)
open scoped Real NNReal ENNReal Topology ComplexConjugate

noncomputable section

variable {G : Type} [NormedAddCommGroup G]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopology E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A nonconstructive function which extracts a dual vector `f` exhibiting `f x = ‖x‖` -/
def dualVector (x : E) : E →L[ℂ] ℂ :=
  choose (exists_dual_vector'' ℂ x)

@[bound] lemma dualVector_norm (x : F) : ‖dualVector x‖ ≤ 1 :=
  (choose_spec (exists_dual_vector'' ℂ x)).1

@[bound] lemma dualVector_nnnorm (x : F) : ‖dualVector x‖₊ ≤ 1 :=
  dualVector_norm _

@[simp]
theorem dualVector_apply (x : F) : dualVector x x = ‖x‖ :=
  (choose_spec (exists_dual_vector'' ℂ x)).2

theorem dualVector_le (x y : F) : ‖dualVector x y‖ ≤ ‖y‖ := by
  calc ‖dualVector x y‖
    _ ≤ ‖dualVector x‖ * ‖y‖ := (dualVector x).le_opNorm y
    _ ≤ 1 * ‖y‖ := by bound
    _ = ‖y‖ := by simp only [one_mul]

/-- Dual vectors of a dense subset of `E` -/
def duals : ℕ → E →L[ℂ] ℂ := fun n ↦ dualVector (TopologicalSpace.denseSeq E n)

/-- Lipschitz 0 functions are constant -/
theorem LipschitzWith.is_const {g : ℝ → ℝ} (g0 : LipschitzWith 0 g) : ∀ x y, g x = g y := by
  intro x y; simpa only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero] using g0 x y

/-- `g ‖duals n x‖` is bounded above w.r.t. `n` for any monotone `g` -/
theorem duals_bddAbove {g : ℝ → ℝ} (gm : Monotone g) (x : E) :
    BddAbove (range fun n ↦ g ‖duals n x‖) := by
  rw [bddAbove_def]; use g ‖x‖
  simp only [Set.mem_range, forall_exists_index]
  intro _ _ h; rw [←h]; apply gm; apply dualVector_le

/-- One-sided Lipschitz bounds on the reals -/
theorem LipschitzWith.le {f : G → ℝ} {k : ℝ≥0} (fk : LipschitzWith k f) (x y : G) :
    f x ≤ f y + k * dist x y := by
  calc f x
    _ = f y + (f x - f y) := by ring_nf
    _ ≤ f y + |f x - f y| := by bound
    _ = f y + dist (f x) (f y) := by rw [Real.dist_eq]
    _ ≤ f y + k * dist x y := by linarith [fk.dist_le_mul x y]

/-- Norms are suprs over `duals` (version with an arbitrary monotone + Lipschitz function) -/
theorem norm_eq_duals_supr' {g : ℝ → ℝ} {k : NNReal} (gm : Monotone g) (gk : LipschitzWith k g)
    (x : E) : g ‖x‖ = ⨆ n, g ‖duals n x‖ := by
  by_cases k0 : k = 0; · rw [k0] at gk; have g0 := gk.is_const 0; simp only [← g0 _, ciSup_const]
  have kp : 0 < (k : ℝ) := by simp only [NNReal.coe_pos]; exact Ne.bot_lt k0
  apply le_antisymm
  · apply le_of_forall_pos_le_add; intro e ep
    rcases Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq E)
      x (e / 2 / k) (by bound) with ⟨n, nx⟩
    generalize hy : TopologicalSpace.denseSeq E n = y; rw [hy] at nx
    have hn : duals n = dualVector y := by rw [← hy, duals]
    have h := le_ciSup (duals_bddAbove gm x) n
    generalize hs : ⨆ n, g ‖duals n x‖ = s
    simp_rw [hs, hn] at h; clear hs hn hy
    have gk' : LipschitzWith k fun x ↦ g ‖dualVector y x‖ := by
      have k11 : (k : ℝ≥0) = k * 1 * 1 := by norm_num
      rw [k11]
      apply (gk.comp lipschitzWith_one_norm).comp
      exact (dualVector y).lipschitz.weaken (dualVector_nnnorm y)
    calc g ‖x‖
      _ ≤ g ‖y‖ + k * 1 * dist x y := (gk.comp lipschitzWith_one_norm).le x y
      _ ≤ g ‖y‖ + k * 1 * (e / 2 / k) := by bound
      _ = g ‖y‖ + k / k * e / 2 := by ring
      _ ≤ g ‖y‖ + 1 * e / 2 := by bound
      _ = g ‖y‖ + e / 2 := by simp only [one_mul]
      _ = g ‖dualVector y y‖ + e / 2 := by
        simp only [dualVector_apply, Complex.norm_real, norm_norm]
      _ ≤ g ‖dualVector y x‖ + k * dist y x + e / 2 := by bound [gk'.le]
      _ ≤ s + k * dist y x + e / 2 := by linarith
      _ = s + k * dist x y + e / 2 := by rw [dist_comm]
      _ ≤ s + k * (e / 2 / k) + e / 2 := by bound
      _ = s + k / k * e / 2 + e / 2 := by ring_nf
      _ ≤ s + 1 * e / 2 + e / 2 := by bound
      _ = s + e := by ring_nf
  · apply ciSup_le; intro n; apply gm; apply dualVector_le

/-- Norms are suprs over `duals` -/
theorem norm_eq_duals_iSup (x : E) : ‖x‖ = ⨆ n, ‖duals n x‖ := by
  have h := norm_eq_duals_supr' (@monotone_id ℝ _) LipschitzWith.id x
  simpa only [id_eq] using h

/-- Norms are suprs over `duals` (`maxLog` version) -/
theorem maxLog_norm_eq_duals_iSup (b : ℝ) (x : E) : maxLog b ‖x‖ = ⨆ n, maxLog b ‖duals n x‖ :=
  norm_eq_duals_supr' (monotone_maxLog b) (LipschitzWith.maxLog b) x

/-- Rewrite a `ℕ` supr into a monotonic limit -/
theorem Csupr.has_lim (s : ℕ → ℝ) (ba : BddAbove (range s)) :
    Filter.Tendsto (fun n ↦ partialSups s n) atTop (𝓝 (⨆ n, s n)) := by
  rw [Metric.tendsto_atTop]; intro e ep
  generalize hb : (⨆ n, s n) - e = b
  have bs : b < ⨆ n, s n := by rw [← hb]; exact sub_lt_self _ (by linarith)
  rcases exists_lt_of_lt_ciSup bs with ⟨N, sN⟩
  use N; intro n nN; rw [Real.dist_eq]; rw [abs_lt]; constructor
  · simp only [neg_lt_sub_iff_lt_add]; simp only [←hb] at sN
    calc iSup s
      _ = iSup s - e + e := by ring
      _ < s N + e := by linarith
      _ ≤ partialSups s n + e := by linarith [le_partialSups_of_le s nN]
      _ = e + partialSups s n := by ring
  · have rs : partialSups s n ≤ iSup s := partialSups_le _ _ _ fun a _ ↦ le_ciSup ba a
    calc partialSups s n - iSup s
      _ ≤ iSup s - iSup s := by linarith
      _ = 0 := by ring
      _ < e := ep

/-- Partial sups of `maxLog b ‖duals k x‖` converge to `maxLog b ‖x‖` -/
theorem duals_lim_tendsto_maxLog_norm (b : ℝ) (x : E) :
    Filter.Tendsto (partialSups fun k ↦ maxLog b ‖duals k x‖) atTop (𝓝 (maxLog b ‖x‖)) := by
  rw [maxLog_norm_eq_duals_iSup]; exact Csupr.has_lim _ (duals_bddAbove (monotone_maxLog _) _)

/-- Partial sups of `maxLog b ‖duals k x‖` converge to `maxLog b ‖x‖` -/
theorem maxLog_norm_eq_duals_limUnder (b : ℝ) (x : E) :
    maxLog b ‖x‖ = Filter.limUnder atTop (partialSups fun k ↦ maxLog b ‖duals k x‖) :=
  haveI a := duals_lim_tendsto_maxLog_norm b x
  tendsto_nhds_unique a (tendsto_nhds_limUnder ⟨_, a⟩)

end
end Ray_Ray_Hartogs_Duals

-- ===== Ray.Misc.Set =====
section Ray_Ray_Misc_Set
/-!
## `Set` facts
-/

open Set

variable {α : Type}

lemma Set.diff_union {s u v : Set α} : s \ (u ∪ v) = (s \ u) \ v :=
  Set.sdiff_sdiff.symm

end Ray_Ray_Misc_Set

-- ===== Ray.Misc.Connected =====
section Ray_Ray_Misc_Connected
/-!
## Basic result about connected sets

Our main results are

1. Downward intersections are compact, preconnected sets are preconnected
2. Limit points at the ends of rays are preconnected
3. `f ⁻¹' s` is path connected if `f ⁻¹' frontier s` is, for compact `s`
-/

open Filter (Tendsto atTop atBot)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball sphere)
open Set
open scoped NNReal Topology Real
noncomputable section

variable {α : Type}
variable {X : Type} [TopologicalSpace X]
variable {I : Type} [TopologicalSpace I] [ConditionallyCompleteLinearOrder I]
variable [DenselyOrdered I] [OrderTopology I]

theorem closure_inter_subset_compl {s u v : Set X} (vo : IsOpen v) (d : Disjoint u v) :
    closure (s ∩ u) ⊆ vᶜ := by
  rw [← vo.isClosed_compl.closure_eq]; apply closure_mono
  exact _root_.trans inter_subset_right (Disjoint.subset_compl_left d.symm)

theorem isClosed_closed_inter {s u v : Set X} (sc : IsClosed s) (vo : IsOpen v) (d : Disjoint u v)
    (suv : s ⊆ u ∪ v) : IsClosed (s ∩ u) := by
  rw [←closure_subset_iff_isClosed, ←sdiff_eq_empty]
  by_contra h
  simp only [← ne_eq, ← nonempty_iff_ne_empty] at h
  rcases h with ⟨x, h⟩; simp only [mem_sdiff, mem_inter_iff, not_and] at h
  have sus : closure (s ∩ u) ⊆ s := by
    nth_rw 2 [← sc.closure_eq]; apply closure_mono; apply inter_subset_left
  have xs := sus h.1
  have m := not_or.mpr ⟨h.2 xs, notMem_of_mem_compl (closure_inter_subset_compl vo d h.1)⟩
  rw [← mem_union _ _ _] at m; exact notMem_subset suv m xs

/-- In a `NormalSpace`, `s` is preconnected iff for any two disjoint open sets that cover it,
    `s` is contained in one of them.  This is an open version of
    `isPreconnected_iff_subset_of_disjoint_closed`. -/
theorem isPreconnected_iff_subset_of_fully_disjoint_open [NormalSpace X] {s : Set X}
    (sc : IsClosed s) :
    IsPreconnected s ↔ ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed sc]; constructor
  · intro h u v uo vo suv uv
    have suc : IsClosed (s ∩ u) := isClosed_closed_inter sc vo uv suv
    have svc : IsClosed (s ∩ v) := isClosed_closed_inter sc uo uv.symm ((union_comm u v).subst suv)
    have h0 : s ⊆ s ∩ u ∪ s ∩ v := by
      simp only [←inter_union_distrib_left]; exact subset_inter (subset_refl _) suv
    have h1 : Disjoint (s ∩ u) (s ∩ v) := Disjoint.inter_left' _ (Disjoint.inter_right' _ uv)
    cases' h (s ∩ u) (s ∩ v) suc svc h0 h1 with su sv
    · left; exact (subset_inter_iff.mp su).2
    · right; exact (subset_inter_iff.mp sv).2
  · intro h u v uc vc suv uv
    rcases NormalSpace.normal u v uc vc uv with ⟨u', v', uo, vo, uu, vv, uv'⟩
    cases' h u' v' uo vo (_root_.trans suv (union_subset_union uu vv)) uv' with h h
    · left; intro x m; cases' (mem_union _ _ _).mp (suv m) with mu mv
      exact mu; exfalso; exact disjoint_left.mp uv' (h m) (vv mv)
    · right; intro x m; cases' (mem_union _ _ _).mp (suv m) with mu mv
      exfalso; exact disjoint_right.mp uv' (h m) (uu mu); exact mv

/-- Directed intersections of preconnected compact sets are preconnected -/
theorem IsPreconnected.directed_iInter {I : Type} {s : I → Set X} [Nonempty I] [T4Space X]
    (d : Directed (· ⊇ ·) s) (p : ∀ a, IsPreconnected (s a)) (c : ∀ a, IsCompact (s a)) :
    IsPreconnected (⋂ a, s a) := by
  contrapose p
  have ci : IsClosed (⋂ a, s a) := isClosed_iInter fun i ↦ (c i).isClosed
  simp only [isPreconnected_iff_subset_of_fully_disjoint_open ci, not_forall] at p
  simp only [isPreconnected_iff_subset_of_fully_disjoint_open (c _).isClosed, not_forall]
  rcases p with ⟨u, v, uo, vo, suv, uv, no⟩
  have e : ∃ a, s a ⊆ u ∪ v := by
    by_contra h; simp only [not_exists, Set.not_subset] at h
    suffices n : (⋂ a, s a \ (u ∪ v)).Nonempty by
      rcases n with ⟨x, n⟩; simp only [mem_iInter, mem_sdiff, forall_and, forall_const] at n
      rw [← mem_iInter] at n; simp only [suv n.1, not_true] at n; exact n.2
    apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    intro a b; rcases d a b with ⟨c, ac, bc⟩
    use c, (sdiff_subset_sdiff_left ac.le).ge, (sdiff_subset_sdiff_left bc.le).ge
    intro a; rcases h a with ⟨x, xa, xuv⟩; exact ⟨x, mem_sdiff_of_mem xa xuv⟩
    intro a; exact (c a).diff (uo.union vo)
    intro a; exact ((c a).diff (uo.union vo)).isClosed
  rcases e with ⟨a, auv⟩
  use a, u, v, uo, vo, auv, uv
  contrapose no
  cases' no with su sv
  left; exact _root_.trans (iInter_subset _ _) su
  right; exact _root_.trans (iInter_subset _ _) sv

/-- The limit points of a ray `atTop` are preconnected, where a ray is a map from a linearly
    ordered, conditionally complete space. -/
theorem IsPreconnected.limits_atTop [CompactSpace X] [T4Space X] {P : Type} [SemilatticeSup P]
    [TopologicalSpace P] [Nonempty P] (p : ∀ a : P, IsPreconnected (Ici a))
    {r : P → X} (rc : Continuous r) : IsPreconnected {x | MapClusterPt x atTop r} := by
  generalize hs : (fun a ↦ closure (r '' Ici a)) = s
  have m : Antitone s := by
    intro a b ab; rw [← hs]; exact closure_mono (monotone_image (Ici_subset_Ici.mpr ab))
  have d : Directed (· ⊇ ·) s := by
    intro a b; exact ⟨a ⊔ b, (m le_sup_left).ge, (m le_sup_right).ge⟩
  have p : ∀ a, IsPreconnected (s a) := by
    intro a; rw [← hs]; exact ((p _).image _ rc.continuousOn).closure
  have c : ∀ a, IsCompact (s a) := by
    intro a; rw [← hs]; exact isClosed_closure.isCompact
  have e : {x | MapClusterPt x atTop r} = ⋂ a, s a := by
    ext x
    simp only [mem_ofPred, mem_iInter, mapClusterPt_iff_frequently, mem_closure_iff_nhds,
      Set.Nonempty, @forall_comm P, ← hs]
    apply forall_congr'; intro t
    simp only [mem_inter_iff, mem_image, mem_Ici, @and_comm (_ ∈ t), exists_exists_and_eq_and,
      Filter.frequently_atTop]
  rw [e]; exact IsPreconnected.directed_iInter d p c

/-- The limit points of a ray `atBot` are preconnected (the other direction of the ray in
    `IsPreconnected.limits_atTop`) -/
theorem IsPreconnected.limits_atBot [CompactSpace X] [T4Space X] {P : Type} [SemilatticeInf P]
    [TopologicalSpace P] [Nonempty P] (p : ∀ a : P, IsPreconnected (Iic a))
    {r : P → X} (rc : Continuous r) : IsPreconnected {x | MapClusterPt x atBot r} := by
  set r' : Pᵒᵈ → X := r
  have rc' : Continuous r' := rc
  have p' : ∀ a : Pᵒᵈ, IsPreconnected (Ici a) := fun a ↦ p a
  exact IsPreconnected.limits_atTop p' rc'

/-- The limits points near `a` of an open curve from `Ioc a b` are preconnected -/
-- Ideally I'd use `IsPreconnected.limits_atTop` to prove this, but when I tried that
-- I hit horrible instance resolution mismatches.
theorem IsPreconnected.limits_Ioc [CompactSpace X] [T4Space X] {r : ℝ → X} {a b : ℝ}
    (rc : ContinuousOn r (Ioc a b)) : IsPreconnected {x | MapClusterPt x (𝓝[Ioc a b] a) r} := by
  by_cases ab : ¬a < b
  · simp only [Ioc_eq_empty ab, nhdsWithin_empty, MapClusterPt, Filter.map_bot, ClusterPt.bot,
      ofPred_false, isPreconnected_empty]
  simp only [not_not] at ab
  generalize hs : (fun t : Ioc a b ↦ closure (r '' Ioc a t)) = s
  have n : Nonempty (Ioc a b) := ⟨b, right_mem_Ioc.mpr ab⟩
  have m : Monotone s := by
    intro a b ab; rw [← hs]; refine closure_mono (monotone_image ?_)
    exact Ioc_subset_Ioc (le_refl _) (Subtype.coe_le_coe.mpr ab)
  have d : Directed (· ⊇ ·) s := fun a b ↦
    ⟨min a b, (m (min_le_left _ _)).ge, (m (min_le_right _ _)).ge⟩
  have p : ∀ t, IsPreconnected (s t) := by
    intro ⟨t, m⟩; rw [← hs]; refine (isPreconnected_Ioc.image _ (rc.mono ?_)).closure
    simp only [mem_Ioc] at m
    simp only [Ioc_subset_Ioc_iff m.1, m.2, le_refl, true_and]
  have c : ∀ t, IsCompact (s t) := by intro t; rw [← hs]; exact isClosed_closure.isCompact
  have e : {x | MapClusterPt x (𝓝[Ioc a b] a) r} = ⋂ t, s t := by
    apply Set.ext; intro x
    simp only [mem_ofPred, mem_iInter, mapClusterPt_iff_frequently, mem_closure_iff_nhds,
      Set.Nonempty, @forall_comm _ (Set X), ← hs]
    apply forall_congr'; intro u
    simp only [Filter.frequently_iff, @forall_comm _ (u ∈ 𝓝 x)]; apply forall_congr'; intro _
    simp only [mem_inter_iff, nhdsWithin_Ioc_eq_nhdsGT ab]
    constructor
    · intro h ⟨t, m⟩
      have tm : Ioc a t ∈ 𝓝[Ioi a] a := by
        apply Ioc_mem_nhdsGT_of_mem
        simp only [mem_Ioc] at m; simp only [mem_Ico]; use le_refl _, m.1
      rcases h tm with ⟨v, vm, vu⟩; exact ⟨r v, vu, mem_image_of_mem _ vm⟩
    · intro h v vm
      rcases mem_nhdsGT_iff_exists_Ioc_subset.mp vm with ⟨w, wa, wv⟩
      simp only [mem_Ioi] at wa
      have m : min w b ∈ Ioc a b := by simp only [mem_Ioc]; use lt_min wa ab, min_le_right _ _
      rcases h ⟨_, m⟩ with ⟨x, xu, rx⟩
      simp only [mem_image, mem_Ioc, le_min_iff] at rx
      rcases rx with ⟨c, ⟨ac, cw, _⟩, cx⟩
      use c, wv (mem_Ioc.mpr ⟨ac, cw⟩); rwa [cx]
  rw [e]; exact IsPreconnected.directed_iInter d p c

/-- Nonempty, relatively clopen subsets of preconnected sets are empty or the full set -/
theorem IsPreconnected.relative_clopen {s t : Set X} (sp : IsPreconnected s)
    (ne : (s ∩ t).Nonempty) (op : s ∩ t ⊆ interior t) (cl : s ∩ closure t ⊆ t) :
    s ⊆ interior t := by
  generalize hu : (fun x : s ↦ (x : X)) ⁻¹' t = u
  have uo : IsOpen u := by
    rw [← subset_interior_iff_isOpen]; intro ⟨x, m⟩ h
    simp only [mem_preimage, ← hu] at h
    have n := op ⟨m, h⟩
    simp only [mem_interior_iff_mem_nhds, preimage_coe_mem_nhds_subtype, ← hu] at n ⊢
    exact nhdsWithin_le_nhds n
  have uc : IsClosed u := by
    rw [← closure_eq_iff_isClosed]; refine subset_antisymm ?_ subset_closure
    rw [← hu]
    refine _root_.trans (continuous_subtype_val.closure_preimage_subset _) ?_
    intro ⟨x, m⟩ h; exact cl ⟨m, h⟩
  have p : IsPreconnected (univ : Set s) := (Subtype.preconnectedSpace sp).isPreconnected_univ
  cases' disjoint_or_subset_of_isClopen p ⟨uc, uo⟩ with h h
  · simp only [univ_disjoint, preimage_eq_empty_iff, Subtype.range_coe, ← hu] at h
    exfalso; exact ne.not_disjoint h.symm
  · rw [← Subtype.coe_preimage_self, ← hu, preimage_subset_preimage_iff] at h
    exact _root_.trans (subset_inter (subset_refl _) h) op
    simp only [Subtype.range_coe, subset_refl]

/-- `ContinuousOn` images of preconnected sets are preconnected (this is a version of
    `IsPathConnected.image` assuming only `ContinuousOn`) -/
theorem IsPathConnected.image_of_continuousOn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (sc : IsPathConnected s) {f : X → Y} (fc : ContinuousOn f s) :
    IsPathConnected (f '' s) := by
  have uc : IsPathConnected (univ : Set s) := by
    convert sc.preimage_coe (subset_refl _); apply Set.ext; intro x
    simp only [mem_univ, mem_preimage, Subtype.mem]
  have e : f '' s = s.domRestrict f '' univ := by
    apply Set.ext; intro y; constructor
    intro ⟨x, m, e⟩; use⟨x, m⟩, mem_univ _, e
    intro ⟨⟨x, m⟩, _, e⟩; use x, m, e
  rw [e]; exact uc.image (continuousOn_iff_continuous_domRestrict.mp fc)

/-- Circles are path connected -/
theorem Complex.isPathConnected_sphere {z : ℂ} {r : ℝ} (r0 : 0 ≤ r) :
    IsPathConnected (sphere z r) := by
  rw [← abs_of_nonneg r0, ← image_circleMap_Ioc z r]
  refine IsPathConnected.image ?_ (continuous_circleMap _ _)
  exact (convex_Ioc 0 (2 * π)).isPathConnected (nonempty_Ioc.mpr Real.two_pi_pos)

/-- Path connectedness of `f ⁻¹' frontier s` implies path connectedness of `f ⁻¹' s`,
    for compact `s`.

    Proof: Walk out of s until we hit the frontier, then move within the frontier.
    Unfortunately this seems very tedious to write out, so I'm clearly missing some tricks. -/
theorem IsPathConnected.of_frontier {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] {f : X → Y} {s : Set Y}
    (pc : IsPathConnected (f ⁻¹' frontier s)) (fc : Continuous f) (sc : IsClosed s) :
    IsPathConnected (f ⁻¹' s) := by
  have pc' := pc; rcases pc' with ⟨b, fb, j⟩; use b
  simp only [mem_preimage] at fb j ⊢
  have bs : f b ∈ s := sc.frontier_subset fb
  use bs; intro x fx
  have p := PathConnectedSpace.somePath x b
  generalize hu : Icc (0 : ℝ) 1 ∩ ⋂ (a) (_ : f (p.extend a) ∉ s), Iic a = u
  have bdd : BddAbove u := by rw [← hu, bddAbove_def]; use 1; intro t ⟨m, _⟩; exact m.2
  have un : u.Nonempty := by
    rw [← hu]; use 0, left_mem_Icc.mpr zero_le_one; simp only [mem_iInter₂, mem_Iic]; intro a m
    contrapose m; simp only [p.extend_of_le_zero (not_le.mp m).le, fx]
  have uc : IsClosed u := by
    rw [← hu]; apply isClosed_Icc.inter; apply isClosed_iInter; intro a; apply isClosed_iInter
    intro _; exact isClosed_Iic
  generalize ht : sSup u = t
  have tu : t ∈ u := by rw [← uc.closure_eq, ← ht]; exact csSup_mem_closure un bdd
  have m : t ∈ Icc (0 : ℝ) 1 := by rw [← hu] at tu; exact tu.1
  have lo : ∀ a, a ≤ t → f (p.extend a) ∈ s := by
    intro a h; contrapose h; simp only [not_le]
    replace h : ∀ᶠ b in 𝓝 a, f (p.extend b) ∉ s :=
      (fc.comp p.continuous_extend).continuousAt.eventually_mem (sc.isOpen_compl.mem_nhds h)
    simp only [← hu, mem_inter_iff, mem_iInter₂, mem_Iic] at tu ⊢
    rcases ((frequently_lt_nhds a).and_eventually h).exists with ⟨c, ca, cs⟩
    exact lt_of_le_of_lt (tu.2 c cs) ca
  by_cases t1 : t = 1
  · use p.symm; intro a; simp only [p.symm_apply, Function.comp, mem_preimage]
    rw [← Path.extend_extends']; apply lo; rw [t1]; unit_interval
  replace t1 : t < 1 := Ne.lt_of_le t1 m.2
  have ft : f (p ⟨t, m⟩) ∈ frontier s := by
    simp only [frontier, mem_sdiff, sc.closure_eq]; constructor
    · convert lo t (le_refl _)
      simp only [Path.extend_apply _ m]
    · have e : p ⟨t, m⟩ = p.extend t := by
        simp only [Path.extend, IccExtend, ContinuousMap.coe_mk, Function.comp_apply, projIcc,
          min_eq_right m.2, max_eq_right m.1]
      rw [e]; clear e; simp only [← ht]
      by_contra h
      rw [ht] at h
      have o : IsOpen (f ∘ p.extend ⁻¹' interior s) :=
        isOpen_interior.preimage (fc.comp p.continuous_extend)
      rcases (nhds_basis_Ioo t).mem_iff.mp (o.mem_nhds h) with ⟨⟨x, y⟩, ⟨xt, ty⟩, h⟩
      simp only [subset_def, mem_Ioo, and_imp, mem_preimage, Function.comp] at xt ty h
      rcases exists_between (lt_min ty t1) with ⟨z, tz, zy1⟩; rcases lt_min_iff.mp zy1 with ⟨zy, z1⟩
      suffices h : z ∈ u by linarith [le_csSup bdd h]
      rw [← hu]; refine ⟨⟨_root_.trans m.1 tz.le, z1.le⟩, ?_⟩
      simp only [mem_iInter₂, mem_Iic]; intro w ws
      contrapose ws; simp only [not_le] at ws ⊢
      by_cases xw : x < w; refine interior_subset (h _ xw (_root_.trans ws zy))
      simp only [not_lt] at xw; exact lo _ (_root_.trans xw xt.le)
  -- Walk from b to p t
  refine ((pc.joinedIn _ ft b fb).mono (preimage_mono sc.frontier_subset)).symm.trans
    (JoinedIn.symm ?_)
  -- Walk from x to p t
  generalize hq : (fun a : unitInterval ↦ p.extend (min a t)) = q
  have qc : Continuous q := by
    rw [← hq]; exact p.continuous_extend.comp (continuous_subtype_val.min continuous_const)
  refine ⟨⟨⟨q,qc⟩,?_,?_⟩,?_⟩
  · simp only [← hq]; simp only [Icc.coe_zero, min_eq_left m.1, p.extend_zero]
  · simp only [← hq]
    simp only [Path.extend, Icc.coe_one, min_eq_right m.2, ContinuousMap.coe_mk, IccExtend_apply,
      max_eq_right m.1]
  · intro ⟨a, n⟩; simp only [mem_preimage, Path.coe_mk_mk, ← hq]
    exact lo _ (min_le_right _ _)

theorem IsPathConnected.of_frontier' {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    {s : Set X} (pc : IsPathConnected (frontier s)) (sc : IsClosed s) : IsPathConnected s :=
  IsPathConnected.of_frontier pc continuous_id sc

/-- If open, preconnected `s` intersects `t` but does not touch `frontier t`, then `s ⊆ t` -/
theorem IsPreconnected.subset_of_disjoint_frontier {s t : Set X} (sp : IsPreconnected s)
    (os : IsOpen s) (ot : IsOpen t) (i : Disjoint (frontier t) s) (n : (s ∩ t).Nonempty) :
    s ⊆ t := by
  have e : s = s ∩ t ∪ (s \ closure t) := by
    simp only [closure_eq_interior_union_frontier, ot.interior_eq, union_comm t, diff_union,
      inter_union_sdiff, i.sdiff_eq_right]
  have d : s ∩ (s ∩ t ∩ (s \ closure t)) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not, and_imp,
      forall_self_imp]
    intro _ m _
    exact subset_closure m
  rcases isPreconnected_iff_subset_of_disjoint.mp sp (s ∩ t) (s \ closure t) (os.inter ot)
    (os.sdiff isClosed_closure) (by simp only [← e, subset_refl]) d with h | h
  · exact subset_trans h inter_subset_right
  · obtain ⟨_, xs, xt⟩ := n
    have xd := h xs
    simp [subset_closure xt] at xd

/-- Two intersecting, open, preconnected sets with common frontier are the same -/
theorem IsPreconnected.eq_of_frontier_eq {s t : Set X} (sp : IsPreconnected s)
    (tp : IsPreconnected t) (os : IsOpen s) (ot : IsOpen t) (f : frontier s = frontier t)
    (n : (s ∩ t).Nonempty) : s = t := by
  apply subset_antisymm
  · exact sp.subset_of_disjoint_frontier os ot (f ▸ disjoint_frontier_iff_isOpen.mpr os) n
  · exact tp.subset_of_disjoint_frontier ot os (f ▸ disjoint_frontier_iff_isOpen.mpr ot)
      (inter_comm _ _ ▸ n)

end
end Ray_Ray_Misc_Connected

-- ===== Ray.Misc.Annuli =====
section Ray_Ray_Misc_Annuli
/-!
## Finite and infinite annuli
-/

open MeasureTheory (volume)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open scoped Real Topology
noncomputable section

/-- The region strictly outside radius `r` -/
def norm_Ioi (r : ℝ) : Set ℂ := {w : ℂ | r < ‖w‖}

/-- The region weakly outside radius `r` -/
def norm_Ici (r : ℝ) : Set ℂ := {w : ℂ | r ≤ ‖w‖}

/-- A closed annulus around the origin -/
def norm_Icc (r s : ℝ) : Set ℂ := Norm.norm ⁻¹' Icc r s

/-- An open annulus around the origin -/
def norm_Ioo (r s : ℝ) : Set ℂ := Norm.norm ⁻¹' Ioo r s

/-- A half-open annulus around `c` -/
def annulus_oc (c : ℂ) (r0 r1 : ℝ) : Set ℂ := closedBall c r1 \ closedBall c r0

/-- A closed annulus around `c` -/
def annulus_cc (c : ℂ) (r0 r1 : ℝ) : Set ℂ := closedBall c r1 \ ball c r0

lemma isOpen_norm_Ioi {r : ℝ} : IsOpen (norm_Ioi r) := by
  simp only [norm_Ioi]; exact isOpen_Ioi.preimage continuous_norm

lemma isOpen_norm_Ioo {r s : ℝ} : IsOpen (norm_Ioo r s) := by
  simp only [norm_Ioo]; exact isOpen_Ioo.preimage continuous_norm

lemma isClosed_norm_Ici {r : ℝ} : IsClosed (norm_Ici r) := by
  simp only [norm_Ici]; exact isClosed_Ici.preimage continuous_norm

lemma norm_Icc_eq_diff {r s : ℝ} : norm_Icc r s = closedBall 0 s \ ball 0 r := by
  ext z
  simp only [norm_Icc, mem_preimage, mem_Icc, mem_sdiff, Metric.mem_closedBall, dist_zero_right,
    Metric.mem_ball, not_lt, and_comm]

@[simp] lemma norm_Ici_diff_norm_Ioi {r : ℝ} : norm_Ici r \ norm_Ioi r = sphere 0 r := by
  ext z
  simp only [norm_Ici, norm_Ioi, mem_sdiff, mem_ofPred_eq, not_lt, ← le_antisymm_iff,
    mem_sphere_iff_norm, sub_zero, eq_comm]

lemma isCompact_norm_Icc {r s : ℝ} : IsCompact (norm_Icc r s) := by
  rw [norm_Icc_eq_diff]; exact (isCompact_closedBall _ _).diff isOpen_ball

lemma isCompact_annulus_cc {c : ℂ} {r s : ℝ} : IsCompact (annulus_cc c r s) := by
  exact (isCompact_closedBall _ _).diff isOpen_ball

lemma norm_Ioi_subset_norm_Ici {r : ℝ} : norm_Ioi r ⊆ norm_Ici r := by
  simp only [norm_Ioi, norm_Ici, ofPred_subset_ofPred]; intro _; exact le_of_lt

lemma norm_Icc_subset_norm_Ici {r s : ℝ} : norm_Icc r s ⊆ norm_Ici r := by
  simp only [norm_Icc, norm_Ici, preimage_subset_iff, mem_Icc, mem_ofPred_eq, and_imp]
  intro _ h _; exact h

lemma norm_Ici_mono {r s : ℝ} (rs : r ≤ s) : norm_Ici s ⊆ norm_Ici r := by
  simp only [norm_Ici, ofPred_subset_ofPred]; intro _ h; linarith

@[simp] lemma norm_Ici_eq_univ {r : ℝ} (r0 : r ≤ 0) : norm_Ici r = univ := by
  ext z
  simp only [norm_Ici, mem_ofPred_eq, mem_univ, iff_true]
  exact le_trans r0 (by bound)

lemma isPathConnected_norm_Ici {r : ℝ} : IsPathConnected (norm_Ici r) := by
  cases' lt_or_ge r 0 with r0 r0
  · simp only [norm_Ici_eq_univ r0.le, isPathConnected_univ]
  simp only [norm_Ici, ← Set.preimage_ofPred_eq, Ici_def]
  refine IsPathConnected.of_frontier ?_ continuous_norm isClosed_Ici
  simp only [nonempty_Iio, frontier_Ici']
  convert Complex.isPathConnected_sphere (z := 0) r0
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_sphere_iff_norm, sub_zero]

lemma isPreconnected_norm_Ioi {r : ℝ} : IsPreconnected (norm_Ioi r) := by
  set f : ℝᵒᵈ → Set ℂ := fun s ↦ norm_Ici (OrderDual.ofDual s)
  have e : norm_Ioi r = ⋃₀ (f '' Iio (OrderDual.toDual r)) := by
    ext z
    simp only [norm_Ioi, mem_ofPred_eq, norm_Ici, Iio_toDual, sUnion_image, mem_preimage, mem_Ioi,
      mem_iUnion, exists_prop, OrderDual.exists, OrderDual.ofDual_toDual, f]
    constructor
    · intro rz; exact ⟨‖z‖, rz, le_refl _⟩
    · intro ⟨s,rs,sz⟩; exact lt_of_lt_of_le rs sz
  rw [e]
  apply IsPreconnected.sUnion_directed
  · simp only [DirectedOn, Iio_toDual, mem_image, mem_preimage, mem_Ioi, OrderDual.exists,
      OrderDual.ofDual_toDual, exists_exists_and_eq_and, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro a ar b br
    exact ⟨min a b, by bound, norm_Ici_mono (by bound), norm_Ici_mono (by bound)⟩
  · simp only [Iio_toDual, mem_image, mem_preimage, mem_Ioi, OrderDual.exists, f,
      OrderDual.ofDual_toDual, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      isPathConnected_norm_Ici.isConnected.isPreconnected, implies_true]

lemma compl_norm_Ioi {r : ℝ} : (norm_Ioi r)ᶜ = closedBall 0 r := by
  ext z
  simp [norm_Ioi]

@[simp] lemma frontier_norm_Ioi {r : ℝ} : frontier (norm_Ioi r) = sphere 0 r := by
  rw [← frontier_compl, compl_norm_Ioi, frontier_closedBall']

@[simp] lemma closure_norm_Ioi {r : ℝ} : closure (norm_Ioi r) = norm_Ici r := by
  simp only [closure_eq_interior_union_frontier, frontier_norm_Ioi, isOpen_norm_Ioi.interior_eq]
  ext z
  simp [norm_Ioi, norm_Ici, eq_comm (b := r), le_iff_lt_or_eq]

@[simp] lemma norm_Ioi_subset_norm_Ioi {r s : ℝ} (sr : s ≤ r) : norm_Ioi r ⊆ norm_Ioi s := by
  intro z m
  simp only [mem_ofPred_eq, norm_Ioi] at m ⊢
  order

@[simp] lemma norm_Ici_subset_norm_Ioi {r s : ℝ} (sr : s < r) : norm_Ici r ⊆ norm_Ioi s := by
  intro z m
  simp only [norm_Ici, mem_ofPred_eq, norm_Ioi] at m ⊢
  order

lemma annulus_oc_subset_annulus_cc {c : ℂ} {r0 r1 : ℝ} :
    annulus_oc c r0 r1 ⊆ annulus_cc c r0 r1 :=
  sdiff_subset_sdiff (subset_refl _) Metric.ball_subset_closedBall

lemma measurableSet_annulus_oc {c : ℂ} {r0 r1 : ℝ} :
    MeasurableSet (annulus_oc c r0 r1) :=
  measurableSet_closedBall.diff measurableSet_closedBall

lemma measurableSet_annulus_cc {c : ℂ} {r0 r1 : ℝ} :
    MeasurableSet (annulus_cc c r0 r1) :=
  measurableSet_closedBall.diff measurableSet_ball

@[simp, aesop (rule_sets := [finiteness]) safe apply] public lemma finite_measure_annulus_cc {c : ℂ}
    {r0 r1 : ℝ} : volume (annulus_cc c r0 r1) ≠ ⊤ := isCompact_annulus_cc.measure_ne_top

lemma annulus_oc_subset_norm_Ioi {a r s : ℝ} (ar : a ≤ r) : annulus_oc 0 r s ⊆ norm_Ioi a := by
  intro z m
  simp only [annulus_oc, mem_sdiff, Metric.mem_closedBall, dist_zero_right, not_le, norm_Ioi,
    mem_ofPred_eq] at m ⊢
  exact lt_of_le_of_lt ar m.2

lemma annulus_cc_subset_norm_Ioi {a r s : ℝ} (ar : a < r) :
    annulus_cc 0 r s ⊆ norm_Ioi a := by
  intro z m
  simp only [annulus_cc, mem_sdiff, Metric.mem_closedBall, dist_zero_right, Metric.mem_ball, not_lt,
    norm_Ioi, mem_ofPred_eq] at m ⊢
  exact lt_of_lt_of_le ar m.2

lemma symmDiff_annulus_oc_annulus_cc {c : ℂ} {r s : ℝ} (rs : r ≤ s) :
    (symmDiff (annulus_oc c r s) (annulus_cc c r s)) = sphere c r := by
  ext z
  simp only [annulus_oc, annulus_cc, mem_symmDiff, mem_sdiff, Metric.mem_closedBall, dist_eq_norm,
    not_le, Metric.mem_ball, not_lt, not_and, mem_sphere_iff_norm]
  -- `grind` used to close the goal at this point, but doesn't anymore due to a bug
  constructor
  · intro h
    rcases h with h | ⟨⟨zs,rz⟩,zr⟩
    · grind
    · linarith [zr zs]
  · intro e
    simp [e, rs]

end
end Ray_Ray_Misc_Annuli

-- ===== Ray.Misc.Complex =====
section Ray_Ray_Misc_Complex
/-!
## Complex facts
-/

open Classical
open Metric (sphere)
open Complex (arg log I imCLM slitPlane)
open ContinuousLinearMap (lsmul)
open Set
open scoped ContDiff Real ComplexConjugate
noncomputable section

variable {X : Type} [TopologicalSpace X]

lemma Complex.arg_lt_zero_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 := by
  rw [← not_iff_not, not_lt, not_lt]
  exact arg_nonneg_iff

/-- A clean version of `(z / w).im` -/
lemma div_im_eq_inner (z w : ℂ) : (z / w).im = inner ℝ z (w * I) / w.normSq := by
  simp [Complex.div_im, Complex.inner]
  ring

/-- Spheres are empty iff the radius is negative -/
@[simp]
theorem Metric.sphere_eq_empty {S : Type} [RCLike S] {c : S} {r : ℝ} : sphere c r = ∅ ↔ r < 0 := by
  constructor
  · intro rp; contrapose rp; simp at rp
    refine Nonempty.ne_empty ⟨c + r, ?_⟩
    simpa only [mem_sphere_iff_norm, add_sub_cancel_left, RCLike.norm_ofReal, abs_eq_self]
  · intro n; contrapose n
    rw [← not_nonempty_iff_eq_empty] at n
    simpa only [not_lt, NormedSpace.sphere_nonempty, not_le] using n

/-- `range (circleMap c r _) = sphere c r` even when restricted to `Ioc 0 (2π)` -/
theorem circleMap_Ioc {c z : ℂ} {r : ℝ} (zs : z ∈ sphere c r) :
    ∃ t, t ∈ Ioc 0 (2 * π) ∧ z = circleMap c r t := by
  by_cases rp : r < 0
  · simp only [Metric.sphere_eq_empty.mpr rp, mem_empty_iff_false] at zs
  simp only [not_lt] at rp
  rw [←abs_of_nonneg rp, ← range_circleMap, mem_range] at zs
  rcases zs with ⟨t, ht⟩
  generalize ha : 2 * π = a
  have ap : a > 0 := by rw [←ha]; bound
  generalize hs : t + a - a * ⌈t / a⌉ = s
  use s; constructor
  · simp only [mem_Ioc, sub_pos, tsub_le_iff_right, ← hs]
    constructor
    · calc a * ⌈t / a⌉
        _ < a * (t / a + 1) := by bound
        _ = a / a * t + a := by ring
        _ = t + a := by field_simp [ap.ne']
    · calc a + a * ⌈t / a⌉
        _ ≥ a + a * (t / a) := by bound
        _ = a / a * t + a := by ring
        _ = t + a := by field_simp [ap.ne']
  · simp only [←ht, circleMap, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_intCast, add_right_inj, mul_eq_mul_left_iff, Complex.ofReal_eq_zero, ← hs]
    rw [mul_sub_right_distrib, right_distrib, Complex.exp_sub, Complex.exp_add]
    rw [mul_comm _ (⌈_⌉:ℂ), mul_assoc, Complex.exp_int_mul, ← ha]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I, mul_one,
      one_zpow, div_one, true_or]

@[fun_prop] lemma ContinuousAt.complex_conj {f : X → ℂ} {x : X} (h : ContinuousAt f x) :
    ContinuousAt (fun x ↦ conj (f x)) x :=
  Complex.continuous_conj.continuousAt.comp h

/-!
### Derivatives mixing `ℝ` and `ℂ`
-/

/-- `Complex.ofReal` is real analytic -/
lemma Complex.analyticAt_ofReal {x : ℝ} : AnalyticAt ℝ Complex.ofReal x := by
  have e : Complex.ofReal = fun x ↦ Complex.ofRealCLM x := by simp
  rw [e]
  exact Complex.ofRealCLM.analyticAt x

/-- `Complex.ofReal` is real analytic -/
lemma AnalyticAt.ofReal {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {x : E} (a : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun x ↦ (f x : ℂ)) x :=
  Complex.analyticAt_ofReal.comp a

/-- `Complex.ofReal` is real analytic -/
lemma Complex.contDiffAt_ofReal {x : ℝ} : ContDiffAt ℝ ω Complex.ofReal x :=
  Complex.analyticAt_ofReal.contDiffAt

/-- `Complex.ofReal` is real analytic -/
lemma Complex.contDiff_ofReal : ContDiff ℝ ω Complex.ofReal := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply Complex.contDiffAt_ofReal

/-- Complex `norm` is real analytic -/
lemma Complex.analyticAt_norm {z : ℂ} (z0 : z ≠ 0) : AnalyticAt ℝ (fun z : ℂ ↦ ‖z‖) z :=
  (contDiffAt_norm (𝕜 := ℝ) z0).analyticAt

/-- Complex `norm` is real analytic -/
lemma AnalyticAt.norm {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜 ℂ] [NormedSpace ℝ E] {f : E → ℂ} {x : E} (a : AnalyticAt 𝕜 f x) (f0 : f x ≠ 0) :
    AnalyticAt ℝ (fun x ↦ ‖f x‖) x :=
  (Complex.analyticAt_norm f0).comp a.restrictScalars

/-- A complex derivative, treated as `ℂ →L[ℝ] → ℂ` -/
lemma Complex.real_hasFDerivAt {f : ℂ → ℂ} {z : ℂ} {f' : ℂ} (h : HasDerivAt f f' z) :
    HasFDerivAt f (lsmul ℝ ℂ f') z := by
  convert h.hasFDerivAt.restrictScalars ℝ
  all_goals try rfl
  ext
  exact mul_comm _ _

/-- The derivative of `.im` -/
lemma hasFDerivAt_im {z : ℂ} : HasFDerivAt Complex.im imCLM z := by
  have e : Complex.im = (fun z ↦ imCLM z) := by ext z; simp only [Complex.imCLM_apply]
  rw [e]; apply ContinuousLinearMap.hasFDerivAt

/-- The derivative of `arg`, via `log` -/
lemma hasFDerivAt_arg {z : ℂ} (m : z ∈ slitPlane) :
    HasFDerivAt arg (imCLM ∘L lsmul ℝ ℂ z⁻¹) z := by
  have e : arg = (fun z ↦ (log z).im) := by ext z; rw [Complex.log_im]
  rw [e]
  exact HasFDerivAt.comp _ hasFDerivAt_im (Complex.real_hasFDerivAt (Complex.hasDerivAt_log m))

/-- The derivative of `arg` along a curve -/
lemma HasDerivAt.arg {p : ℝ → ℂ} {p' : ℂ} {t : ℝ} (h : HasDerivAt p p' t)
    (m : p t ∈ slitPlane) : HasDerivAt (fun t ↦ arg (p t)) ((p t)⁻¹ * p').im t := by
  convert ((hasFDerivAt_arg m).comp t h.hasFDerivAt).hasDerivAt
  all_goals try rfl
  simp

/-!
### Determinants of complex derivatives
-/

@[simp] lemma Complex.algebra_norm (z : ℂ) : Algebra.norm ℝ (z : ℂ) = ‖z‖ ^ 2 := by
  simp [Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

/-- If `f` is complex differentiable at a point, it's `fderiv` determinant is clean -/
lemma Complex.fderiv_det {f : ℂ → ℂ} {z : ℂ} (df : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2 := by
  have d1 := df.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have d2 := (df.restrictScalars ℝ).hasFDerivAt
  rw [d2.unique d1]
  simp [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, Complex.algebra_norm,
    LinearMap.det_restrictScalars, LinearMap.det_ring, smul_eq_mul, one_mul]

end
end Ray_Ray_Misc_Complex

-- ===== Ray.Misc.Circle =====
section Ray_Ray_Misc_Circle
/-!
## `Circle` facts
-/

open Classical
open Complex (arg exp I slitPlane)
open Metric (sphere)
open Set
open scoped Real ComplexConjugate
noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- `-z = Circle.exp π * z` (Mathlib now provides `Neg Circle` and `HasDistribNeg Circle`) -/
lemma Circle.neg_def (z : Circle) : -z = Circle.exp π * z := by
  apply Circle.ext
  simp only [Circle.coe_neg, Circle.coe_mul, Circle.coe_exp, Complex.exp_pi_mul_I, neg_one_mul]

@[simp] lemma Circle.neg_ne (z : Circle) : -z ≠ z := Circle.neg_ne_self z

lemma Circle.arg_neg_one : arg (-1 : Circle).val = π := by
  simp only [Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one]

@[simp] lemma Circle.mem_slitPlane (z : Circle) : z.val ∈ slitPlane ↔ z ≠ -1 := by
  simp only [Complex.mem_slitPlane_iff_arg, ne_eq, Circle.ext_iff, Complex.ext_norm_arg_iff,
    norm_zero, Complex.arg_zero, Circle.norm_coe, true_and, one_ne_zero, false_and, not_false_iff,
    and_true, coe_neg, norm_neg, Circle.coe_one, Complex.arg_neg_one, norm_one]

@[fun_prop] lemma Continuous.circle_exp {f : X → ℝ} (fc : Continuous f) :
    Continuous (fun x ↦ Circle.exp (f x)) := by fun_prop

instance : Inhabited Circle where
  default := 1

instance : Nonempty Circle := by infer_instance

instance : Infinite Circle := by
  rw [Circle.argEquiv.infinite_iff]
  apply Set.Infinite.to_subtype
  exact Ioc_infinite (by linarith [Real.pi_pos])

-- Courtesy of Junyan Xu, see https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/No.20continuous.2C.20injective.20maps.20.60Circle.20.E2.86.92.20.E2.84.9D.20.60/near/534054211
lemma AddCircle.isConnected_compl_singleton {T : ℝ} [h : Fact (0 < T)]
    (s : AddCircle T) : IsConnected {s}ᶜ := by
  obtain ⟨s⟩ := s
  have := isConnected_iff_connectedSpace.mp
    (isConnected_Ioo <| show s < s + T by linarith [h.out])
  have : Set.Ioo s (s + T) ≃ₜ _ :=
    (AddCircle.openPartialHomeomorphCoe T s).toHomeomorphSourceTarget
  exact isConnected_iff_connectedSpace.mpr <|
    this.surjective.connectedSpace this.continuous

-- Courtesy of Junyan Xu, see https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/No.20continuous.2C.20injective.20maps.20.60Circle.20.E2.86.92.20.E2.84.9D.20.60/near/534054211
lemma Circle.isConnected_compl_singleton (s : Circle) : IsConnected {s}ᶜ := by
  have e := AddCircle.homeomorphCircle'
  have : Fact (0 < 2 * Real.pi) := ⟨by simp [Real.pi_pos]⟩
  rw [← e.isConnected_preimage]
  convert AddCircle.isConnected_compl_singleton (e.symm s)
  aesop

/-- There are no continuous, injective maps `Circle → ℝ` -/
lemma Circle.not_continuous_or_not_injective {f : Circle → ℝ} (cont : Continuous f)
    (inj : f.Injective) : False := by
  obtain ⟨a,_,lo⟩ := isCompact_univ.exists_isMinOn univ_nonempty cont.continuousOn
  obtain ⟨b,_,hi⟩ := isCompact_univ.exists_isMaxOn univ_nonempty cont.continuousOn
  simp only [isMinOn_iff, mem_univ, forall_const, isMaxOn_iff] at lo hi
  by_cases ab : f a = f b
  · have e : ∀ x y, f x = f y := by intro x y; linarith [lo x, hi x, lo y, hi y]
    specialize e (-1) 1
    simp only [inj.eq_iff, neg_ne] at e
  · replace ab : f a < f b := Ne.lt_of_le ab (lo b)
    obtain ⟨x,m⟩ := Infinite.exists_notMem_finset {a, b}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at m
    have ax : f a < f x := (inj.ne_iff.mpr m.1).symm.lt_of_le (lo x)
    have xb : f x < f b := (inj.ne_iff.mpr m.2).lt_of_le (hi x)
    have connect : (f '' {x}ᶜ).OrdConnected :=
      ((Circle.isConnected_compl_singleton x).image _ cont.continuousOn).isPreconnected.ordConnected
    have mem := connect.out (x := f a) (y := f b) (by aesop) (by aesop) ⟨ax.le, xb.le⟩
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, inj.eq_iff, not_and_self,
      exists_const] at mem

/-- If `f : Circle → Circle` is continuous and injective, it is surjective -/
lemma Circle.surjective_of_injective {f : Circle → Circle} (cont : Continuous f)
    (inj : f.Injective) : f.Surjective := by
  intro c
  by_contra s
  simp only [not_exists] at s
  set g : Circle → ℝ := fun z ↦ arg (f z / -c : Circle)
  have gc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    refine (Complex.continuousAt_arg ?_).comp (by fun_prop)
    simp only [Circle.mem_slitPlane, ne_eq, div_eq_iff_eq_mul', neg_mul_neg, mul_one, s,
      not_false_eq_true]
  have gi : g.Injective := Circle.injective_arg.comp (div_left_injective.comp inj)
  exact Circle.not_continuous_or_not_injective gc gi

/-- If `f : Circle → Circle` is continuous and injective, it is a homeomorphism -/
lemma Circle.isHomeomorph_of_injective {f : Circle → Circle} (cont : Continuous f)
    (inj : f.Injective) : IsHomeomorph f := by
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨cont, inj, surjective_of_injective cont inj⟩

@[simp] lemma Complex.conj_circleMap {c : ℂ} {r : ℝ} {t : ℝ} :
    conj (circleMap c r t) = circleMap (conj c) r (-t) := by
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_neg,
    neg_mul, ← Complex.exp_conj, Complex.conj_I, mul_neg]

/-- Only diagonal expoential integrals survive -/
lemma integral_exp_mul_I (n : ℤ) :
    ∫ t in -π..π, exp (n * t * I) = if n = 0 then 2 * π else 0 := by
  by_cases n0 : n = 0
  · simp [n0, two_mul]
  · have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ exp (n * t * I)) (n * I * exp (n * t * I)) t := by
      intro t
      simp only [← mul_assoc, mul_comm _ I]
      generalize I * n = c
      simp only [mul_comm c]
      apply HasDerivAt.cexp
      nth_rw 2 [← (by simp : (1 : ℝ) * c = c)]
      exact (hasDerivAt_id t).ofReal_comp.mul_const _
    have d : deriv (fun t : ℝ ↦ exp (n * t * I) / (n * I)) = fun t : ℝ ↦ exp (n * t * I) := by
      ext t
      rw [deriv_div_const, (hd t).deriv, mul_div_cancel_left₀ _ (by simp [n0])]
    rw [intervalIntegral.integral_deriv_eq_sub' (E := ℂ) _ d (a := -π) (b := π)]
    · simp only [n0, if_false, mul_assoc, Complex.exp_int_mul, Complex.ofReal_neg, neg_mul,
        Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, sub_self, Complex.ofReal_zero]
    · exact fun t _ ↦ (hd t).differentiableAt.div_const _
    · fun_prop

/-- `circleMap` is continuous on `ℝ × ℝ` -/
@[fun_prop] theorem continuous_circleMap_full {c : ℂ} :
    Continuous fun x : ℝ × ℝ ↦ circleMap c x.1 x.2 := by
  continuity

/-- `circleMap` is analytic in `t` -/
@[fun_prop] theorem analyticAt_circleMap {c : ℂ} {r t : ℝ} : AnalyticAt ℝ (circleMap c r) t := by
  unfold circleMap
  refine analyticAt_const.add (analyticAt_const.mul (analyticAt_cexp.restrictScalars.comp ?_))
  exact Complex.analyticAt_ofReal.mul analyticAt_const

/-- The derivative of `circleMap` w.r.t. the radius -/
lemma HasDerivAt.circleMap_radius {c : ℂ} {r t : ℝ} :
    HasDerivAt (fun r ↦ circleMap c r t) (circleMap 0 1 t) r := by
  simp only [circleMap, zero_add]
  exact ((hasDerivAt_id _).ofReal_comp.mul_const _).const_add _

/-- `circleMap` is surjective from `|t| ≤ π` -/
lemma exists_circleMap_le {r : ℝ} {z : ℂ} (m : ‖z‖ = r) :
    ∃ t, |t| ≤ π ∧ circleMap 0 r t = z := by
  replace m : z ∈ sphere 0 |r| := by simp [← m]
  simp only [← image_circleMap_Ioc, mem_image, mem_Ioc] at m
  obtain ⟨t,⟨t0,t1⟩,tz⟩ := m
  by_cases t0 : t ≤ π
  · exact ⟨t, abs_le.mpr ⟨by linarith, by linarith⟩, tz⟩
  · refine ⟨t - 2 * π, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
    simp only [circleMap, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, sub_mul,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one, zero_add, ← tz]

lemma abs_le_mul_norm_circleMap {t : ℝ} (m : |t| ≤ π) :
    |t| ≤ π/2 * ‖circleMap 0 1 t - 1‖ := by
  suffices h : t ^ 2 ≤ π ^ 2 / 2 ^ 2 * Complex.normSq (circleMap 0 1 t - 1) by
    rw [← sq_le_sq₀ (by bound) (by bound)]
    simp only [sq_abs, Complex.norm_def, mul_pow, div_pow]
    rwa [Real.sq_sqrt (by bound)]
  rw [mul_comm, ← div_le_iff₀ (by bound)]
  simp only [circleMap, Complex.exp_mul_I, Complex.normSq_apply, Complex.sub_re,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_self,
    add_zero, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, one_mul,
    Complex.one_im, sub_zero, Complex.ofReal_re, Complex.ofReal_im, ← pow_two, zero_mul,
    Complex.cos_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
    zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  simp only [sub_sq, mul_one, one_pow, Real.cos_sq']
  ring_nf
  have b := Real.cos_le_one_sub_mul_cos_sq m
  rw [inv_pow, ← div_eq_mul_inv, div_mul_eq_mul_div, mul_div_assoc, mul_comm (t^2)]
  rw [div_mul_eq_mul_div, mul_div_assoc] at b ⊢
  linarith [b]

end
end Ray_Ray_Misc_Circle

-- ===== Ray.Misc.Prod =====
section Ray_Ray_Misc_Prod
/-!
## Lemmas about `A × B`
-/

open Function (uncurry curry)
open Prod (swap)
open Metric (ball)
open scoped Topology
noncomputable section

variable {A B C : Type}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- `swap` is an involution -/
theorem swap_swap (s : Set (A × B)) : swap '' (swap '' s) = s := by
  ext x; simp only [Set.mem_image, Prod.exists]; constructor
  · intro ⟨a,b,⟨⟨c,d,e,f⟩,g⟩⟩; rw [←g, ←f]; simpa only [swap]
  · intro m; exact ⟨x.2,x.1,⟨x.1,x.2,m,rfl⟩,rfl⟩

theorem flip_swap (f : A → B → C) : uncurry (flip f) = uncurry f ∘ swap := rfl

theorem differentiable_swap [NormedAddCommGroup A] [NormedAddCommGroup B] [NormedSpace 𝕜 A]
    [NormedSpace 𝕜 B] : Differentiable 𝕜 (swap : A × B → B × A) := fun _ ↦
  DifferentiableAt.prodMk (differentiable_snd _) (differentiable_fst _)

theorem differentiableOn_swap {s : Set (A × B)} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [NormedSpace 𝕜 A] [NormedSpace 𝕜 B] : DifferentiableOn 𝕜 swap s :=
  differentiable_swap.differentiableOn

/-- `swap` is an open map -/
theorem isOpen_swap {s : Set (A × B)} [TopologicalSpace A] [TopologicalSpace B] :
    IsOpen s → IsOpen (swap '' s) := by
  rw [Set.image_swap_eq_preimage_swap]; exact IsOpen.preimage continuous_swap

theorem swap_mem {a : A} {b : B} {s : Set (A × B)} : (b, a) ∈ swap '' s ↔ (a, b) ∈ s := by
  aesop

theorem swap_mem' {x : A × B} {s : Set (B × A)} : x ∈ swap '' s ↔ swap x ∈ s := by
  have h := @swap_mem _ _ x.snd x.fst s; simp at h ⊢; exact h

theorem ball_prod_same' [PseudoMetricSpace A] [PseudoMetricSpace B] (x : A × B) (r : ℝ) :
    ball x r = ball x.fst r ×ˢ ball x.snd r := by
  have s := ball_prod_same x.fst x.snd r
  simp only [Prod.mk.eta] at s; exact s.symm

theorem ball_swap [PseudoMetricSpace A] [PseudoMetricSpace B] {x : A × B} {r : ℝ} :
    ball x.swap r = swap '' ball x r := by
  apply Set.ext; intro y
  rw [swap_mem', Metric.mem_ball, Metric.mem_ball, Prod.dist_eq, Prod.dist_eq]
  simp only [max_lt_iff, Prod.fst_swap, Prod.snd_swap, and_comm]

theorem dist_swap [PseudoMetricSpace A] [PseudoMetricSpace B] {x y : A × B} :
    dist x.swap y.swap = dist x y := by
  rw [Prod.dist_eq, Prod.dist_eq]; simp only [Prod.fst_swap, Prod.snd_swap, max_comm]

end
end Ray_Ray_Misc_Prod

-- ===== Ray.Hartogs.FubiniBall =====
section Ray_Ray_Hartogs_FubiniBall
/-!
## Fubini's theorem for integration over the complex closed disk

We rewrite integration over the closed disk in polar coordinates, so that we can relate
disk integrals to `intervalIntegral`s of `circleIntegral`s.

We extend the result for annuli as well, since we use that for the Koebe quarter theorem.
-/

open Complex (arg exp I)
open LinearMap (toMatrix_apply)
open MeasureTheory
open Metric (ball closedBall sphere)
open Module (Basis)
open Real (cos sin)
open Set
open scoped Real
noncomputable section

namespace RealCircleMap

/-- `circleMap` as a map from `ℝ² → ℝ²` -/
def realCircleMap (c : ℂ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ⟨c.re + x.1 * cos x.2, c.im + x.1 * sin x.2⟩

lemma realCircleMap_eq_circleMap (c : ℂ) (x : ℝ × ℝ) :
    realCircleMap c x = Complex.equivRealProd (circleMap c x.1 x.2) := by
  simp only [realCircleMap, circleMap, Complex.equivRealProd_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
    zero_mul, sub_zero, Complex.add_im, Complex.mul_im, add_zero]

/-- Abbreviation for the `fst` continuous linear map -/
abbrev d1 := ContinuousLinearMap.fst ℝ ℝ ℝ
/-- Abbreviation for the `snd` continuous linear map -/
abbrev d2 := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The derivative of `realCircleMap` -/
def rcmDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (0 + (x.1 • -sin x.2 • d2 + cos x.2 • d1)).prod (0 + (x.1 • cos x.2 • d2 + sin x.2 • d1))

lemma realCircleMap.fderiv {c : ℂ} {x : ℝ × ℝ} :
    HasFDerivAt (fun x ↦ realCircleMap c x) (rcmDeriv x) x := by
  simp_rw [realCircleMap]
  apply_rules [hasFDerivAt_const, hasFDerivAt_fst, hasFDerivAt_snd, HasFDerivAt.cos,
    HasFDerivAt.sin, HasFDerivAt.add, HasFDerivAt.mul, HasFDerivAt.prodMk]

/-- The Jacobian matrix of `realCircleMap` -/
def rcmMatrix (x : ℝ × ℝ) :=
  LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) (rcmDeriv x)
lemma rcm00 (x : ℝ × ℝ) : rcmMatrix x 0 0 = cos x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]
lemma rcm01 (x : ℝ × ℝ) : rcmMatrix x 0 1 = -x.1 * sin x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]
lemma rcm10 (x : ℝ × ℝ) : rcmMatrix x 1 0 = sin x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]
lemma rcm11 (x : ℝ × ℝ) : rcmMatrix x 1 1 = x.1 * cos x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]

/-- The Jacobian determinant of `realCircleMap` -/
lemma rcmDeriv.det (x : ℝ × ℝ) : (rcmDeriv x).det = x.1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), ←rcmMatrix]
  rw [Matrix.det_fin_two, rcm00, rcm01, rcm10, rcm11]; ring_nf
  calc cos x.2 ^ 2 * x.1 + x.1 * sin x.2 ^ 2
    _ = x.1 * (cos x.2 ^ 2 + sin x.2 ^ 2) := by ring
    _ = x.1 := by simp only [Real.cos_sq_add_sin_sq, mul_one]

end RealCircleMap

namespace FubiniHelper
open RealCircleMap

/-- The square that we'll map onto the ball -/
def square (r0 r1 : ℝ) : Set (ℝ × ℝ) :=
  Ioc r0 r1 ×ˢ Ioc 0 (2 * π)

theorem square.rp {r0 r1 : ℝ} {x : ℝ × ℝ} (r0p : 0 ≤ r0) : x ∈ square r0 r1 → 0 < x.1 := by
  simp only [square, mem_prod, mem_Ioc, and_imp]
  intro h _ _ _; linarith

theorem Measurable.square {r0 r1 : ℝ} : MeasurableSet (square r0 r1) := by
  apply_rules [MeasurableSet.prod, measurableSet_Ioc]

theorem square_eq {c : ℂ} {r0 r1 : ℝ} (r0p : 0 ≤ r0) :
    Complex.measurableEquivRealProd.symm ⁻¹' (annulus_oc c r0 r1) =
      realCircleMap c '' square r0 r1 := by
  rw [← MeasurableEquiv.image_eq_preimage_symm]
  have e : realCircleMap c =
      fun x : ℝ × ℝ ↦ Complex.measurableEquivRealProd (circleMap c x.1 x.2) := by
    funext
    simp only [realCircleMap_eq_circleMap, Complex.measurableEquivRealProd,
      Complex.equivRealProd_apply, Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_apply]
  have i : (fun x : ℝ × ℝ ↦ circleMap c x.1 x.2) '' square r0 r1 = annulus_oc c r0 r1 := by
    ext z
    rw [mem_image]
    constructor
    · intro gp
      rcases gp with ⟨⟨s, t⟩, ss, tz⟩
      simp only at tz
      simp only [square, prodMk_mem_set_prod_eq, mem_Ioc] at ss
      rw [← tz]
      have s0 : 0 < s := by linarith
      simp only [circleMap, add_comm c, annulus_oc, mem_sdiff, Metric.mem_closedBall,
        dist_add_self_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I, mul_one, not_le, abs_of_pos s0, ss.1, true_and]
    · intro zr
      simp only [mem_sdiff, Metric.mem_closedBall, annulus_oc, not_le] at zr
      rw [dist_comm] at zr
      have zz : z ∈ sphere c (dist c z) := by
        simp only [Complex.dist_eq, mem_sphere_iff_norm, norm_sub_rev]
      rcases circleMap_Ioc zz with ⟨t, ts, tz⟩
      use (dist c z, t)
      simpa only [square, gt_iff_lt, not_lt, ge_iff_le, zero_lt_two, mul_pos_iff_of_pos_left,
        mem_prod, mem_Ioc, dist_pos, ne_eq, not_false_eq_true, zr, and_self, true_and,
        tz.symm, and_true] using ts
  have im := image_comp Complex.measurableEquivRealProd (fun x : ℝ × ℝ ↦ circleMap c x.1 x.2)
    (square r0 r1)
  simp only [Function.comp] at im
  simp only [e, im, i]

/-- `exp (t * I) = cos t + sin t * I` -/
theorem exp_of_im (t : ℝ) : exp (t * I) = cos t + sin t * I := by
  simp [Complex.ext_iff, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem Complex.cos_eq_cos (t : ℝ) : Complex.cos t = ↑(Real.cos t) := by simp

theorem Complex.sin_eq_sin (t : ℝ) : Complex.sin t = ↑(Real.sin t) := by simp

/-- The argument of `exp (t * I)` -/
theorem arg_exp_of_im (t : ℝ) : ∃ n : ℤ, arg (exp (t * I)) = t - 2 * π * n := by
  generalize hn : ⌈t / (2 * π) - 1 / 2⌉ = n; exists n
  have en : exp (2 * π * n * I) = 1 := by
    rw [mul_comm _ (n:ℂ), mul_assoc, Complex.exp_int_mul]
    simp only [Complex.exp_two_pi_mul_I, one_zpow]
  have e : exp (t * I) = exp (↑(t - 2 * π * n) * I) := by
    simp [mul_sub_right_distrib, Complex.exp_sub, en]
  have ts : t - 2 * π * n ∈ Ioc (-π) π := by
    simp only [mem_Ioc, neg_lt_sub_iff_lt_add, tsub_le_iff_right]
    constructor
    · have h : ↑n < t * (2 * π)⁻¹ - 1 / 2 + 1 := by rw [← hn]; exact Int.ceil_lt_add_one _
      calc 2 * π * ↑n
        _ < 2 * π * (t * (2 * π)⁻¹ - 1 / 2 + 1) := by bound
        _ = π + 2 * π * (2 * π)⁻¹ * t := by ring
        _ = π + t := by field_simp [Real.two_pi_pos.ne']
    · have h : ↑n ≥ t * (2 * π)⁻¹ - 1 / 2 := by rw [← hn]; exact Int.le_ceil _
      calc π + 2 * π * ↑n
        _ ≥ π + 2 * π * (t * (2 * π)⁻¹ - 1 / 2) := by bound
        _ = 2 * π * (2 * π)⁻¹ * t := by ring
        _ = t := by field_simp [Real.two_pi_pos.ne']
  rw [e, exp_of_im, ← Complex.cos_eq_cos, ← Complex.sin_eq_sin, Complex.arg_cos_add_sin_mul_I ts]

/-- `realCircleMap` is injective on the square -/
theorem rcm_inj {c : ℂ} {r0 r1 : ℝ} (r0p : 0 ≤ r0) : InjOn (realCircleMap c) (square r0 r1) := by
  intro x xs y ys e; simp [square] at xs ys
  simp_rw [realCircleMap_eq_circleMap, Equiv.apply_eq_iff_eq] at e
  simp_rw [circleMap] at e; simp at e
  have re : ‖↑x.1 * exp (x.2 * I)‖ = ‖↑y.1 * exp (y.2 * I)‖ := by rw [e]
  have x0 : 0 < x.1 := by linarith
  have y0 : 0 < y.1 := by linarith
  simp only [norm_mul, Complex.norm_real, abs_of_pos x0, Complex.norm_exp_ofReal_mul_I, mul_one,
    abs_of_pos y0, Real.norm_eq_abs] at re
  have ae : arg (↑x.1 * exp (x.2 * I)) = arg (↑y.1 * exp (y.2 * I)) := by rw [e]
  simp [Complex.arg_real_mul _ x0, Complex.arg_real_mul _ y0] at ae
  rcases arg_exp_of_im x.2 with ⟨nx, hx⟩
  rcases arg_exp_of_im y.2 with ⟨ny, h⟩
  rw [← ae, hx] at h; clear e ae hx
  have n0 : 2 * π * (nx - ny) < 2 * π * 1 := by linarith
  have n1 : 2 * π * -1 < 2 * π * (nx - ny) := by linarith
  have hn : (nx : ℝ) - ny = ↑(nx - ny) := by simp only [Int.cast_sub]
  have hn1 : (-1 : ℝ) = ↑(-1 : ℤ) := by norm_num
  have h1 : (1 : ℝ) = ↑(1 : ℤ) := by norm_num
  rw [mul_lt_mul_iff_right₀ Real.two_pi_pos, hn] at n0 n1
  rw [hn1] at n1; rw [h1] at n0; rw [Int.cast_lt] at n0 n1
  have n : nx = ny := by linarith
  rw [n] at h
  have i : x.2 = y.2 := by linarith
  have g : (x.1, x.2) = (y.1, y.2) := by rw [re, i]
  simp only [Prod.mk.eta] at g; exact g

end FubiniHelper
open RealCircleMap
open FubiniHelper

/-- Inverse lemma for fubini_ball -/
theorem measurable_symm_equiv_inverse {z : ℂ} :
    Complex.measurableEquivRealProd.symm (Complex.equivRealProd z) = z := by
  simp only [Complex.equivRealProd_apply]
  rw [Complex.measurableEquivRealProd, Homeomorph.toMeasurableEquiv_symm_coe]
  simp only [ContinuousLinearEquiv.coe_symm_toHomeomorph]
  apply Complex.ext; · simp only [Complex.equivRealProdCLM_symm_apply_re]
  · simp only [Complex.equivRealProdCLM_symm_apply_im]

/-- Integration over a complex annulus using polar coordinates -/
theorem fubini_annulus {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {r0 r1 : ℝ} (fc : ContinuousOn f (annulus_cc c r0 r1)) (r0p : 0 ≤ r0) :
    ∫ z in annulus_oc c r0 r1, f z =
      ∫ s in Ioc r0 r1, s • ∫ t in Ioc 0 (2 * π), f (circleMap c s t) := by
  have im := MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod
  rw [← MeasurePreserving.setIntegral_preimage_emb im
    Complex.measurableEquivRealProd.symm.measurableEmbedding f _]
  clear im
  rw [square_eq r0p]
  have dc : ∀ x, x ∈ square r0 r1 →
      HasFDerivWithinAt (realCircleMap c) (rcmDeriv x) (square r0 r1) x :=
    fun _ _ ↦ realCircleMap.fderiv.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume Measurable.square dc (rcm_inj r0p)]
  clear dc
  simp_rw [rcmDeriv.det]
  simp_rw [realCircleMap_eq_circleMap]
  simp_rw [measurable_symm_equiv_inverse]
  have e : ∀ x : ℝ × ℝ, x ∈ square r0 r1 → |x.1| • f (circleMap c x.1 x.2) =
      x.1 • f (circleMap c x.1 x.2) := by
    intro x xs; rw [abs_of_pos (square.rp r0p xs)]
  rw [MeasureTheory.setIntegral_congr_fun Measurable.square e]; clear e
  rw [square, Measure.volume_eq_prod, MeasureTheory.setIntegral_prod]
  simp [integral_smul]
  have fi : IntegrableOn (fun x : ℝ × ℝ ↦ x.1 • f (circleMap c x.1 x.2))
      (Icc r0 r1 ×ˢ Icc 0 (2 * π)) := by
    apply ContinuousOn.integrableOn_compact
    · exact IsCompact.prod isCompact_Icc isCompact_Icc
    · apply ContinuousOn.smul continuous_fst.continuousOn
      apply fc.comp continuous_circleMap_full.continuousOn
      intro x xs
      simp only [Icc_prod_Icc, mem_Icc, Prod.le_def] at xs
      have x0 : 0 ≤ x.1 := by linarith
      simp only [circleMap, annulus_cc, mem_sdiff, Metric.mem_closedBall, dist_self_add_left,
        norm_mul, Complex.norm_real, abs_of_nonneg x0, Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I, mul_one, xs.2.1, Metric.mem_ball, not_lt, xs.1.1, and_self]
  exact fi.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Integration over a complex ball using polar coordinates -/
theorem fubini_ball {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {r : ℝ} (fc : ContinuousOn f (closedBall c r)) :
    ∫ z in closedBall c r, f z =
      ∫ s in Ioc 0 r, s • ∫ t in Ioc 0 (2 * π), f (circleMap c s t) := by
  have center : closedBall c r =ᵐ[volume] (closedBall c r \ {c} : Set ℂ) := ae_minus_point
  rw [MeasureTheory.setIntegral_congr_set center]; clear center
  rw [← Metric.closedBall_zero, ← annulus_oc]
  apply fubini_annulus
  · simpa only [annulus_cc, Metric.ball_zero, sdiff_empty]
  · rfl

/-- The volume of the complex closed ball is `π r^2` -/
theorem Complex.volume_closedBall' {c : ℂ} {r : ℝ} (rp : 0 ≤ r) :
    volume.real (closedBall c r) = π * r ^ 2 := by
  have c : ContinuousOn (fun _ : ℂ ↦ (1 : ℝ)) (closedBall c r) := continuousOn_const
  have f := fubini_ball c; clear c
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
    smul_eq_mul, mul_one, Real.volume_real_Ioc, sub_zero, max_eq_left Real.two_pi_pos.le, ←
    intervalIntegral.integral_of_le rp, intervalIntegral.integral_mul_const, integral_id, Ne,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at f
  ring_nf at f ⊢
  exact f

/-- `closedBall` with positive radius has positive, nonzero volume -/
theorem NiceVolume.closedBall (c : ℂ) {r : ℝ} (rp : 0 < r) :
    NiceVolume (closedBall c r) where
  measurable := measurableSet_closedBall
  finite := by
    simp only [Complex.volume_closedBall]
    apply ENNReal.mul_lt_top
    · exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
    · exact ENNReal.coe_lt_top
  pos := by
    simp only [Complex.volume_closedBall, gt_iff_lt, CanonicallyOrderedAdd.mul_pos,
      ENNReal.coe_pos, NNReal.pi_pos, and_true]
    apply ENNReal.pow_pos
    bound

/-- `closedBall` with positive radius has positive volume near each point -/
theorem LocalVolume.closedBall {c : ℂ} {r : ℝ} (rp : r > 0) :
    LocalVolumeSet (closedBall c r) := by
  apply LocalVolume.closure_interior
  · intro x r rp
    simp only [Complex.volume_ball, gt_iff_lt, CanonicallyOrderedAdd.mul_pos, ENNReal.coe_pos,
      NNReal.pi_pos, and_true]
    apply ENNReal.pow_pos
    bound
  · have rz := rp.ne'
    simp only [interior_closedBall c rz, closure_ball c rz, subset_refl]

end
end Ray_Ray_Hartogs_FubiniBall

-- ===== Ray.Misc.Max =====
section Ray_Ray_Misc_Max
/-!
## Lemmas about `max` and `partialSups`
-/

open Set (univ)
noncomputable section

/-- `max` is continuous, `ContinuousOn` comp version -/
theorem ContinuousOn.max {A : Type} [TopologicalSpace A] {f g : A → ℝ} {s : Set A}
    (fc : ContinuousOn f s) (gc : ContinuousOn g s) : ContinuousOn (fun x ↦ max (f x) (g x)) s :=
  continuous_max.comp_continuousOn (fc.prodMk gc)

/-- `max` is convex -/
theorem convexOn_max : ConvexOn ℝ univ (fun p : ℝ × ℝ ↦ max p.1 p.2) := by
  apply ConvexOn.sup; · use convex_univ; intros; simp
  · use convex_univ; intros; simp

/-- `partialSups` is continuous -/
theorem ContinuousOn.rayPartialSups {A : Type} [TopologicalSpace A] {f : ℕ → A → ℝ} {s : Set A}
    (fc : ∀ n, ContinuousOn (f n) s) (n : ℕ) :
    ContinuousOn (fun x ↦ partialSups (fun k ↦ f k x) n) s := by
  induction' n with n h
  · simp only [partialSups_zero, fc 0]
  · simp only [← Order.succ_eq_add_one, partialSups_succ]
    exact ContinuousOn.max h (fc _)

end
end Ray_Ray_Misc_Max


