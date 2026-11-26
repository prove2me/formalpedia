-- Prove2me | solution 1 for Auto.multilinear_interpolation_two_endpoint_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:49.890221+00:00
-- url     : https://prove2.me/submissions/3513474f-f285-428e-b3c6-7ca99fa0df34

module
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Definitions.Def_LeanNct_Auto_MultilinearInterpolation
public import Theorems.Thm_Auto_aux_multilinear_interpolation_two_endpoint_normalized
section
@[expose] public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
namespace Auto
private theorem diffContOnCl_const_mul_exp_affine
    (a b c : ℂ) (s : Set ℂ) :
    DiffContOnCl ℂ (fun z ↦ c * Complex.exp (a * z + b)) s := by
  apply Differentiable.diffContOnCl
  exact
    ((Complex.differentiable_exp.comp
      ((differentiable_id.const_mul a).add_const b)).const_mul c)
private theorem diffContOnCl_input_deformation_coeff
    {a₀ a₁ : ℝ} (c : ℂ) (U : Set ℂ) :
    DiffContOnCl ℂ (fun z ↦ if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))) U := by
  by_cases hc : c = 0
  · simpa [hc] using (diffContOnCl_const (𝕜 := ℂ) (s := U) (c := (0 : ℂ)))
  · simp only [if_neg hc]
    convert diffContOnCl_const_mul_exp_affine
      (((a₁ - a₀ : ℝ) : ℂ) * ((Real.log ‖c‖ : ℝ) : ℂ))
      ((a₀ : ℂ) * ((Real.log ‖c‖ : ℝ) : ℂ))
      (c / (‖c‖ : ℂ)) U using 1
    funext z
    congr 2
    ring
private theorem rpow_affine_le_max_one
    {r a₀ a₁ x : ℝ} (hr : 0 ≤ r) (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hx : x ∈ Set.Icc 0 1) :
    r ^ (a₀ + x * (a₁ - a₀)) ≤ max 1 (r ^ max a₀ a₁) := by
  have he_nonneg : 0 ≤ a₀ + x * (a₁ - a₀) := by
    rcases le_total a₀ a₁ with h | h
    · have : 0 ≤ x * (a₁ - a₀) := mul_nonneg hx.1 (sub_nonneg.mpr h)
      linarith
    · have h' : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
      have hrewrite : a₀ + x * (a₁ - a₀) = x * a₁ + (1 - x) * a₀ := by ring
      rw [hrewrite]
      exact add_nonneg (mul_nonneg hx.1 ha₁) (mul_nonneg h' ha₀)
  have he_le : a₀ + x * (a₁ - a₀) ≤ max a₀ a₁ := by
    rcases le_total a₀ a₁ with h | h
    · rw [max_eq_right h]
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr h),
        mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h)]
    · rw [max_eq_left h]
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr h),
        mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr h)]
  rcases le_total r 1 with hr1 | hr1
  · exact (Real.rpow_le_one hr hr1 he_nonneg).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le hr1 he_le).trans (le_max_right _ _)
private theorem norm_input_deformation_coeff_uniform
    {a₀ a₁ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (c z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) :
    ‖if c = 0 then 0 else
      c / (‖c‖ : ℂ) * Complex.exp
        ((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
          ((Real.log ‖c‖ : ℝ) : ℂ))‖ ≤
      max 1 (‖c‖ ^ max a₀ a₁) := by
  by_cases hc : c = 0
  · simp [hc]
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hre : z.re ∈ Set.Icc 0 1 := hz
  have hpow := rpow_affine_le_max_one (r := ‖c‖) (norm_nonneg c) ha₀ ha₁ hre
  rw [if_neg hc, norm_mul, norm_div, Complex.norm_exp]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [div_self hcn.ne', one_mul]
  have hreal :
      (((((a₁ - a₀ : ℝ) : ℂ) * z + (a₀ : ℂ)) *
        ((Real.log ‖c‖ : ℝ) : ℂ))).re =
        (a₀ + z.re * (a₁ - a₀)) * Real.log ‖c‖ := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero]
    ring
  rw [hreal]
  calc
    Real.exp ((a₀ + z.re * (a₁ - a₀)) * Real.log ‖c‖) =
        ‖c‖ ^ (a₀ + z.re * (a₁ - a₀)) := by
      rw [Real.rpow_def_of_pos hcn]
      congr 1
      ring
    _ ≤ max 1 (‖c‖ ^ max a₀ a₁) := hpow
private theorem restrict_one_preimage_singleton_apply
    {X : Type*} [MeasurableSpace X] (f : SimpleFunc X ℂ) (c : ℂ) (x : X) :
    ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x = if f x = c then 1 else 0 := by
  rw [SimpleFunc.restrict_apply _ (f.measurableSet_preimage _)]
  by_cases h : f x = c
  · rw [Set.indicator_of_mem (by simpa using h)]
    simp [h]
  · rw [Set.indicator_of_notMem (by simpa using h)]
    simp [h]
private theorem map_eq_sum_smul_restrict
    {X : Type*} [MeasurableSpace X] (f : SimpleFunc X ℂ) (φ : ℂ → ℂ)
    (hφ : φ 0 = 0) :
    f.map φ = ∑ c ∈ f.range.erase 0,
      φ c • (SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c}) := by
  classical
  ext x
  have hsum_apply (S : Finset ℂ) :
      (∑ c ∈ S, φ c • (SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x =
        ∑ c ∈ S, φ c * ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, SimpleFunc.coe_add,
        SimpleFunc.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih]
  rw [hsum_apply]
  simp_rw [restrict_one_preimage_singleton_apply]
  by_cases hx : f x = 0
  · simp [SimpleFunc.map_apply, hx, hφ]
  · have hmem : f x ∈ f.range.erase 0 := by
      exact Finset.mem_erase.mpr ⟨hx, f.mem_range_self x⟩
    rw [Finset.sum_eq_single (f x)]
    · simp [SimpleFunc.map_apply]
    · intro b hb hne
      have hbx : f x ≠ b := by
        intro h
        exact hne h.symm
      simp [hbx]
    · exact fun h ↦ (h hmem).elim
private theorem integrable_basis_of_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : SimpleFunc X ℂ) (hf : Integrable f μ) {c : ℂ}
    (hc : c ∈ f.range.erase 0) :
    Integrable ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c}) : X → ℂ) μ := by
  have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
  have hfin : μ (f ⁻¹' {c}) < ∞ :=
    (SimpleFunc.integrable_iff_finMeasSupp.mp hf).meas_preimage_singleton_ne_zero hc0
  apply SimpleFunc.FinMeasSupp.integrable
  rw [SimpleFunc.finMeasSupp_iff_support]
  refine lt_of_le_of_lt (measure_mono ?_) hfin
  intro x hx
  by_contra hxc
  have hzero : ((SimpleFunc.const X (1 : ℂ)).restrict (f ⁻¹' {c})) x = 0 := by
    rw [SimpleFunc.restrict_apply _ (f.measurableSet_preimage _)]
    rw [Set.indicator_of_notMem hxc]
  exact hx hzero
private theorem diffContOnCl_finset_sum
    {ι : Type*} (s : Finset ι) (A : ι → ℂ → ℂ) (U : Set ℂ)
    (hA : ∀ i ∈ s, DiffContOnCl ℂ (A i) U) :
    DiffContOnCl ℂ (fun z ↦ ∑ i ∈ s, A i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (diffContOnCl_const (𝕜 := ℂ) (s := U) (c := (0 : ℂ)))
  | insert i s his ih =>
    simp only [Finset.sum_insert his]
    change DiffContOnCl ℂ (A i + fun z ↦ ∑ j ∈ s, A j z) U
    exact (hA i (by simp)).add (ih fun j hj ↦ hA j (by simp [hj]))
private theorem aux_multilinear_pairing_analytic
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    {p₀ p₁ p : Fin (m + 1) → ENNReal}
    (f : SimpleFunc X ℂ) (g : Fin m → SimpleFunc X ℂ) (h : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hh : Integrable (h : Y → ℂ) ν)
    (hpair : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        Integrable (h : Y → ℂ) ν → Integrable (fun y ↦ B u y * h y) ν) :
    DiffContOnCl ℂ (fun z ↦ ∫ y,
      B (Fin.cons f (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i)) y * h y ∂ν)
      (verticalStrip 0 1) := by
  classical
  let S : Fin m → Finset ℂ := fun i ↦ (g i).range.erase 0
  let e : (i : Fin m) → ℂ → SimpleFunc X ℂ := fun i c ↦
    (SimpleFunc.const X (1 : ℂ)).restrict ((g i) ⁻¹' {c})
  let φ : Fin m → ℂ → ℂ → ℂ := fun i z c ↦ if c = 0 then 0 else
    c / (‖c‖ : ℂ) * Complex.exp
      (((((p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal -
            (p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal : ℝ) : ℂ) * z +
          ((p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal : ℝ) : ℂ) *
        ((Real.log ‖c‖ : ℝ) : ℂ))
  let Bf := B.curryLeft f
  have he : ∀ i c, c ∈ S i → Integrable (e i c : X → ℂ) μ := by
    intro i c hc
    exact integrable_basis_of_integrable (g i) (hg i) (by simpa only [S] using hc)
  have hDsum (z : ℂ) (i : Fin m) :
      aux_multilinear_input_deformation p₀ p₁ p g z i =
        ∑ c ∈ S i, φ i z c • e i c := by
    simpa only [S, e, φ, aux_multilinear_input_deformation] using
      (map_eq_sum_smul_restrict (g i) (φ i z) (by simp [φ]))
  have hBsum (z : ℂ) :
      Bf (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) =
        ∑ r ∈ Fintype.piFinset S, Bf (fun i ↦ φ i z (r i) • e i (r i)) := by
    rw [show (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) =
      (fun i ↦ ∑ c ∈ S i, φ i z c • e i c) by funext i; exact hDsum z i]
    exact Bf.map_sum_finset (fun i c ↦ φ i z c • e i c) S
  let H : (∀ i, ℂ) → ℂ := fun r ↦
    ∫ y, Bf (fun i ↦ e i (r i)) y * h y ∂ν
  have hH_integrable : ∀ r ∈ Fintype.piFinset S,
      Integrable (fun y ↦ Bf (fun i ↦ e i (r i)) y * h y) ν := by
    intro r hr
    apply hpair (Fin.cons f (fun i ↦ e i (r i)))
      (fun i ↦ Fin.cases hf (fun j ↦ he j (r j) ((Fintype.mem_piFinset.mp hr) j)) i) hh
  have hF : (fun z ↦ ∫ y,
      B (Fin.cons f (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i)) y * h y ∂ν) =
      fun z ↦ ∑ r ∈ Fintype.piFinset S, (∏ i, φ i z (r i)) * H r := by
    funext z
    change (∫ y, Bf (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) y * h y ∂ν) = _
    rw [hBsum z]
    simp_rw [Finset.sum_apply, Finset.sum_mul]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Bf.map_smul_univ]
      change (∫ y, ((∏ i, φ i z (r i)) • Bf (fun i ↦ e i (r i))) y * h y ∂ν) = _
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      simp only [mul_assoc]
    · intro r hr
      rw [Bf.map_smul_univ]
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (by simpa only [mul_assoc] using
          (hH_integrable r hr).const_mul (∏ i, φ i z (r i)))
  rw [hF]
  apply diffContOnCl_finset_sum (Fintype.piFinset S)
    (fun r z ↦ (∏ i, φ i z (r i)) * H r) (verticalStrip 0 1)
  intro r hr
  have hprod : DiffContOnCl ℂ (fun z ↦ ∏ i, φ i z (r i)) (verticalStrip 0 1) := by
    classical
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => simpa using (diffContOnCl_const (𝕜 := ℂ) (s := verticalStrip 0 1) (c := (1 : ℂ)))
    | insert i s his ih =>
      simpa only [Finset.prod_insert his, smul_eq_mul] using
        (diffContOnCl_input_deformation_coeff (a₀ :=
        (p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal) (a₁ :=
        (p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal) (r i) (verticalStrip 0 1)).smul ih
  simpa only [smul_eq_mul] using hprod.smul
    (diffContOnCl_const (𝕜 := ℂ) (s := verticalStrip 0 1) (c := H r))
private theorem aux_multilinear_pairing_growth
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    {p₀ p₁ p : Fin (m + 1) → ENNReal}
    (f : SimpleFunc X ℂ) (g : Fin m → SimpleFunc X ℂ) (h : SimpleFunc Y ℂ)
    (hf : Integrable (f : X → ℂ) μ) (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hh : Integrable (h : Y → ℂ) ν)
    (hpair : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        Integrable (h : Y → ℂ) ν → Integrable (fun y ↦ B u y * h y) ν) :
    ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
      ‖∫ y, B (Fin.cons f (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i)) y * h y ∂ν‖ ≤
        Real.exp (C * Real.exp (0 * |(z : ℂ).im|)) := by
  classical
  let S : Fin m → Finset ℂ := fun i ↦ (g i).range.erase 0
  let e : (i : Fin m) → ℂ → SimpleFunc X ℂ := fun i c ↦
    (SimpleFunc.const X (1 : ℂ)).restrict ((g i) ⁻¹' {c})
  let φ : Fin m → ℂ → ℂ → ℂ := fun i z c ↦ if c = 0 then 0 else
    c / (‖c‖ : ℂ) * Complex.exp
      (((((p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal -
            (p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal : ℝ) : ℂ) * z +
          ((p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal : ℝ) : ℂ) *
        ((Real.log ‖c‖ : ℝ) : ℂ))
  let Bf := B.curryLeft f
  have he : ∀ i c, c ∈ S i → Integrable (e i c : X → ℂ) μ := by
    intro i c hc
    exact integrable_basis_of_integrable (g i) (hg i) (by simpa only [S] using hc)
  have hDsum (z : ℂ) (i : Fin m) :
      aux_multilinear_input_deformation p₀ p₁ p g z i =
        ∑ c ∈ S i, φ i z c • e i c := by
    simpa only [S, e, φ, aux_multilinear_input_deformation] using
      (map_eq_sum_smul_restrict (g i) (φ i z) (by simp [φ]))
  have hBsum (z : ℂ) :
      Bf (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) =
        ∑ r ∈ Fintype.piFinset S, Bf (fun i ↦ φ i z (r i) • e i (r i)) := by
    rw [show (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) =
      (fun i ↦ ∑ c ∈ S i, φ i z c • e i c) by funext i; exact hDsum z i]
    exact Bf.map_sum_finset (fun i c ↦ φ i z c • e i c) S
  let H : (∀ i, ℂ) → ℂ := fun r ↦
    ∫ y, Bf (fun i ↦ e i (r i)) y * h y ∂ν
  have hH_integrable : ∀ r ∈ Fintype.piFinset S,
      Integrable (fun y ↦ Bf (fun i ↦ e i (r i)) y * h y) ν := by
    intro r hr
    apply hpair (Fin.cons f (fun i ↦ e i (r i)))
      (fun i ↦ Fin.cases hf (fun j ↦ he j (r j) ((Fintype.mem_piFinset.mp hr) j)) i) hh
  have hF : (fun z ↦ ∫ y,
      B (Fin.cons f (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i)) y * h y ∂ν) =
      fun z ↦ ∑ r ∈ Fintype.piFinset S, (∏ i, φ i z (r i)) * H r := by
    funext z
    change (∫ y, Bf (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i) y * h y ∂ν) = _
    rw [hBsum z]
    simp_rw [Finset.sum_apply, Finset.sum_mul]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Bf.map_smul_univ]
      change (∫ y, ((∏ i, φ i z (r i)) • Bf (fun i ↦ e i (r i))) y * h y ∂ν) = _
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]
      simp only [mul_assoc]
    · intro r hr
      rw [Bf.map_smul_univ]
      simpa only [Pi.smul_apply, smul_eq_mul] using
        (by simpa only [mul_assoc] using
          (hH_integrable r hr).const_mul (∏ i, φ i z (r i)))
  let w : Fin m → ℝ := fun i ↦ ∑ c ∈ S i,
    max 1 (‖c‖ ^ max ((p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal)
      ((p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal))
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    dsimp [w]
    exact Finset.sum_nonneg fun c hc ↦
      le_trans zero_le_one (le_max_left _ _)
  have hφ_bound : ∀ i c, c ∈ S i → ∀ z : verticalClosedStrip 0 1,
      ‖φ i z c‖ ≤ w i := by
    intro i c hc z
    calc
      ‖φ i z c‖ ≤
          max 1 (‖c‖ ^ max ((p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal)
            ((p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal)) := by
        simpa only [φ] using
          (norm_input_deformation_coeff_uniform
            (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) c (z : ℂ) z.2)
      _ ≤ w i := by
        dsimp [w]
        exact Finset.single_le_sum (s := S i)
          (fun d hd ↦ show (0 : ℝ) ≤ max 1
            (‖d‖ ^ max ((p i.succ).toReal * ((p₀ i.succ)⁻¹).toReal)
              ((p i.succ).toReal * ((p₁ i.succ)⁻¹).toReal)) from
            le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _)) hc
  have hprod_bound : ∀ r ∈ Fintype.piFinset S, ∀ z : verticalClosedStrip 0 1,
      ‖∏ i, φ i z (r i)‖ ≤ ∏ i, w i := by
    intro r hr z
    rw [norm_prod]
    apply Finset.prod_le_prod
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      exact hφ_bound i (r i) ((Fintype.mem_piFinset.mp hr) i) z
  let C : ℝ := ∑ r ∈ Fintype.piFinset S, (∏ i, w i) * ‖H r‖
  refine ⟨C, ?_⟩
  intro z
  have hnorm :
      ‖∫ y, B (Fin.cons f
        (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i)) y * h y ∂ν‖ ≤ C := by
    rw [congrFun hF (z : ℂ)]
    calc
      ‖∑ r ∈ Fintype.piFinset S, (∏ i, φ i z (r i)) * H r‖ ≤
          ∑ r ∈ Fintype.piFinset S, ‖(∏ i, φ i z (r i)) * H r‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Fintype.piFinset S, (∏ i, w i) * ‖H r‖ := by
        apply Finset.sum_le_sum
        intro r hr
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hprod_bound r hr z) (norm_nonneg _)
      _ = C := rfl
  calc
    ‖∫ y, B (Fin.cons f
      (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p g z i)) y * h y ∂ν‖ ≤ C := hnorm
    _ ≤ C + 1 := le_add_of_nonneg_right zero_le_one
    _ ≤ Real.exp C := add_one_le_exp C
    _ = Real.exp (C * Real.exp (0 * |(z : ℂ).im|)) := by simp
section
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Complex.HadamardThreeLines Real Filter Topology ENNReal Asymptotics Set Metric
  MeromorphicOn
open scoped BigOperators
open Auto
namespace Auto
theorem _root_.solution
    {m : ℕ} {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite ν]
    (B : MultilinearMap ℂ (fun _ : Fin (m + 1) ↦ SimpleFunc X ℂ) (Y → ℂ))
    {p₀ p₁ p : Fin (m + 1) → ENNReal} {q : ENNReal} {θ M₀ M₁ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 1)
    (hp₀ : ∀ i, 1 ≤ p₀ i) (hp₁ : ∀ i, 1 ≤ p₁ i) (hp : ∀ i, 1 ≤ p i)
    (hp_top : ∀ i, p i ≠ ∞)
    (hint : ∀ i, (p i)⁻¹ = ENNReal.ofReal (1 - θ) * (p₀ i)⁻¹ +
      ENNReal.ofReal θ * (p₁ i)⁻¹)
    (hq : 1 ≤ q) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hB_measurable : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) → Measurable (B u))
    (hB_pair_integrable : ∀ (u : Fin (m + 1) → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ),
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ B u y * h y) ν)
    (hB_bound₀ : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        eLpNorm (B u) q ν ≤ ENNReal.ofReal M₀ * ∏ i,
          eLpNorm (u i : X → ℂ) (p₀ i) μ)
    (hB_bound₁ : ∀ u : Fin (m + 1) → SimpleFunc X ℂ,
      (∀ i, Integrable (u i : X → ℂ) μ) →
        eLpNorm (B u) q ν ≤ ENNReal.ofReal M₁ * ∏ i,
          eLpNorm (u i : X → ℂ) (p₁ i) μ)
    (g : Fin (m + 1) → SimpleFunc X ℂ)
    (hg : ∀ i, Integrable (g i : X → ℂ) μ)
    (hgnorm : ∀ i : Fin m, eLpNorm (g i.succ : X → ℂ) (p i.succ) μ ≤ 1) :
    MemLp (B g) q ν ∧
      eLpNorm (B g) q ν ≤
        ENNReal.ofReal (Real.rpow M₀ (1 - θ) * Real.rpow M₁ θ) *
          eLpNorm (g 0 : X → ℂ) (p 0) μ := by
  let Bcur : SimpleFunc X ℂ → (Fin m → SimpleFunc X ℂ) → Y → ℂ :=
    fun f u ↦ B.curryLeft f u
  have hB_add : ∀ (f k : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → Integrable (k : X → ℂ) μ →
        Bcur (f + k) u = Bcur f u + Bcur k u := by
    intro f k u hf hk
    change B.curryLeft (f + k) u = B.curryLeft f u + B.curryLeft k u
    rw [map_add]
    rfl
  have hB_smul : ∀ (c : ℂ) (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → Bcur (c • f) u = c • Bcur f u := by
    intro c f u hf
    change B.curryLeft (c • f) u = c • B.curryLeft f u
    rw [map_smul]
    rfl
  have hBmeas : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → (∀ i, Integrable (u i : X → ℂ) μ) →
        Measurable (Bcur f u) := by
    intro f u hf hu
    simpa only [Bcur, MultilinearMap.curryLeft_apply] using
      hB_measurable (Fin.cons f u) (fun i ↦ Fin.cases hf (fun j ↦ hu j) i)
  have hBpair : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ)
      (h : SimpleFunc Y ℂ), Integrable (f : X → ℂ) μ →
      (∀ i, Integrable (u i : X → ℂ) μ) → Integrable (h : Y → ℂ) ν →
        Integrable (fun y ↦ Bcur f u y * h y) ν := by
    intro f u h hf hu hh
    simpa only [Bcur, MultilinearMap.curryLeft_apply] using
      hB_pair_integrable (Fin.cons f u) h (fun i ↦ Fin.cases hf (fun j ↦ hu j) i) hh
  have hBbound₀ : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → (∀ i, Integrable (u i : X → ℂ) μ) →
      eLpNorm (Bcur f u) q ν ≤ ENNReal.ofReal M₀ * eLpNorm (f : X → ℂ) (p₀ 0) μ *
        ∏ i, eLpNorm (u i : X → ℂ) (p₀ i.succ) μ := by
    intro f u hf hu
    simpa only [Bcur, MultilinearMap.curryLeft_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, mul_assoc] using
      hB_bound₀ (Fin.cons f u) (fun i ↦ Fin.cases hf (fun j ↦ hu j) i)
  have hBbound₁ : ∀ (f : SimpleFunc X ℂ) (u : Fin m → SimpleFunc X ℂ),
      Integrable (f : X → ℂ) μ → (∀ i, Integrable (u i : X → ℂ) μ) →
      eLpNorm (Bcur f u) q ν ≤ ENNReal.ofReal M₁ * eLpNorm (f : X → ℂ) (p₁ 0) μ *
        ∏ i, eLpNorm (u i : X → ℂ) (p₁ i.succ) μ := by
    intro f u hf hu
    simpa only [Bcur, MultilinearMap.curryLeft_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, mul_assoc] using
      hB_bound₁ (Fin.cons f u) (fun i ↦ Fin.cases hf (fun j ↦ hu j) i)
  have hBanalytic : ∀ (f : SimpleFunc X ℂ) (h : SimpleFunc Y ℂ),
      Integrable (f : X → ℂ) μ → Integrable (h : Y → ℂ) ν →
    DiffContOnCl ℂ (fun z ↦ ∫ y,
        Bcur f
          (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p (fun i ↦ g i.succ) z i) y * h y ∂ν)
        (verticalStrip 0 1) := by
    intro f h hf hh
    simpa only [Bcur, MultilinearMap.curryLeft_apply] using
      aux_multilinear_pairing_analytic B f (fun i ↦ g i.succ) h hf (fun i ↦ hg i.succ) hh
        (fun u hu hh' ↦ hB_pair_integrable u h hu hh')
  have hBgrowth : ∃ a : ℝ, a < Real.pi ∧
      ∀ (f : SimpleFunc X ℂ) (h : SimpleFunc Y ℂ),
        Integrable (f : X → ℂ) μ → Integrable (h : Y → ℂ) ν →
        ∃ C : ℝ, ∀ z : verticalClosedStrip 0 1,
          ‖∫ y, Bcur f
            (fun i ↦ aux_multilinear_input_deformation p₀ p₁ p (fun i ↦ g i.succ) z i) y * h y ∂ν‖ ≤
              Real.exp (C * Real.exp (a * |(z : ℂ).im|)) := by
    refine ⟨0, Real.pi_pos, ?_⟩
    intro f h hf hh
    simpa only [Bcur, MultilinearMap.curryLeft_apply] using
      aux_multilinear_pairing_growth B f (fun i ↦ g i.succ) h hf (fun i ↦ hg i.succ) hh
        (fun u hu hh' ↦ hB_pair_integrable u h hu hh')
  have hcons : Fin.cons (g 0) (fun i ↦ g i.succ) = g := Fin.cons_self_tail g
  simpa only [Fin.cons_zero, Bcur, MultilinearMap.curryLeft_apply, hcons] using
    aux_multilinear_interpolation_two_endpoint_normalized Bcur hθ hp₀ hp₁ hp hp_top hint hq
      hM₀ hM₁ hB_add hB_smul hBmeas hBpair hBbound₀ hBbound₁ (g 0) (fun i ↦ g i.succ)
      (hg 0) (fun i ↦ hg i.succ) hgnorm hBanalytic hBgrowth
end Auto
