-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/98286eee-cb8e-58a2-bde7-a91e63008b9d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff

set_option autoImplicit false

open MeasureTheory

namespace FibreIntegral

noncomputable section

private def fibreIntegral {A : Type} [NormedField A] {P : Type}
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (r : (Fin 2 → Fin 2 → A) × P) : ℂ :=
  ∫ h, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
    Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of r.1), r.2) ∂μA

private theorem fibreIntegral_apply {A : Type} [NormedField A] {P : Type}
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (g : GL (Fin 2) A) (p : P) :
    fibreIntegral μA Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) A), p) =
      ∫ h, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
        Matrix.of.symm ((h⁻¹ * g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A), p) ∂μA :=
  rfl

private def fibreSupport {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) : Set (GL (Fin 2) A) :=
  (fun h : GL (Fin 2) A => Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A)) ⁻¹' (Prod.fst '' tsupport Φ)

private theorem integrand_eq_zero {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) {h : GL (Fin 2) A} (hh : h ∉ fibreSupport Φ)
    (E : Fin 2 → Fin 2 → A) (p : P) :
    Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
      Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of E), p) = 0 := by
  by_contra hne
  exact hh ⟨(Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
    Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of E), p),
    subset_tsupport Φ hne, rfl⟩

private theorem continuous_entries {A : Type} [NormedField A] :
    Continuous fun h : GL (Fin 2) A => Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A) := by
  have hval : Continuous fun h : GL (Fin 2) A => (h : Matrix (Fin 2) (Fin 2) A) := Units.continuous_val
  exact continuous_pi fun i => continuous_pi fun j => hval.matrix_elem i j

private theorem isUnit_det_entries {A : Type} [NormedField A] (h : GL (Fin 2) A) :
    IsUnit (Matrix.det (Matrix.of (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A)))) :=
  (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit

private def unitOfEntries {A : Type} [NormedField A]
    (E : {E : Fin 2 → Fin 2 → A // IsUnit (Matrix.det (Matrix.of E))}) : GL (Fin 2) A :=
  ⟨Matrix.of E.1, (Matrix.of E.1)⁻¹, Matrix.mul_nonsing_inv _ E.2, Matrix.nonsing_inv_mul _ E.2⟩

private theorem continuous_unitOfEntries {A : Type} [NormedField A] :
    Continuous (unitOfEntries (A := A)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_matrix fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  · change Continuous fun E : {E : Fin 2 → Fin 2 → A // IsUnit (Matrix.det (Matrix.of E))} => (Matrix.of E.1)⁻¹
    refine continuous_iff_continuousAt.2 fun E => ?_
    have hdet : ContinuousAt Ring.inverse (Matrix.of E.1).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (isUnit_iff_ne_zero.1 E.2)
    exact ContinuousAt.comp (g := Inv.inv)
      (f := fun E' : {E : Fin 2 → Fin 2 → A // IsUnit (Matrix.det (Matrix.of E))} => Matrix.of E'.1)
      (continuousAt_matrix_inv _ hdet) continuous_subtype_val.continuousAt

private theorem isCompact_preimage_entries {A : Type} [NormedField A] {K : Set (Fin 2 → Fin 2 → A)}
    (hK : IsCompact K) (hKU : K ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsCompact ((fun h : GL (Fin 2) A => Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A)) ⁻¹' K) := by
  have hKs : IsCompact (Subtype.val ⁻¹' K :
      Set {E : Fin 2 → Fin 2 → A // IsUnit (Matrix.det (Matrix.of E))}) := by
    refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).2 hK
    rw [Subtype.range_coe]
    exact hKU
  refine (hKs.image continuous_unitOfEntries).of_isClosed_subset (hK.isClosed.preimage continuous_entries)
    fun g hg => ?_
  exact ⟨⟨Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) A), isUnit_det_entries g⟩, hg, Units.ext rfl⟩

private theorem fst_image_tsupport_subset {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    Prod.fst '' tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hU hx).1

private theorem snd_image_tsupport_subset {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    (fun q : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P => q.2.1) '' tsupport Φ ⊆
      {E | IsUnit (Matrix.det (Matrix.of E))} := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hU hx).2

private theorem isCompact_fibreSupport {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    IsCompact (fibreSupport Φ) := by
  have h₁ : IsCompact (Prod.fst '' tsupport Φ) := IsCompact.image hc continuous_fst
  exact isCompact_preimage_entries h₁ (fst_image_tsupport_subset Φ hU)

private def productSet {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) : Set ((Fin 2 → Fin 2 → A) × P) :=
  ((fun x : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) => Matrix.of.symm (Matrix.of x.1 * Matrix.of x.2)) ''
      ((Prod.fst '' tsupport Φ) ×ˢ ((fun q : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P => q.2.1) ''
        tsupport Φ))) ×ˢ
    ((fun q : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P => q.2.2) '' tsupport Φ)

private theorem isCompact_productSet {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (hc : HasCompactSupport Φ) :
    IsCompact (productSet Φ) := by
  have h₁ : IsCompact (Prod.fst '' tsupport Φ) := IsCompact.image hc continuous_fst
  have h₂ : IsCompact ((fun q : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P => q.2.1) '' tsupport Φ) :=
    IsCompact.image hc (continuous_fst.comp continuous_snd)
  have h₃ : IsCompact ((fun q : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P => q.2.2) '' tsupport Φ) :=
    IsCompact.image hc (continuous_snd.comp continuous_snd)
  have hl : Continuous fun x : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) => Matrix.of x.1 := continuous_fst
  have hr : Continuous fun x : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) => Matrix.of x.2 := continuous_snd
  have hmul : Continuous fun x : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) =>
      Matrix.of.symm (Matrix.of x.1 * Matrix.of x.2) := hl.matrix_mul hr
  exact ((h₁.prod h₂).image hmul).prod h₃

private theorem support_subset_productSet {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) :
    Function.support (fibreIntegral μA Φ) ⊆ productSet Φ := by
  intro r hr
  obtain ⟨h, hh⟩ : ∃ h : GL (Fin 2) A, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
      Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of r.1), r.2) ≠ 0 := by
    by_contra hall
    refine hr ?_
    have hzero : ∀ h : GL (Fin 2) A, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
        Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of r.1), r.2) = 0 :=
      fun h => by
        by_contra hne
        exact hall ⟨h, hne⟩
    simp only [fibreIntegral, hzero, MeasureTheory.integral_zero]
  have hx := subset_tsupport Φ hh
  unfold productSet
  refine ⟨⟨(Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
    Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of r.1)),
    ⟨⟨_, hx, rfl⟩, ⟨_, hx, rfl⟩⟩, ?_⟩, ⟨_, hx, rfl⟩⟩
  exact (congrArg Matrix.of.symm (Units.mul_inv_cancel_left h (Matrix.of r.1))).trans
    (Matrix.of.symm_apply_apply r.1)

private theorem hasCompactSupport_fibreIntegral {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (hc : HasCompactSupport Φ) :
    HasCompactSupport (fibreIntegral μA Φ) :=
  HasCompactSupport.intro (isCompact_productSet Φ hc) fun r hr => by
    by_contra hne
    exact hr (support_subset_productSet μA Φ (Function.mem_support.2 hne))

private theorem tsupport_fibreIntegral_subset {A : Type} [NormedField A] {P : Type} [NormedAddCommGroup P]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    tsupport (fibreIntegral μA Φ) ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} := by
  intro r hr
  have hr' : r ∈ productSet Φ :=
    closure_minimal (support_subset_productSet μA Φ) (isCompact_productSet Φ hc).isClosed hr
  unfold productSet at hr'
  obtain ⟨⟨ab, ⟨hKa, hKb⟩, hab⟩, -⟩ := hr'
  have ha : IsUnit (Matrix.det (Matrix.of ab.1)) := fst_image_tsupport_subset Φ hU hKa
  have hb : IsUnit (Matrix.det (Matrix.of ab.2)) := snd_image_tsupport_subset Φ hU hKb
  change IsUnit (Matrix.det (Matrix.of r.1))
  rw [← hab]
  change IsUnit (Matrix.det (Matrix.of ab.1 * Matrix.of ab.2))
  rw [Matrix.det_mul]
  exact ha.mul hb

end

end FibreIntegral

namespace FibreIntegral

noncomputable section

private def partialSnd {V X Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ψ : V × X → Y) (q : V × X) : X →L[ℝ] Y :=
  (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inr ℝ V X)

private theorem contDiff_partialSnd {V X Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ψ : V × X → Y) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) : ContDiff ℝ (⊤ : ℕ∞) (partialSnd Ψ) := by
  show ContDiff ℝ (⊤ : ℕ∞) fun q => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inr ℝ V X)
  exact (contDiff_infty_iff_fderiv.1 hΨ).2.clm_comp contDiff_const

private theorem hasFDerivAt_partialSnd {V X Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ψ : V × X → Y) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (v : V) (x : X) :
    HasFDerivAt (fun y => Ψ (v, y)) (partialSnd Ψ (v, x)) x :=
  ((contDiff_infty_iff_fderiv.1 hΨ).1 (v, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right v x)

private theorem partialSnd_eq_zero {V X Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ψ : V × X → Y) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {v : V} (hv : ∀ y, Ψ (v, y) = 0) (x : X) :
    partialSnd Ψ (v, x) = 0 := by
  have h₁ : HasFDerivAt (fun _ : X => (0 : Y)) (partialSnd Ψ (v, x)) x := by
    simpa only [hv] using hasFDerivAt_partialSnd Ψ hΨ v x
  exact h₁.unique (hasFDerivAt_const (0 : Y) x)

private theorem hasCompactSupport_slice {G V X Y : Type} [TopologicalSpace G] [T2Space G] [Zero Y]
    {c : G → V} {K : Set G} (hK : IsCompact K) (Θ : V × X → Y)
    (h0 : ∀ h, h ∉ K → ∀ x, Θ (c h, x) = 0) (x : X) : HasCompactSupport fun h => Θ (c h, x) :=
  HasCompactSupport.intro' hK hK.isClosed fun h hh => h0 h hh x

private theorem integrable_slice {G V X Y : Type} [TopologicalSpace G] [T2Space G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [TopologicalSpace V] [TopologicalSpace X] [NormedAddCommGroup Y]
    {c : G → V} (hc : Continuous c) {K : Set G} (hK : IsCompact K) (Θ : V × X → Y)
    (hΘ : Continuous Θ) (h0 : ∀ h, h ∉ K → ∀ x, Θ (c h, x) = 0) (x : X) :
    Integrable (fun h => Θ (c h, x)) μ :=
  (hΘ.comp (hc.prodMk continuous_const)).integrable_of_hasCompactSupport
    (hasCompactSupport_slice hK Θ h0 x)

private theorem exists_integrable_bound {G V X Y : Type} [TopologicalSpace G] [T2Space G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [TopologicalSpace V] [TopologicalSpace X] [NormedAddCommGroup Y]
    {c : G → V} (hc : Continuous c) {K : Set G} (hK : IsCompact K) (Θ : V × X → Y)
    (hΘ : Continuous Θ) (h0 : ∀ h, h ∉ K → ∀ x, Θ (c h, x) = 0) (x₀ : X) :
    ∃ s ∈ nhds x₀, ∃ bound : G → ℝ,
      Integrable bound μ ∧ ∀ h, ∀ x ∈ s, ‖Θ (c h, x)‖ ≤ bound h := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun h => Θ (c h, x₀))
    (hΘ.comp (hc.prodMk continuous_const)).continuousOn
  have hev : ∀ᶠ x in nhds x₀, ∀ h ∈ K, ‖Θ (c h, x)‖ ≤ C + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun h hh => ?_
    have hcont : Continuous fun z : X × G => ‖Θ (c z.2, z.1)‖ :=
      (hΘ.comp ((hc.comp continuous_snd).prodMk continuous_fst)).norm
    have hlt : ‖Θ (c h, x₀)‖ < C + 1 := (hC h hh).trans_lt (lt_add_one C)
    exact ((hcont.continuousAt (x := (x₀, h))).eventually_lt continuousAt_const hlt).mono
      fun z hz => hz.le
  refine ⟨{x | ∀ h ∈ K, ‖Θ (c h, x)‖ ≤ C + 1}, hev, K.indicator fun _ => C + 1,
    (integrableOn_const (hK.measure_lt_top (μ := μ)).ne).integrable_indicator
      hK.isClosed.measurableSet, fun h x hx => ?_⟩
  have hx' : ∀ h ∈ K, ‖Θ (c h, x)‖ ≤ C + 1 := hx
  by_cases hh : h ∈ K
  · rw [Set.indicator_of_mem hh]
    exact hx' h hh
  · simp [Set.indicator_of_notMem hh, h0 h hh x]

private theorem hasFDerivAt_integral_slice {G V X Y : Type} [TopologicalSpace G] [T2Space G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {c : G → V} (hc : Continuous c) {K : Set G} (hK : IsCompact K) (Ψ : V × X → Y)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (h0 : ∀ h, h ∉ K → ∀ x, Ψ (c h, x) = 0) (x₀ : X) :
    HasFDerivAt (fun x => ∫ h, Ψ (c h, x) ∂μ) (∫ h, partialSnd Ψ (c h, x₀) ∂μ) x₀ := by
  have hΨ' : ContDiff ℝ (⊤ : ℕ∞) (partialSnd Ψ) := contDiff_partialSnd Ψ hΨ
  have h0' : ∀ h, h ∉ K → ∀ x, partialSnd Ψ (c h, x) = 0 :=
    fun h hh x => partialSnd_eq_zero Ψ hΨ (h0 h hh) x
  obtain ⟨s, hs, bound, hbound, hle⟩ :=
    exists_integrable_bound μ hc hK (partialSnd Ψ) hΨ'.continuous h0' x₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun x h => partialSnd Ψ (c h, x)) hs ?_ ?_ ?_ ?_ hbound ?_
  · exact Filter.Eventually.of_forall fun x =>
      (integrable_slice μ hc hK Ψ hΨ.continuous h0 x).aestronglyMeasurable
  · exact integrable_slice μ hc hK Ψ hΨ.continuous h0 x₀
  · exact (integrable_slice μ hc hK (partialSnd Ψ) hΨ'.continuous h0' x₀).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun h x hx => hle h x hx
  · exact Filter.Eventually.of_forall fun h x _ => hasFDerivAt_partialSnd Ψ hΨ (c h) x

private theorem contDiff_integral_slice_nat {G V X : Type} [TopologicalSpace G] [T2Space G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c : G → V} (hc : Continuous c) {K : Set G} (hK : IsCompact K) (n : ℕ) :
    ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] (Ψ : V × X → Y),
      ContDiff ℝ (⊤ : ℕ∞) Ψ → (∀ h, h ∉ K → ∀ x, Ψ (c h, x) = 0) →
        ContDiff ℝ n fun x => ∫ h, Ψ (c h, x) ∂μ := by
  induction n with
  | zero =>
    intro Y _ _ Ψ hΨ h0
    have key : Continuous fun x => ∫ h, Ψ (c h, x) ∂μ :=
      continuous_iff_continuousAt.2 fun x₀ => (hasFDerivAt_integral_slice μ hc hK Ψ hΨ h0 x₀).continuousAt
    exact_mod_cast (contDiff_zero.2 key : ContDiff ℝ 0 fun x => ∫ h, Ψ (c h, x) ∂μ)
  | succ n ih =>
    intro Y _ _ Ψ hΨ h0
    have key := (contDiff_succ_iff_hasFDerivAt (n := n)).2 ⟨fun x => ∫ h, partialSnd Ψ (c h, x) ∂μ,
      ih (X →L[ℝ] Y) (partialSnd Ψ) (contDiff_partialSnd Ψ hΨ)
        (fun h hh x => partialSnd_eq_zero Ψ hΨ (h0 h hh) x),
      fun x₀ => hasFDerivAt_integral_slice μ hc hK Ψ hΨ h0 x₀⟩
    exact_mod_cast key

private theorem contDiff_integral_slice {G V X Y : Type} [TopologicalSpace G] [T2Space G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {c : G → V} (hc : Continuous c) {K : Set G} (hK : IsCompact K) (Ψ : V × X → Y)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (h0 : ∀ h, h ∉ K → ∀ x, Ψ (c h, x) = 0) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => ∫ h, Ψ (c h, x) ∂μ :=
  contDiff_infty.2 fun n => contDiff_integral_slice_nat μ hc hK n Y Ψ hΨ h0

private def entriesPair (A : Type) [NormedField A] (h : GL (Fin 2) A) :
    (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) :=
  (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
    Matrix.of.symm ((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A))

private theorem continuous_entriesPair (A : Type) [NormedField A] : Continuous (entriesPair A) :=
  (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) A)).prodMk
    (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) A))

private def integrandKernel {A : Type} [NormedField A] {P : Type}
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ)
    (q : ((Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A)) × ((Fin 2 → Fin 2 → A) × P)) : ℂ :=
  Φ (q.1.1, Matrix.of.symm (Matrix.of q.1.2 * Matrix.of q.2.1), q.2.2)

private theorem contDiff_entriesMul {A : Type} [NormedField A] [NormedAlgebra ℝ A] {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ContDiff ℝ (⊤ : ℕ∞)
      fun q : ((Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A)) × ((Fin 2 → Fin 2 → A) × P) =>
        (Matrix.of.symm (Matrix.of q.1.2 * Matrix.of q.2.1) : Fin 2 → Fin 2 → A) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ (⊤ : ℕ∞)
    fun q : ((Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A)) × ((Fin 2 → Fin 2 → A) × P) =>
      ∑ k : Fin 2, q.1.2 i k * q.2.1 k j
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ A k).comp
        ((contDiff_apply ℝ (Fin 2 → A) i).comp (contDiff_snd.comp contDiff_fst))).mul
      ((contDiff_apply ℝ A j).comp
        ((contDiff_apply ℝ (Fin 2 → A) k).comp (contDiff_fst.comp contDiff_snd)))

private theorem contDiff_integrandKernel {A : Type} [NormedField A] [NormedAlgebra ℝ A] {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (integrandKernel Φ) :=
  hΦ.comp ((contDiff_fst.comp contDiff_fst).prodMk
    (contDiff_entriesMul.prodMk (contDiff_snd.comp contDiff_snd)))

private theorem contDiff_fibreIntegral {A : Type} [NormedField A] [NormedAlgebra ℝ A]
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μA : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {K : Set (GL (Fin 2) A)} (hK : IsCompact K)
    (h0 : ∀ h : GL (Fin 2) A, h ∉ K → ∀ (E : Fin 2 → Fin 2 → A) (p : P),
      Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
        Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of E), p) = 0) :
    letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
    IsFiniteMeasureOnCompacts μA →
      ContDiff ℝ (⊤ : ℕ∞) fun r : (Fin 2 → Fin 2 → A) × P =>
        ∫ h, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
          Matrix.of.symm (((h⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * Matrix.of r.1), r.2) ∂μA := by
  intro hμ
  letI : MeasurableSpace (GL (Fin 2) A) := AutomorphicForm.glBorelOf A
  haveI : BorelSpace (GL (Fin 2) A) := AutomorphicForm.borelSpace_glBorelOf A
  haveI : IsFiniteMeasureOnCompacts μA := hμ
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact contDiff_integral_slice μA (continuous_entriesPair A) hK (integrandKernel Φ)
    (contDiff_integrandKernel Φ hΦ) fun h hh x => h0 h hh x.1 x.2

end

end FibreIntegral

open AutomorphicForm in

theorem solution
    (A : Type) [NormedField A] [NormedAlgebra ℝ A]
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (Φ : (Fin 2 → Fin 2 → A) × (Fin 2 → Fin 2 → A) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1)) ∧ IsUnit (Matrix.det (Matrix.of q.2.1))}) :
    letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
    IsFiniteMeasureOnCompacts μA →
    ∃ F : (Fin 2 → Fin 2 → A) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
        ∀ (g : GL (Fin 2) A) (p : P),
          F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) A), p) =
            ∫ h, Φ (Matrix.of.symm (h : Matrix (Fin 2) (Fin 2) A),
              Matrix.of.symm ((h⁻¹ * g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A), p) ∂μA := by
  intro hμ
  refine ⟨FibreIntegral.fibreIntegral μA Φ, ?_, FibreIntegral.hasCompactSupport_fibreIntegral μA Φ hc,
    FibreIntegral.tsupport_fibreIntegral_subset μA Φ hc hU, fun g p => FibreIntegral.fibreIntegral_apply μA Φ g p⟩
  exact FibreIntegral.contDiff_fibreIntegral μA Φ hΦ (FibreIntegral.isCompact_fibreSupport Φ hc hU)
    (fun h hh E p => FibreIntegral.integrand_eq_zero Φ hh E p) hμ

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_isUnit_det_forall_eq_integral_of_contDiff (solution)
