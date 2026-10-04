-- Prove2me | solution 1 for AnosovPlugs.comparable_of_metrics
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T19:13:19.001708+00:00
-- url     : https://prove2.me/submissions/a47e9fb8-20f8-4b5f-a189-5819319f9bb8

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing

open scoped Manifold ContDiff Topology
open Set
open AnosovPlugs

local notation "F3" => EuclideanSpace ℝ (Fin 3)

/-- A positive definite continuous bilinear form on `F3` is coercive. -/
theorem cm_exists_coercive (φ : F3 →L[ℝ] F3 →L[ℝ] ℝ) (h : ∀ v ≠ 0, 0 < φ v v) :
    ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ φ v v := by
  rcases subsingleton_or_nontrivial F3 with hs | hs
  · refine ⟨1, one_pos, fun v => ?_⟩
    have : v = 0 := Subsingleton.elim _ _
    subst this
    simp
  have hS : (Metric.sphere (0 : F3) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hc : Continuous (fun v : F3 => φ v v) :=
    φ.continuous₂.comp (continuous_id.prodMk continuous_id)
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : F3) 1).exists_isMinOn hS hc.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  refine ⟨φ u u, h u hu0, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set u' : F3 := ‖v‖⁻¹ • v with hu'def
  have hu' : u' ∈ Metric.sphere (0 : F3) 1 := by
    simp [u', norm_smul, hn.ne']
  have hle : φ u u ≤ φ u' u' := isMinOn_iff.1 hmin u' hu'
  have hvu : v = ‖v‖ • u' := by
    simp [u', smul_smul, hn.ne']
  have hφv : φ v v = ‖v‖ ^ 2 * φ u' u' := by
    conv_lhs => rw [hvu]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hφv]
  calc φ u u * ‖v‖ ^ 2 = ‖v‖ ^ 2 * φ u u := by ring
    _ ≤ ‖v‖ ^ 2 * φ u' u' := by gcongr

/-- Local two-sided bounds for a continuous family of bilinear forms that is positive definite
at the base point. -/
theorem cm_local_bounds {X : Type*} [TopologicalSpace X] (φ : X → F3 →L[ℝ] F3 →L[ℝ] ℝ)
    (x₀ : X) (hφ : ContinuousAt φ x₀) (h : ∀ w ≠ 0, 0 < φ x₀ w w) :
    ∃ m > 0, ∃ C > 0, ∀ᶠ x in 𝓝 x₀, ∀ w, m * ‖w‖ ^ 2 ≤ φ x w w ∧ φ x w w ≤ C * ‖w‖ ^ 2 := by
  obtain ⟨m₀, hm₀, hcoer⟩ := cm_exists_coercive (φ x₀) h
  refine ⟨m₀ / 2, by positivity, ‖φ x₀‖ + m₀, by positivity, ?_⟩
  have hev := (Metric.continuousAt_iff' (f := φ) (b := x₀)).1 hφ (m₀ / 2) (by positivity)
  filter_upwards [hev] with x hx w
  rw [dist_eq_norm (φ x) (φ x₀)] at hx
  have h1 : |(φ x - φ x₀) w w| ≤ m₀ / 2 * ‖w‖ ^ 2 := by
    calc |(φ x - φ x₀) w w| = ‖(φ x - φ x₀) w w‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ x - φ x₀‖ * ‖w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ m₀ / 2 * ‖w‖ * ‖w‖ := by gcongr
      _ = m₀ / 2 * ‖w‖ ^ 2 := by ring
  have h2 : φ x₀ w w ≤ ‖φ x₀‖ * ‖w‖ ^ 2 := by
    calc φ x₀ w w ≤ ‖φ x₀ w w‖ := Real.le_norm_self _
      _ ≤ ‖φ x₀‖ * ‖w‖ * ‖w‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ = ‖φ x₀‖ * ‖w‖ ^ 2 := by ring
  have h3 := hcoer w
  have h4 : (φ x - φ x₀) w w = φ x w w - φ x₀ w w := by simp
  rw [h4, abs_le] at h1
  have h5 : 0 ≤ m₀ * ‖w‖ ^ 2 := by positivity
  constructor <;> linarith [h1.1, h1.2]

/-- The abstract local comparison in the model fibre. -/
theorem cm_local_model {X : Type*} [TopologicalSpace X] (G H : X → F3 →L[ℝ] F3 →L[ℝ] ℝ)
    (D : X → F3 →L[ℝ] F3) (x₀ : X) (hG : ContinuousAt G x₀) (hH : ContinuousAt H x₀)
    (hD : ContinuousAt D x₀) (hG0 : ∀ w ≠ 0, 0 < G x₀ w w) (hH0 : ∀ w ≠ 0, 0 < H x₀ w w)
    (hD0 : Function.Injective (D x₀)) :
    ∃ a > 0, ∃ b > 0, ∀ᶠ x in 𝓝 x₀, ∀ w,
      a * G x w w ≤ H x (D x w) (D x w) ∧ H x (D x w) (D x w) ≤ b * G x w w := by
  set Φ : X → F3 →L[ℝ] F3 →L[ℝ] ℝ := fun x => (((H x).comp (D x)).flip.comp (D x)).flip
    with hΦdef
  have hΦ : ∀ x w, Φ x w w = H x (D x w) (D x w) := by
    intro x w
    simp [Φ]
  have hflip : Continuous (fun f : F3 →L[ℝ] F3 →L[ℝ] ℝ => f.flip) := by
    simpa using (ContinuousLinearMap.flipₗᵢ ℝ F3 F3 ℝ).continuous
  have hΦc : ContinuousAt Φ x₀ := by
    have h1 : ContinuousAt (fun x => ((H x).comp (D x)).flip) x₀ :=
      hflip.continuousAt.comp (hH.clm_comp hD)
    exact hflip.continuousAt.comp (h1.clm_comp hD)
  have hΦ0 : ∀ w ≠ 0, 0 < Φ x₀ w w := by
    intro w hw
    rw [hΦ]
    apply hH0
    intro h
    apply hw
    apply hD0
    rw [h, map_zero]
  obtain ⟨mG, hmG, CG, hCG, hGev⟩ := cm_local_bounds G x₀ hG hG0
  obtain ⟨mΦ, hmΦ, CΦ, hCΦ, hΦev⟩ := cm_local_bounds Φ x₀ hΦc hΦ0
  refine ⟨mΦ / CG, by positivity, CΦ / mG, by positivity, ?_⟩
  filter_upwards [hGev, hΦev] with x hx1 hx2 w
  obtain ⟨g1, g2⟩ := hx1 w
  obtain ⟨p1, p2⟩ := hx2 w
  rw [hΦ] at p1 p2
  constructor
  · calc mΦ / CG * G x w w ≤ mΦ / CG * (CG * ‖w‖ ^ 2) := by gcongr
      _ = mΦ * ‖w‖ ^ 2 := by field_simp
      _ ≤ _ := p1
  · calc _ ≤ CΦ * ‖w‖ ^ 2 := p2
      _ = CΦ / mG * (mG * ‖w‖ ^ 2) := by field_simp
      _ ≤ CΦ / mG * G x w w := by gcongr

section Bundle

variable {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X]
  [IsManifold I3 ∞ X]

/-- The metric `g` read in the trivialization at `x₀`. -/
noncomputable def cm_coord (g : RiemannianMetric3 X) (x₀ x : X) : F3 →L[ℝ] F3 →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates F3 (TangentSpace I3) (F3 →L[ℝ] ℝ)
    (fun x : X => TangentSpace I3 x →L[ℝ] ℝ) x₀ x x₀ x (g.inner x)

theorem cm_coord_continuousAt (g : RiemannianMetric3 X) (x₀ : X) :
    ContinuousAt (fun x => cm_coord g x₀ x) x₀ := by
  have W := g.continuous.continuousAt (x := x₀)
  simp only [continuousAt_hom_bundle] at W
  exact W.2

theorem cm_coord_apply (g : RiemannianMetric3 X) {x₀ x : X}
    (hx : x ∈ (trivializationAt F3 (TangentSpace I3 : X → Type) x₀).baseSet)
    (v : TangentSpace I3 x) :
    cm_coord g x₀ x ((trivializationAt F3 (TangentSpace I3 : X → Type) x₀).continuousLinearMapAt ℝ x v)
      ((trivializationAt F3 (TangentSpace I3 : X → Type) x₀).continuousLinearMapAt ℝ x v) =
      g.inner x v v := by
  rw [cm_coord, inCoordinates_apply_eq₂ hx hx (Set.mem_univ _)]
  have A : ((trivializationAt F3 (TangentSpace I3 : X → Type) x₀).symm x)
      ((trivializationAt F3 (TangentSpace I3 : X → Type) x₀).linearMapAt ℝ x v) = v :=
    Bundle.Trivialization.symm_linearMapAt _ hx v
  simp [A]

theorem cm_coord_pos (g : RiemannianMetric3 X) (x₀ : X) :
    ∀ w ≠ 0, 0 < cm_coord g x₀ x₀ w w := by
  intro w hw
  have hx₀ : x₀ ∈ (trivializationAt F3 (TangentSpace I3 : X → Type) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hv := Bundle.Trivialization.continuousLinearMapAt_symmL
    (trivializationAt F3 (TangentSpace I3 : X → Type) x₀) (R := ℝ) hx₀ w
  rw [← hv, cm_coord_apply g hx₀]
  apply g.pos
  intro h
  apply hw
  rw [← hv, h, map_zero]

end Bundle

section Map

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]
  {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]

theorem cm_D_continuousAt (i : M → N) (hi : ContMDiff I3 I3 1 i) (x₀ : M) :
    ContinuousAt (inTangentCoordinates I3 I3 id i (fun x => mfderiv I3 I3 i x) x₀) x₀ :=
  (hi.contMDiffAt.mfderiv_const (m := 0) (by norm_num)).continuousAt

theorem cm_D_apply (i : M → N) {x₀ x : M}
    (hx : x ∈ (trivializationAt F3 (TangentSpace I3 : M → Type) x₀).baseSet)
    (v : TangentSpace I3 x) :
    inTangentCoordinates I3 I3 id i (fun x => mfderiv I3 I3 i x) x₀ x
      ((trivializationAt F3 (TangentSpace I3 : M → Type) x₀).continuousLinearMapAt ℝ x v) =
      (trivializationAt F3 (TangentSpace I3 : N → Type) (i x₀)).continuousLinearMapAt ℝ (i x)
        (mfderiv I3 I3 i x v) := by
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates, id,
    ContinuousLinearMap.comp_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hx v]

theorem cm_D_injective (i : M → N) (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (x₀ : M) :
    Function.Injective (inTangentCoordinates I3 I3 id i (fun x => mfderiv I3 I3 i x) x₀ x₀) := by
  have hx₀ : x₀ ∈ (trivializationAt F3 (TangentSpace I3 : M → Type) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hy₀ : i x₀ ∈ (trivializationAt F3 (TangentSpace I3 : N → Type) (i x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (i x₀)
  intro w₁ w₂ h
  rw [← Bundle.Trivialization.continuousLinearMapAt_symmL
    (trivializationAt F3 (TangentSpace I3 : M → Type) x₀) (R := ℝ) hx₀ w₁,
    ← Bundle.Trivialization.continuousLinearMapAt_symmL
    (trivializationAt F3 (TangentSpace I3 : M → Type) x₀) (R := ℝ) hx₀ w₂,
    cm_D_apply i hx₀, cm_D_apply i hx₀] at h
  have h' := congrArg
    ((trivializationAt F3 (TangentSpace I3 : N → Type) (i x₀)).symmL ℝ (i x₀)) h
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hy₀,
    Bundle.Trivialization.symmL_continuousLinearMapAt _ hy₀] at h'
  have h'' := hinj x₀ h'
  rw [← Bundle.Trivialization.continuousLinearMapAt_symmL
    (trivializationAt F3 (TangentSpace I3 : M → Type) x₀) (R := ℝ) hx₀ w₁,
    ← Bundle.Trivialization.continuousLinearMapAt_symmL
    (trivializationAt F3 (TangentSpace I3 : M → Type) x₀) (R := ℝ) hx₀ w₂, h'']

theorem cm_local (i : M → N) (hi : ContMDiff I3 I3 1 i)
    (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (g : RiemannianMetric3 M) (g' : RiemannianMetric3 N) (x₀ : M) :
    ∃ a > 0, ∃ b > 0, ∀ᶠ x in 𝓝 x₀, ∀ v : TangentSpace I3 x,
      a * g.inner x v v ≤ g'.inner (i x) (mfderiv I3 I3 i x v) (mfderiv I3 I3 i x v) ∧
      g'.inner (i x) (mfderiv I3 I3 i x v) (mfderiv I3 I3 i x v) ≤ b * g.inner x v v := by
  have hx₀ : x₀ ∈ (trivializationAt F3 (TangentSpace I3 : M → Type) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  have hy₀ : i x₀ ∈ (trivializationAt F3 (TangentSpace I3 : N → Type) (i x₀)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (i x₀)
  have hH : ContinuousAt (fun x => cm_coord g' (i x₀) (i x)) x₀ :=
    (cm_coord_continuousAt g' (i x₀)).comp hi.continuous.continuousAt
  obtain ⟨a, ha, b, hb, hev⟩ := cm_local_model (fun x => cm_coord g x₀ x)
    (fun x => cm_coord g' (i x₀) (i x))
    (inTangentCoordinates I3 I3 id i (fun x => mfderiv I3 I3 i x) x₀) x₀
    (cm_coord_continuousAt g x₀) hH (cm_D_continuousAt i hi x₀) (cm_coord_pos g x₀)
    (cm_coord_pos g' (i x₀)) (cm_D_injective i hinj x₀)
  refine ⟨a, ha, b, hb, ?_⟩
  filter_upwards [hev, (trivializationAt F3 (TangentSpace I3 : M → Type) x₀).open_baseSet.mem_nhds hx₀,
    hi.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt F3 (TangentSpace I3 : N → Type) (i x₀)).open_baseSet.mem_nhds hy₀)]
    with x hx hxe hxe' v
  have hxe'' : i x ∈ (trivializationAt F3 (TangentSpace I3 : N → Type) (i x₀)).baseSet := hxe'
  have key := hx ((trivializationAt F3 (TangentSpace I3 : M → Type) x₀).continuousLinearMapAt ℝ x v)
  rw [cm_coord_apply g hxe, cm_D_apply i hxe, cm_coord_apply g' hxe''] at key
  exact key

end Map

theorem cm_inner_nonneg {X : Type} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 3) X]
    [IsManifold I3 ∞ X] (g : RiemannianMetric3 X) (x : X) (v : TangentSpace I3 x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (g.pos x v hv).le

theorem solution
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    [CompactSpace M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (i : M → N) (hi : ContMDiff I3 I3 1 i) (hinj : ∀ x, Function.Injective (mfderiv I3 I3 i x))
    (g : RiemannianMetric3 M) (g' : RiemannianMetric3 N) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (x : M) (v : TangentSpace I3 x),
        c₁ * g.norm x v ≤ g'.norm (i x) (mfderiv I3 I3 i x v) ∧
        g'.norm (i x) (mfderiv I3 I3 i x v) ≤ c₂ * g.norm x v := by
  have hloc := fun x₀ : M => cm_local i hi hinj g g' x₀
  choose a ha b hb hev using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x₀ => {x : M | ∀ v : TangentSpace I3 x,
      a x₀ * g.inner x v v ≤ g'.inner (i x) (mfderiv I3 I3 i x v) (mfderiv I3 I3 i x v) ∧
      g'.inner (i x) (mfderiv I3 I3 i x v) (mfderiv I3 I3 i x v) ≤ b x₀ * g.inner x v v})
    (fun x₀ _ => hev x₀)
  set A : ℝ := 1 + ∑ x ∈ t, 1 / a x with hA
  set B : ℝ := 1 + ∑ x ∈ t, b x with hB
  have hsumA : 0 ≤ ∑ x ∈ t, 1 / a x :=
    Finset.sum_nonneg (fun x _ => (one_div_pos.2 (ha x)).le)
  have hsumB : 0 ≤ ∑ x ∈ t, b x := Finset.sum_nonneg (fun x _ => (hb x).le)
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hsq : ∀ (x : M) (v : TangentSpace I3 x),
      1 / A * g.inner x v v ≤ g'.inner (i x) (mfderiv I3 I3 i x v) (mfderiv I3 I3 i x v) ∧
      g'.inner (i x) (mfderiv I3 I3 i x v) (mfderiv I3 I3 i x v) ≤ B * g.inner x v v := by
    intro x v
    have hx := ht (mem_univ x)
    simp only [mem_iUnion] at hx
    obtain ⟨x₀, hx₀t, hx⟩ := hx
    obtain ⟨h1, h2⟩ := hx v
    have hg0 := cm_inner_nonneg g x v
    have hAle : 1 / a x₀ ≤ A := by
      have := Finset.single_le_sum (f := fun x => 1 / a x)
        (fun x _ => (one_div_pos.2 (ha x)).le) hx₀t
      linarith
    have hBle : b x₀ ≤ B := by
      have := Finset.single_le_sum (f := b) (fun x _ => (hb x).le) hx₀t
      linarith
    have hAa : 1 / A ≤ a x₀ := by
      have := one_div_le_one_div_of_le (one_div_pos.2 (ha x₀)) hAle
      simpa using this
    constructor
    · calc 1 / A * g.inner x v v ≤ a x₀ * g.inner x v v := by gcongr
        _ ≤ _ := h1
    · calc _ ≤ b x₀ * g.inner x v v := h2
        _ ≤ B * g.inner x v v := by gcongr
  refine ⟨Real.sqrt (1 / A), Real.sqrt B, Real.sqrt_pos.2 (by positivity),
    Real.sqrt_pos.2 hBpos, fun x v => ?_⟩
  obtain ⟨h1, h2⟩ := hsq x v
  simp only [RiemannianMetric3.norm]
  constructor
  · rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt h1
  · rw [← Real.sqrt_mul hBpos.le]
    exact Real.sqrt_le_sqrt h2
