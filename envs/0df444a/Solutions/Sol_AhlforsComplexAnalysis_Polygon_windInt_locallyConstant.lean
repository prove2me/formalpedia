-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.windInt_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:14.840984+00:00
-- url     : https://prove2.me/submissions/36c4a503-3478-40cf-bdda-88b1fb5211f0

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon
import Theorems.Thm_AhlforsComplexAnalysis_Polygon_polyInt_eq_sub_of_hasDerivAt

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

open scoped Interval

/-- Points of the form `p + t (q - p)` with `t ∈ [0, 1]` lie on the segment. -/
lemma w3_mem_segment {p q : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p + (t : ℂ) * (q - p) ∈ segment ℝ p q := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

lemma w3_isCompact_segment (p q : ℂ) : IsCompact (segment ℝ p q) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

/-- Derivative of the segment integral of `(z - b)⁻¹` in the pole `b`. -/
lemma w3_segInt_hasDerivAt {p q a : ℂ} (ha : a ∉ segment ℝ p q) :
    HasDerivAt (fun b => segInt (fun z => (z - b)⁻¹) p q)
      (segInt (fun w => ((w - a) ^ 2)⁻¹) p q) a := by
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (w3_isCompact_segment p q).isClosed.isOpen_compl a ha
  have hfar : ∀ w ∈ segment ℝ p q, ∀ x ∈ Metric.ball a (δ / 2), δ / 2 ≤ ‖w - x‖ := by
    intro w hw x hx
    by_contra h
    rw [not_le] at h
    refine hball (show w ∈ Metric.ball a δ from ?_) hw
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    have : ‖w - a‖ ≤ ‖w - x‖ + ‖x - a‖ := by simpa using norm_add_le (w - x) (x - a)
    linarith
  have hs : Metric.ball a (δ / 2) ∈ 𝓝 a := Metric.ball_mem_nhds _ (by positivity)
  have hne : ∀ x ∈ Metric.ball a (δ / 2), ∀ t ∈ Icc (0 : ℝ) 1, p + (t : ℂ) * (q - p) - x ≠ 0 := by
    intro x hx t ht h
    have := hfar _ (w3_mem_segment ht) x hx
    rw [h, norm_zero] at this
    linarith
  have hcont : ∀ x ∈ Metric.ball a (δ / 2),
      ContinuousOn (fun t : ℝ => (p + (t : ℂ) * (q - p) - x)⁻¹ * (q - p)) (Icc 0 1) := by
    intro x hx
    exact ((by fun_prop : Continuous fun t : ℝ => p + (t : ℂ) * (q - p) - x).continuousOn.inv₀
      (hne x hx)).mul continuousOn_const
  have hcont' : ∀ x ∈ Metric.ball a (δ / 2),
      ContinuousOn (fun t : ℝ => ((p + (t : ℂ) * (q - p) - x) ^ 2)⁻¹ * (q - p)) (Icc 0 1) := by
    intro x hx
    exact ((by fun_prop : Continuous fun t : ℝ => (p + (t : ℂ) * (q - p) - x) ^ 2).continuousOn.inv₀
      (fun t ht => pow_ne_zero 2 (hne x hx t ht))).mul continuousOn_const
  have hIoc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [Set.uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
    (F := fun (x : ℂ) (t : ℝ) => (p + (t : ℂ) * (q - p) - x)⁻¹ * (q - p))
    (F' := fun (x : ℂ) (t : ℝ) => ((p + (t : ℂ) * (q - p) - x) ^ 2)⁻¹ * (q - p))
    (x₀ := a) (s := Metric.ball a (δ / 2)) (bound := fun _ => ((δ / 2) ^ 2)⁻¹ * ‖q - p‖)
    hs
    (Filter.eventually_of_mem hs fun x hx =>
      ((hcont x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    ((hcont a (Metric.mem_ball_self (by positivity))).intervalIntegrable_of_Icc zero_le_one)
    (((hcont' a (Metric.mem_ball_self (by positivity))).mono hIoc).aestronglyMeasurable
      measurableSet_uIoc)
    (Filter.Eventually.of_forall fun t ht x hx => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := hIoc ht
      have h1 := hfar _ (w3_mem_segment ht') x hx
      have h2 : 0 < δ / 2 := by positivity
      rw [norm_mul, norm_inv, norm_pow]
      gcongr)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht x hx => by
      have ht' : t ∈ Icc (0 : ℝ) 1 := hIoc ht
      have hne' := hne x hx t ht'
      refine HasDerivAt.congr_deriv
        ((((hasDerivAt_id x).const_sub _).inv ?_).mul_const (q - p)) ?_
      · simpa using hne'
      · simp)
  exact key.2

/-- Derivative of `windInt l` in the pole, off the trace. -/
lemma w3_hasDerivAt : ∀ (l : List ℂ) {a : ℂ}, a ∉ polyTrace l →
    HasDerivAt (windInt l) (polyInt (fun w => ((w - a) ^ 2)⁻¹) l) a
  | [], a, _ => by
      have h : windInt [] = fun _ => 0 := by funext b; simp [windInt, polyInt]
      rw [h]
      simpa [polyInt] using hasDerivAt_const a (0 : ℂ)
  | [x], a, _ => by
      have h : windInt [x] = fun _ => 0 := by funext b; simp [windInt, polyInt]
      rw [h]
      simpa [polyInt] using hasDerivAt_const a (0 : ℂ)
  | p :: q :: rest, _, ha => by
      have h1 : _ ∉ segment ℝ p q := fun h => ha (Or.inl h)
      have h2 : _ ∉ polyTrace (q :: rest) := fun h => ha (Or.inr h)
      exact (w3_segInt_hasDerivAt h1).add (w3_hasDerivAt (q :: rest) h2)

/-- A polygon missing `a` lies in `{a}ᶜ`. -/
lemma w3_polyIn_compl : ∀ (l : List ℂ) {a : ℂ}, a ∉ polyTrace l → PolyIn {a}ᶜ l
  | [], _, _ => trivial
  | [x], a, h => by
      intro hx
      exact h (by simpa [polyTrace] using hx.symm)
  | p :: q :: rest, a, h =>
      ⟨fun z hz hza => h (Or.inl (by rw [mem_singleton_iff] at hza; rwa [← hza])),
        w3_polyIn_compl (q :: rest) fun h' => h (Or.inr h')⟩

/-- For a closed polygon, the derivative of `windInt` in the pole vanishes. -/
lemma w3_polyInt_sq_eq_zero {l : List ℂ} (hl : IsClosedPoly l) {a : ℂ}
    (ha : a ∉ polyTrace l) : polyInt (fun w => ((w - a) ^ 2)⁻¹) l = 0 := by
  have hG : ∀ z ∈ ({a}ᶜ : Set ℂ), HasDerivAt (fun w : ℂ => -(w - a)⁻¹) (((z - a) ^ 2)⁻¹) z := by
    intro z hz
    have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
    refine ((((hasDerivAt_id' z).sub_const a).inv hza).neg).congr_deriv ?_
    field_simp
  have hg : ContinuousOn (fun w : ℂ => ((w - a) ^ 2)⁻¹) {a}ᶜ :=
    ContinuousOn.inv₀ (by fun_prop) fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr hz)
  have hne : l ≠ [] := hl.1
  have h : l.head? = l.getLast? := hl.2
  rw [List.head?_eq_some_head hne, List.getLast?_eq_some_getLast hne] at h
  rw [polyInt_eq_sub_of_hasDerivAt isOpen_compl_singleton hG hg
    (w3_polyIn_compl l ha) hne]
  simp [Option.some.inj h]

/-- For a closed polygon, `windInt l` is constant on an open preconnected set missing the trace. -/
lemma w3_const_of_preconnected {l : List ℂ} (hl : IsClosedPoly l) {V : Set ℂ}
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hV : Disjoint V (polyTrace l)) {x y : ℂ}
    (hx : x ∈ V) (hy : y ∈ V) : windInt l x = windInt l y := by
  have hderiv : ∀ b ∈ V, HasDerivAt (windInt l) 0 b := fun b hb => by
    have hb' : b ∉ polyTrace l := Set.disjoint_left.mp hV hb
    have := w3_hasDerivAt l hb'
    rwa [w3_polyInt_sq_eq_zero hl hb'] at this
  exact hVo.is_const_of_deriv_eq_zero hVc
    (fun b hb => (hderiv b hb).differentiableAt.differentiableWithinAt)
    (fun b hb => (hderiv b hb).deriv) hx hy

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

theorem solution {l : List ℂ} (hl : IsClosedPoly l) {a : ℂ}
    (ha : a ∉ polyTrace l) : ∀ᶠ b in 𝓝 a, windInt l b = windInt l a := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (polyTrace_isCompact l).isClosed.isOpen_compl a ha
  filter_upwards [Metric.ball_mem_nhds a hr] with b hb
  exact w3_const_of_preconnected hl Metric.isOpen_ball (convex_ball a r).isPreconnected
    (Set.disjoint_left.mpr fun z hz => hball hz) hb (Metric.mem_ball_self hr)

#print axioms solution
