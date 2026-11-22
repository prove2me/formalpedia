-- Prove2me | Definitions.Def_NoHair_PseudoRiemannianNormalCoordinates
-- name    : NoHair_PseudoRiemannianNormalCoordinates
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:24:07.905572+00:00
-- url     : https://prove2.me/theorems/3068e12a-b78f-4aaa-b9bd-4aa3aded42a4
-- title:
--   Normal coordinates and the signed-energy first variation for a nondegenerate metric
-- statement:
--   The local logarithm, signed initial energy, and terminal velocity of a geodesic for a smooth symmetric nondegenerate metric on a finite-dimensional real inner product space. Includes existence of the normal-coordinate flow, its differential at the diagonal, conservation of signed energy, and the first variation of signed initial energy with the terminal endpoint.
-- source:
--   Semi-Riemannian normal coordinates and the Gauss lemma, B. O’Neill, Semi-Riemannian Geometry, ch. 3. The Lean coordinate proofs adapt the OAI.WeakMTWGlobalSupport geometry and Gauss lemma already on Prove2Me, https://prove2.me/submissions/6b998234-2973-4009-b1c3-a3b4dc4a1810.

import Definitions.Def_OAIQWMTW001

/-!
# Normal coordinates and first variation for a nondegenerate metric

Adapted from the coordinate geometry and smooth flow in OAI.WeakMTWGlobalSupport,
in particular Prove2Me definitions OAIQWMTW000 and OAIQWMTW001, and its
Gauss lemma proof (submission 6b998234-2973-4009-b1c3-a3b4dc4a1810).
The metric is required to be invertible and symmetric, allowing indefinite signature.
-/

open Set Filter InnerProductSpace
open scoped Topology ContDiff
open OAI.WeakMTWGlobalSupport
open OAI.WeakMTWGlobalSupport.CoordinateGeometry
open OAI.WeakMTWGlobalSupport.NormalNeighborhood
open OAI.WeakMTWGlobalSupport.NormalCoordinates
open OAI.WeakMTWGlobalSupport.VariationCalculus

namespace NoHair.PseudoNormal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

theorem metric_christoffel_of_invertible {x : E} (hinv : (G x).IsInvertible)
    (v w z : E) :
    G x (christoffel G x v w) z =
      (fderiv ℝ G x v w z + fderiv ℝ G x w v z - fderiv ℝ G x z v w) / 2 := by
  unfold christoffel
  rw [hinv.self_apply_inverse, lowerChristoffel_apply]

theorem metric_compatible_of_invertible (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {x : E} (hx : x ∈ S) (v w z : E) :
    fderiv ℝ G x v w z = G x (christoffel G x v w) z + G x w (christoffel G x v z) := by
  rw [hsym x hx w, metric_christoffel_of_invertible (hinv x hx), metric_christoffel_of_invertible (hinv x hx)]
  rw [derivative_metric_symmetric hS hG hsym hx v z w,
    derivative_metric_symmetric hS hG hsym hx z v w,
    derivative_metric_symmetric hS hG hsym hx w v z]
  ring

theorem contDiffOn_metric_inverse_of_invertible (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ x ∈ S, (G x).IsInvertible) :
    ContDiffOn ℝ ∞ (fun x => (G x).inverse) S := by
  intro x hx
  obtain ⟨e, he⟩ := hinv x hx
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G x) := by
    rw [← he]
    exact contDiffAt_map_inverse e
  exact (hi.comp x ((hG x hx).contDiffAt (hS.mem_nhds hx))).contDiffWithinAt

theorem contDiffOn_geodesicSpray_of_invertible (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ x ∈ S, (G x).IsInvertible) :
    ContDiffOn ℝ ∞ (geodesicSpray G) (S ×ˢ univ) := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (MetricTensor E) := inferInstance
  let : NormedSpace ℝ (MetricTensor E) := inferInstance
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ G) S :=
    hG.fderiv_of_isOpen hS (by rw [ENat.coe_top_add_one])
  have hD' : ContDiffOn ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) (S ×ˢ univ) :=
    hD.comp contDiffOn_fst (fun q hq => hq.1)
  have hG' : ContDiffOn ℝ ∞ (fun q : E × E => (G q.1).inverse) (S ×ˢ univ) :=
    (contDiffOn_metric_inverse_of_invertible hS hG hinv).comp contDiffOn_fst (fun q hq => hq.1)
  have hA : ContDiffOn ℝ ∞ (fun q : E × E =>
      (fderiv ℝ G q.1).flip q.2) (S ×ˢ univ) :=
    ((ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.comp_contDiffOn hD').clm_apply
      contDiffOn_snd
  have hB : ContDiffOn ℝ ∞ (fun q : E × E =>
      ((fderiv ℝ G q.1).flip q.2).flip q.2) (S ×ˢ univ) :=
    ((ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.contDiff.comp_contDiffOn hA).clm_apply
      contDiffOn_snd
  have hC := (hD'.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd
  exact contDiffOn_snd.prodMk (hG'.clm_apply ((hC.add hC |>.sub hB).const_smul (1 / 2 : ℝ))).neg

theorem geodesic_energy_hasDerivAt_zero_of_invertible (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {c V : ℝ → E} {t : ℝ} (ht : c t ∈ S)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t) :
    HasDerivAt (fun r => G (c r) (V r) (V r)) 0 t := by
  have hd := hasDerivAt_metric_pairing ((hG (c t) ht).differentiableAt (hS.mem_nhds ht)) hc hV hV
  have hm := metric_compatible_of_invertible hS hG hsym hinv ht (V t) (V t) (V t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

theorem geodesic_energy_constant_of_invertible (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {c V : ℝ → E} {a b : ℝ}
    (hmem : ∀ t ∈ Icc a b, c t ∈ S)
    (hc : ∀ t ∈ Icc a b, HasDerivAt c (V t) t)
    (hV : ∀ t ∈ Icc a b, HasDerivAt V (-christoffel G (c t) (V t) (V t)) t) :
    ∀ t ∈ Icc a b, G (c t) (V t) (V t) = G (c a) (V a) (V a) := by
  have hd := fun t ht => geodesic_energy_hasDerivAt_zero_of_invertible hS hG hsym hinv (hmem t ht) (hc t ht) (hV t ht)
  exact constant_of_has_deriv_right_zero (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

theorem hasFDerivAt_geodesicSpray_zero_of_invertible (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ x ∈ S, (G x).IsInvertible) {x : E} (hx : x ∈ S) :
    HasFDerivAt (geodesicSpray G)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (x, 0) := by
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (MetricTensor E) := inferInstance
  let : NormedSpace ℝ (MetricTensor E) := inferInstance
  have hc := (hG x hx).contDiffAt (hS.mem_nhds hx)
  have hD : ContDiffAt ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) (x, 0) :=
    (hc.fderiv_right (m := ∞) (by rw [ENat.coe_top_add_one])).comp (x, 0) contDiffAt_fst
  have hA : HasFDerivAt (fun q : E × E => fderiv ℝ G q.1 q.2 q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    have hd := (((hD.differentiableAt (by simp)).hasFDerivAt.clm_apply hasFDerivAt_snd).clm_apply hasFDerivAt_snd)
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hDflip : ContDiffAt ℝ ∞ (fun q : E × E => (fderiv ℝ G q.1).flip) (x, 0) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).toContinuousLinearMap.contDiff.contDiffAt.comp (x, 0) hD
  have hAflip := hDflip.clm_apply contDiffAt_snd
  have hDflip2 : ContDiffAt ℝ ∞ (fun q : E × E => ((fderiv ℝ G q.1).flip q.2).flip) (x, 0) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp (x, 0) hAflip
  have hB : HasFDerivAt (fun q : E × E => ((fderiv ℝ G q.1).flip q.2).flip q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    have hd₁ := (hDflip.differentiableAt (by simp)).hasFDerivAt.clm_apply hasFDerivAt_snd
    have hd₂ := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.hasFDerivAt.comp (x, 0) hd₁
    have hd := hd₂.clm_apply hasFDerivAt_snd
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hL : HasFDerivAt (fun q : E × E => lowerChristoffel (fderiv ℝ G q.1) q.2 q.2) (0 : E × E →L[ℝ] E →L[ℝ] ℝ) (x, 0) := by
    convert! ((hA.add hA).sub hB).const_smul (1 / 2 : ℝ) using 1
    simp
  have hI : ContDiffAt ℝ ∞ (fun q : E × E => (G q.1).inverse) (x, 0) :=
    ((contDiffOn_metric_inverse_of_invertible hS hG hinv x hx).contDiffAt (hS.mem_nhds hx)).comp (x, 0) contDiffAt_fst
  have hC : HasFDerivAt (fun q : E × E => christoffel G q.1 q.2 q.2) (0 : E × E →L[ℝ] E) (x, 0) := by
    have hd := (hI.differentiableAt (by simp)).hasFDerivAt.clm_apply hL
    convert! hd using 1
    apply ContinuousLinearMap.ext
    intro q
    simp [lowerChristoffel]
  convert! hasFDerivAt_snd.prodMk hC.neg using 1
  simp

theorem hasFDerivAt_flow_zero_of_invertible {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x : E} (hx : x ∈ S) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, 0)) ∈ U) :
    HasFDerivAt (fun q => Φ (T, q))
      (ContinuousLinearMap.id ℝ (E × E) + T •
        (ContinuousLinearMap.snd ℝ E E).prod (0 : E × E →L[ℝ] E)) (x, 0) := by
  have heq := FlowLinearization.equilibrium hU (hΦ.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hS.prod isOpen_univ) ((contDiffOn_geodesicSpray_of_invertible hS hG hinv).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top))
    hzero (fun q hq => ⟨⟨(hode q hq).1, mem_univ _⟩, (hode q hq).2⟩)
    (x := (x, 0)) ⟨hx, mem_univ _⟩ (geodesicSpray_zero G x) hT hseg
  have hd := hasFDerivAt_geodesicSpray_zero_of_invertible hS hG hinv hx
  have hlin := FlowLinearization.nilpotent_variation hU (hΦ.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hzero
    (fun q hq => (hode q hq).2) hd (by intro w; simp) hT hseg heq
  have hTx := hseg T ⟨hT, le_rfl⟩
  have hder := (((hΦ _ hTx).contDiffAt (hU.mem_nhds hTx)).differentiableAt (by simp)).hasFDerivAt.comp
    (x, 0) ((hasFDerivAt_const T (x, 0)).prodMk (hasFDerivAt_id (x, 0)))
  convert! hder using 1
  apply ContinuousLinearMap.ext
  intro w
  simpa [ContinuousLinearMap.comp_apply] using (hlin w T ⟨hT, le_rfl⟩).symm

theorem hasFDerivAt_normalMap_zero_of_invertible {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x : E} (hx : x ∈ S) {T : ℝ} (hT : 0 < T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, 0)) ∈ U) :
    HasFDerivAt (fun q => (q.1, (Φ (T, q)).1)) ((normalShear (E := E) T (ne_of_gt hT)) : E × E →L[ℝ] E × E) (x, 0) := by
  have hd := hasFDerivAt_flow_zero_of_invertible hS hG hinv hU hΦ hzero hode hx hT.le hseg
  convert! hasFDerivAt_fst.prodMk hd.fst using 1

theorem exists_normalFlow_of_invertible {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {x₀ : E} (hx₀ : x₀ ∈ S) : Nonempty (NormalFlow G S x₀) := by
  obtain ⟨U, Φ, hU, h0, hΦ, hzero, hode'⟩ := SmoothFlow.exists_smooth_local_flow
    (hS.prod isOpen_univ) (contDiffOn_geodesicSpray_of_invertible hS hG hinv)
    (x₀ := (x₀, (0 : E))) ⟨hx₀, mem_univ _⟩
  have hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1 :=
    fun q hq => ⟨(hode' q hq).1.1, (hode' q hq).2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let T : ℝ := r / 2
  have hT : 0 < T := half_pos hr
  have hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x₀, 0)) ∈ U := by
    intro t ht
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
      abs_of_nonneg ht.1, max_eq_left ht.1]
    exact lt_of_le_of_lt ht.2 (half_lt_self hr)
  let A : Set (E × E) := {q | ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U}
  have hA : IsOpen A := isOpen_initial_segment hU T
  have ha : (x₀, 0) ∈ A := hseg
  let N : E × E → E × E := fun q => (q.1, (Φ (T, q)).1)
  have hN : ContDiffOn ℝ ∞ N A :=
    contDiffOn_fst.prodMk ((hΦ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun q (hq : q ∈ A) => hq T ⟨hT.le, le_rfl⟩)).fst)
  have hDN := hasFDerivAt_normalMap_zero_of_invertible hS hG hinv hU hΦ
    hzero hode hx₀ hT hseg
  obtain ⟨e, he, hem, hesub, hesmooth, heinv⟩ :=
    exists_smooth_local_diffeomorph hA hN ha hDN
  exact ⟨{
    time := T
    time_pos := hT
    domain := U
    domain_open := hU
    flow := Φ
    flow_smooth := hΦ
    initial := hzero
    ode := hode
    normal := e
    normal_apply := fun q => congrFun he q
    center_mem := hem
    source_stays := fun q hq => hesub hq
    inverse_smooth := hesmooth
    normal_derivative_invertible := fun q hq => by simpa only [he] using heinv q hq
  }⟩

theorem normalAt_zero_of_invertible (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hinv : ∀ z ∈ S, (G z).IsInvertible)
    {x : E} (hx : (0 : E) ∈ (N.normalAt x).source) : N.normalAt x 0 = x := by
  have he := FlowLinearization.equilibrium N.domain_open
    (N.flow_smooth.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top))
    (hS.prod isOpen_univ) ((contDiffOn_geodesicSpray_of_invertible hS hG hinv).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top))
    N.initial (fun q hq => ⟨⟨(N.ode q hq).1, mem_univ _⟩, (N.ode q hq).2⟩)
    (x := (x, 0)) ⟨N.base_mem hx, mem_univ _⟩ (geodesicSpray_zero G x)
    N.time_pos.le (N.source_stays (x, 0) hx)
  rw [N.normalAt_apply, he N.time ⟨N.time_pos.le, le_rfl⟩]

section Variation
variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem parameter_variation_hasDerivAt {Φ Ψ : ℝ × P → F} {U : Set (ℝ × P)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (htime : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (Ψ q) q.1)
    {T : ℝ} {x w : P} (hTx : (T, x) ∈ U)
    (hΨ : DifferentiableAt ℝ Ψ (T, x)) :
    HasDerivAt (fun t => fderiv ℝ Φ (t, x) (0, w))
      (fderiv ℝ Ψ (T, x) (0, w)) T := by
  have hc := (hΦ (T, x) hTx).contDiffAt (hU.mem_nhds hTx)
  have hdD : DifferentiableAt ℝ (fderiv ℝ Φ) (T, x) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hdD.hasFDerivAt.clm_apply (hasFDerivAt_const (1, 0) (T, x))
  have heq : (fun q => fderiv ℝ Φ q (1, 0)) =ᶠ[𝓝 (T, x)] Ψ := by
    filter_upwards [hU.mem_nhds hTx] with q hq
    exact (hasDerivAt_time_slice (((hΦ q hq).contDiffAt (hU.mem_nhds hq)).differentiableAt
      (by norm_num))).unique (htime q hq)
  have he := congrArg (fun L : (ℝ × P) →L[ℝ] F => L (0, w))
    (hA.unique (hΨ.hasFDerivAt.congr_of_eventuallyEq heq))
  have hs := hc.isSymmSndFDerivAt (by simp) (1, 0) (0, w)
  have hd := ((hasDerivAt_time_slice hdD).hasFDerivAt.clm_apply (hasFDerivAt_const (0, w) T)).hasDerivAt
  convert! hd using 1
  simpa [hs] using he.symm

end Variation

theorem geodesic_pairing_hasDerivAt {G : E → MetricTensor E}
    {c V J : ℝ → E} {t : ℝ} {W : E}
    (hG : DifferentiableAt ℝ G (c t))
    (hinv : (G (c t)).IsInvertible)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t)
    (hJ : HasDerivAt J W t) :
    HasDerivAt (fun r => G (c r) (V r) (J r))
      (fderiv ℝ G (c t) (J t) (V t) (V t) / 2 + G (c t) (V t) W) t := by
  have hd := hasDerivAt_metric_pairing hG hc hV hJ
  have hm := metric_christoffel_of_invertible hinv (V t) (V t) (J t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

omit [FiniteDimensional ℝ E] in
theorem parameter_hasDerivAt {c : ℝ × ℝ → E} {t s : ℝ}
    (hc : DifferentiableAt ℝ c (t, s)) :
    HasDerivAt (fun r => c (t, r)) (fderiv ℝ c (t, s) (0, 1)) s := by
  convert! hc.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)) using 1

theorem geodesic_fan_pairing {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {c V : ℝ × ℝ → E} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hc : ContDiffOn ℝ 2 c U) (hV : ContDiffOn ℝ 1 V U)
    (hmem : ∀ q ∈ U, c q ∈ S)
    (hct : ∀ q ∈ U, HasDerivAt (fun t => c (t, q.2)) (V q) q.1)
    (hVt : ∀ q ∈ U, HasDerivAt (fun t => V (t, q.2))
      (-christoffel G (c q) (V q) (V q)) q.1)
    {T : ℝ} (hT : 0 ≤ T) {P : Set ℝ} (hP : P ∈ 𝓝 (0 : ℝ))
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P, (t, s) ∈ U)
    {x v w : E} (hc0 : ∀ s ∈ P, c (0, s) = x)
    (hV0 : ∀ s ∈ P, V (0, s) = v + s • w) :
    ∀ t ∈ Icc (0 : ℝ) T,
      G (c (t, 0)) (V (t, 0)) (fderiv ℝ c (t, 0) (0, 1)) = t * G x v w := by
  have hP0 : (0 : ℝ) ∈ P := mem_of_mem_nhds hP
  have h00 : (0, (0 : ℝ)) ∈ U := hseg 0 ⟨le_rfl, hT⟩ 0 hP0
  have hx : x ∈ S := by simpa only [hc0 0 hP0] using hmem _ h00
  let J : ℝ → E := fun t => fderiv ℝ c (t, 0) (0, 1)
  let W : ℝ → E := fun t => fderiv ℝ V (t, 0) (0, 1)
  have hq : ∀ t ∈ Icc (0 : ℝ) T, (t, (0 : ℝ)) ∈ U := fun t ht => hseg t ht 0 hP0
  have hCdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ c (t, 0) :=
    fun t ht => ((hc _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hVdiff : ∀ t ∈ Icc (0 : ℝ) T, DifferentiableAt ℝ V (t, 0) :=
    fun t ht => ((hV _ (hq t ht)).contDiffAt (hU.mem_nhds (hq t ht))).differentiableAt (by norm_num)
  have hdJ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt J (W t) t := by
    intro t ht
    exact parameter_variation_hasDerivAt hU hc hct (hq t ht) (hVdiff t ht)
  have henergy : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ P,
      G (c (t, s)) (V (t, s)) (V (t, s)) = G x (v + s • w) (v + s • w) := by
    intro t ht s hs
    have he := geodesic_energy_constant_of_invertible hS hG hsym hinv
      (fun r hr => hmem _ (hseg r hr s hs))
      (fun r hr => hct _ (hseg r hr s hs)) (fun r hr => hVt _ (hseg r hr s hs)) t ht
    simpa only [hc0 s hs, hV0 s hs] using he
  have henergyD : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
        2 * G (c (t, 0)) (V (t, 0)) (W t) = 2 * G x v w := by
    intro t ht
    have hGs := (hG _ (hmem _ (hq t ht))).differentiableAt (hS.mem_nhds (hmem _ (hq t ht)))
    have hdL := hasDerivAt_metric_pairing hGs
      (parameter_hasDerivAt (hCdiff t ht)) (parameter_hasDerivAt (hVdiff t ht))
      (parameter_hasDerivAt (hVdiff t ht))
    have hdR := hasDerivAt_metric_pairing ((hG x hx).differentiableAt (hS.mem_nhds hx))
      (hasDerivAt_const (0 : ℝ) x)
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
    have heq : (fun s => G (c (t, s)) (V (t, s)) (V (t, s))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => G x (v + s • w) (v + s • w)) := by
      filter_upwards [hP] with s hs
      exact henergy t ht s hs
    have he := hdL.unique (hdR.congr_of_eventuallyEq heq)
    simp only [id_eq, zero_smul, add_zero, map_zero, zero_apply, zero_add, one_smul] at he
    rw [hsym _ (hmem _ (hq t ht)) (W t) (V (t, 0)), hsym x hx w v] at he
    change fderiv ℝ G (c (t, 0)) (J t) (V (t, 0)) (V (t, 0)) +
      G (c (t, 0)) (V (t, 0)) (W t) + G (c (t, 0)) (V (t, 0)) (W t) =
      G x v w + G x v w at he
    linarith
  have hJ0 : J 0 = 0 := by
    have heq : (fun s => c (0, s)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => x) := by
      filter_upwards [hP] with s hs
      exact hc0 s hs
    exact (parameter_hasDerivAt (hCdiff 0 ⟨le_rfl, hT⟩)).unique
      ((hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq heq)
  have hpair : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivAt (fun r => G (c (r, 0)) (V (r, 0)) (J r)) (G x v w) t := by
    intro t ht
    have hm := hmem _ (hq t ht)
    have hd := geodesic_pairing_hasDerivAt (c := fun r => c (r, 0)) (V := fun r => V (r, 0)) (J := J) ((hG _ hm).differentiableAt (hS.mem_nhds hm))
      (hinv _ hm) (hct _ (hq t ht)) (hVt _ (hq t ht)) (hdJ t ht)
    convert! hd using 1
    linarith [henergyD t ht]
  have hconst := constant_of_has_deriv_right_zero
    (f := fun t => G (c (t, 0)) (V (t, 0)) (J t) - t * G x v w)
    (fun t ht => ((hpair t ht).sub ((hasDerivAt_id t).mul_const (G x v w))).continuousAt.continuousWithinAt)
    (fun t ht => by
      convert! ((hpair t (Ico_subset_Icc_self ht)).sub
        ((hasDerivAt_id t).mul_const (G x v w))).hasDerivWithinAt using 1; simp)
  intro t ht
  have he := hconst t ht
  simp only [hJ0, map_zero, zero_mul, sub_zero] at he
  exact sub_eq_zero.mp he

theorem terminal_pairing {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hinv : ∀ x ∈ S, (G x).IsInvertible)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1)
    {x v : E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
    G (Φ (T, (x, v))).1
      (Φ (T, (x, v))).2
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T * G x v w := by
  let χ : ℝ × ℝ → ℝ × (E × E) := fun q => (q.1, (x, v + q.2 • w))
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_fst.prodMk (contDiff_const.prodMk (contDiff_const.add
      (contDiff_snd.smul contDiff_const)))
  let W : Set (ℝ × ℝ) := χ ⁻¹' U
  have hW : IsOpen W := hU.preimage hχ.continuous
  let c : ℝ × ℝ → E := fun q => (Φ (χ q)).1
  let V : ℝ × ℝ → E := fun q => (Φ (χ q)).2
  have hcomp : ContDiffOn ℝ ∞ (Φ ∘ χ) W :=
    hΦ.comp hχ.contDiffOn (fun _ hq => hq)
  have hc : ContDiffOn ℝ 2 c W := hcomp.fst.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hV : ContDiffOn ℝ 1 V W := hcomp.snd.of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T, (t, s) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hm : χ (t, 0) ∈ U := by simpa [χ] using hseg t ht
    have hh := ((hχ.continuous.comp continuous_swap).continuousAt (x := (0, t))).preimage_mem_nhds
      (hU.mem_nhds hm)
    exact hh
  let P : Set ℝ := {s | ∀ t ∈ Icc (0 : ℝ) T, (t, s) ∈ W}
  have hP : P ∈ 𝓝 (0 : ℝ) := hnear
  have hfan := geodesic_fan_pairing hS
    (hG.differentiableOn (by simp)) hsym hinv hW hc hV
    (fun q hq => (hode (χ q) hq).1)
    (fun q hq => (hode (χ q) hq).2.fst)
    (fun q hq => (hode (χ q) hq).2.snd) hT hP
    (fun t ht s hs => hs t ht)
    (x := x) (v := v) (w := w)
    (fun s hs => congrArg Prod.fst (hzero (x, v + s • w) (hs 0 ⟨le_rfl, hT⟩)))
    (fun s hs => congrArg Prod.snd (hzero (x, v + s • w) (hs 0 ⟨le_rfl, hT⟩)))
    T ⟨hT, le_rfl⟩
  have hterm : (T, (x, v)) ∈ U := hseg T ⟨hT, le_rfl⟩
  have hdΦ := ((hΦ _ hterm).contDiffAt (hU.mem_nhds hterm)).differentiableAt
    (by simp)
  have hdχ : HasFDerivAt χ
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        ((0 : ℝ × ℝ →L[ℝ] E).prod
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight w))) (T, 0) := by
    exact (hasFDerivAt_fst (p := (T, (0 : ℝ)))).prodMk
      ((hasFDerivAt_const x (T, (0 : ℝ))).prodMk
        (((hasFDerivAt_snd (p := (T, (0 : ℝ)))).smul_const w).const_add v))
  have hdΦ' : HasFDerivAt Φ (fderiv ℝ Φ (T, (x, v))) (χ (T, 0)) := by
    simpa [χ] using hdΦ.hasFDerivAt
  have hdc : HasFDerivAt c _ (T, (0 : ℝ)) := (hdΦ'.comp (T, (0 : ℝ)) hdχ).fst
  have hdval : fderiv ℝ c (T, 0) (0, 1) =
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 := by
    rw [hdc.fderiv]
    simp [ContinuousLinearMap.comp_apply]

  simpa only [c, V, χ, zero_smul, add_zero, hdval] using hfan

/-- Initial velocity of the geodesic from x to y in the local inverse of the normal map. -/
def logVec (N : NormalFlow G S x₀) (x y : E) : E := ((N.normalAt x).symm y)

/-- The signed squared norm of the initial velocity in these normal coordinates. -/
def initialEnergy (N : NormalFlow G S x₀) (x y : E) := G x (logVec N x y) (logVec N x y)

/-- Final velocity, evaluated in the same affine time parameter as the geodesic flow. -/
def terminalVelocity (N : NormalFlow G S x₀) (x y : E) :=
  (N.flow (N.time,(x,logVec N x y))).2

theorem normal_terminal_pairing (N : NormalFlow G S x₀) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) (hsym : ∀ x∈S, ∀ v w, G x v w=G x w v)
    (hinv : ∀ x∈S, (G x).IsInvertible) {x v : E} (hv : v∈(N.normalAt x).source) (w : E) :
    G (N.normalAt x v) (N.flow (N.time,(x,v))).2 (fderiv ℝ (N.normalAt x) v w) = N.time*G x v w := by
  have htv := N.source_stays (x,v) hv N.time ⟨N.time_pos.le,le_rfl⟩
  have hdΦ := ((N.flow_smooth _ htv).contDiffAt (N.domain_open.mem_nhds htv)).differentiableAt (by simp)
  have hpath : HasFDerivAt (fun v' : E => (N.time,(x,v')))
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (.id ℝ E))) v :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id v))
  have hd := hdΦ.hasFDerivAt.comp v hpath
  have hde : HasFDerivAt (N.normalAt x)
      ((ContinuousLinearMap.fst ℝ E E).comp ((fderiv ℝ N.flow (N.time,(x,v))).comp
        ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (.id ℝ E))))) v := by
    convert! hd.fst using 1
    ext z
    exact N.normalAt_apply x z
  rw [hde.fderiv,N.normalAt_apply]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,zero_apply,ContinuousLinearMap.id_apply]
  exact terminal_pairing hS hG hsym hinv N.domain_open N.flow_smooth N.initial N.ode
    N.time_pos.le (N.source_stays (x,v) hv) w

theorem initialEnergy_deriv (N : NormalFlow G S x₀) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) (hsym : ∀ x∈S, ∀ v w, G x v w=G x w v)
    (hinv : ∀ x∈S, (G x).IsInvertible) {x : E} {c : ℝ → E} {t : ℝ} {c' : E}
    (ht : c t ∈ (N.normalAt x).target) (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s => initialEnergy N x (c s)) ((2/N.time)*G (c t) (terminalVelocity N x (c t)) c') t := by
  let e := N.normalAt x
  let v := e.symm (c t)
  have hv : v ∈ e.source := e.map_target ht
  have hdi := ((N.normalAt_inverse_smooth x _ ht).contDiffAt
    (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  let w := fderiv ℝ e.symm (c t) c'
  have hdv : HasDerivAt (fun s => e.symm (c s)) w t := hdi.hasFDerivAt.comp_hasDerivAt t hc
  have hdf := ((N.normalAt_smooth x _ hv).contDiffAt (e.open_source.mem_nhds hv)).differentiableAt (by simp)
  have hforward := hdf.hasFDerivAt.comp_hasDerivAt t hdv
  have heq : (fun s => e (e.symm (c s))) =ᶠ[𝓝 t] c := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds ht)] with s hs
    exact e.right_inv hs
  have hD : fderiv ℝ e v w = c' := (hforward.congr_of_eventuallyEq heq.symm).unique hc
  have hpair := normal_terminal_pairing N hS hG hsym hinv hv w
  change G (e v) (terminalVelocity N x (c t)) (fderiv ℝ e v w) = N.time*G x v w at hpair
  rw [hD,show e v = c t from e.right_inv ht] at hpair
  have hraw := hasDerivAt_metric_pairing (G := G)
    (((hG x (N.base_mem hv)).contDiffAt (hS.mem_nhds (N.base_mem hv))).differentiableAt (by simp))
    (hasDerivAt_const t x) hdv hdv
  apply hraw.congr_deriv
  change fderiv ℝ G x 0 v v + G x w v + G x v w = _
  rw [map_zero,zero_apply,zero_apply,zero_add,hsym x (N.base_mem hv) w v,hpair]
  field_simp [N.time_pos.ne']
  <;> ring

theorem logVec_continuousAt (N : NormalFlow G S x₀) {z : E×E} (h : z ∈ N.normal.target) :
    ContinuousAt (fun p : E×E => logVec N p.1 p.2) z :=
  (N.normal.continuousOn_symm.continuousAt (N.normal.open_target.mem_nhds h)).snd

theorem normal_center (N : NormalFlow G S x₀) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) (hinv : ∀ x∈S, (G x).IsInvertible) {x : E}
    (hx : (x,(0:E)) ∈ N.normal.source) : N.normal (x,0) = (x,x) := by
  rw [N.normal_apply]
  apply Prod.ext
  · rfl
  · simpa only [N.normalAt_apply] using normalAt_zero_of_invertible N hS hG hinv hx

theorem logVec_base_deriv (N : NormalFlow G S x₀) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G S) (hinv : ∀ x∈S, (G x).IsInvertible) {x : E}
    (hx : (x,(0:E)) ∈ N.normal.source) (w : E) :
    HasDerivAt (fun s : ℝ => logVec N (x-s • w) x) (N.time⁻¹ • w) 0 := by
  have hdiag := normal_center N hS hG hinv hx
  have htar : (x,x)∈N.normal.target := hdiag ▸ N.normal.map_source hx
  have hi : N.normal.symm (x,x)=(x,0) := hdiag ▸ N.normal.left_inv hx
  let L := normalShear (E:=E) N.time N.time_pos.ne'
  have hN : HasFDerivAt N.normal (L : E×E →L[ℝ] E×E) (N.normal.symm (x,x)) := by
    rw [hi]
    have hd := hasFDerivAt_normalMap_zero_of_invertible hS hG hinv N.domain_open N.flow_smooth
      N.initial N.ode (N.base_mem hx) N.time_pos (N.source_stays (x,0) hx)
    have he : (N.normal : E×E → E×E) = fun q => (q.1,(N.flow (N.time,q)).1) := funext N.normal_apply
    rw [he]
    exact hd
  have hNi := N.normal.hasFDerivAt_symm htar hN
  have hp : HasDerivAt (fun s : ℝ => (x-s • w,x)) (-w,0) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).smul_const w).const_sub x).prodMk (hasDerivAt_const 0 x)
  have hd : HasFDerivAt N.normal.symm (L.symm : E×E →L[ℝ] E×E) (x-(0:ℝ) • w,x) := by simpa using hNi
  have hcomp := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt 0 (hd.comp_hasDerivAt 0 hp)
  apply hcomp.congr_deriv
  change N.time⁻¹ • ((0:E)- -w) = _
  simp

theorem flow_energy (N : NormalFlow G S x₀) (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x∈S, ∀ v w, G x v w=G x w v) (hinv : ∀ x∈S, (G x).IsInvertible)
    {x v : E} (hv : (x,v)∈N.normal.source) {t : ℝ} (ht : t∈Icc (0:ℝ) N.time) :
    G (N.flow (t,(x,v))).1 (N.flow (t,(x,v))).2 (N.flow (t,(x,v))).2 = G x v v := by
  have h := geodesic_energy_constant_of_invertible hS (hG.differentiableOn (by simp)) hsym hinv
    (fun t ht => (N.ode _ (N.source_stays (x,v) hv t ht)).1)
    (fun t ht => (N.ode _ (N.source_stays (x,v) hv t ht)).2.fst)
    (fun t ht => (N.ode _ (N.source_stays (x,v) hv t ht)).2.snd) t ht
  simpa only [N.initial (x,v) (N.source_stays (x,v) hv 0 ⟨le_rfl,N.time_pos.le⟩),geodesicSpray] using h

end
end NoHair.PseudoNormal


