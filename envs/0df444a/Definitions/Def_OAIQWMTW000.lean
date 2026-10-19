-- Prove2me | Definitions.Def_OAIQWMTW000
-- name    : OAIQWMTW000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:07.694758+00:00
-- url     : https://prove2.me/theorems/098c75b2-ec66-4626-b7e4-afb13e34e088
-- title:
--   OpenAI weak MTW split: definitions bundle OAIQWMTW000
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWGlobalSupport.current_main_convexity`. That theorem says that on a compact connected Riemannian manifold of dimension at least two satisfying the weak Ma–Trudinger–Wang condition, every tangent injectivity domain is convex (Villani's conjecture in this setting).
--
--   The bundle holds OpenAI's Lean definitions, structures and predicates from the modules `Coordinates_CoordinateGeometry`, `Geodesics_InitialScaling`, `Variations_CurveCalculus`, `Variations_FlowLinearization` of `lean/OAI/Geometry/WeakMTW` (OpenAI, *Global Support and Convex Injectivity Domains under Weak MTW*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. It imports no other bundle of this split.
--
--   Its definitions are the coordinate Riemannian geometry that the standalone statement `OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma` writes out. They are a metric tensor field as a field of continuous bilinear forms (`MetricTensor`), the Christoffel map lowered and raised (`lowerChristoffel`, `christoffel`), the geodesic spray $(x, v) \mapsto (v, -\Gamma_x(v, v))$ (`geodesicSpray`), and the rescaling of a phase point $(x, v) \mapsto (x, sv)$ (`scalePhase`).
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakMTW at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_CoordinateGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace CoordinateGeometry
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev MetricTensor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ

theorem metric_invertible {G : MetricTensor E}
    (hG : ∀ v : E, v ≠ 0 → 0 < G v v) : G.IsInvertible := by
  have hinj : Function.Injective G := by
    apply (G : E →ₗ[ℝ] E →L[ℝ] ℝ).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot.mpr
    apply (injective_iff_map_eq_zero G).mpr
    intro v hv
    by_contra hn
    have hp := hG v hn
    exact (lt_irrefl (0 : ℝ)) (by simpa only [hv, zero_apply] using hp)
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    (toDual ℝ E).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective G :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective G
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), rfl⟩

def lowerChristoffel (D : E →L[ℝ] MetricTensor E) (v w : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (D v w + D w v - (D.flip v).flip w)

omit [FiniteDimensional ℝ E] in
@[simp] theorem lowerChristoffel_apply (D : E →L[ℝ] MetricTensor E) (v w z : E) :
    lowerChristoffel D v w z = (D v w z + D w v z - D z v w) / 2 := by
  simp [lowerChristoffel, div_eq_mul_inv, mul_comm]

def christoffel (G : E → MetricTensor E) (x v w : E) : E :=
  (G x).inverse (lowerChristoffel (fderiv ℝ G x) v w)

def geodesicSpray (G : E → MetricTensor E) (q : E × E) : E × E :=
  (q.2, -christoffel G q.1 q.2 q.2)

variable {G : E → MetricTensor E} {S : Set E}

theorem metric_christoffel {x : E} (hpos : ∀ v : E, v ≠ 0 → 0 < G x v v)
    (v w z : E) :
    G x (christoffel G x v w) z =
      (fderiv ℝ G x v w z + fderiv ℝ G x w v z - fderiv ℝ G x z v w) / 2 := by
  unfold christoffel
  rw [(metric_invertible hpos).self_apply_inverse, lowerChristoffel_apply]

omit [FiniteDimensional ℝ E] in
theorem derivative_metric_symmetric (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v) {x : E} (hx : x ∈ S)
    (a v w : E) : fderiv ℝ G x a v w = fderiv ℝ G x a w v := by
  have hd := (hG x hx).differentiableAt (hS.mem_nhds hx)
  have h₁ := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  have h₂ := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).clm_apply (hasFDerivAt_const v x)
  have heq : (fun y => G y v w) =ᶠ[𝓝 x] (fun y => G y w v) := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact hsym y hy v w
  simpa using congrArg (fun L : E →L[ℝ] ℝ => L a)
    (h₁.unique (h₂.congr_of_eventuallyEq heq))

theorem metric_compatible (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {x : E} (hx : x ∈ S) (v w z : E) :
    fderiv ℝ G x v w z = G x (christoffel G x v w) z + G x w (christoffel G x v z) := by
  rw [hsym x hx w, metric_christoffel (hpos x hx), metric_christoffel (hpos x hx)]
  rw [derivative_metric_symmetric hS hG hsym hx v z w,
    derivative_metric_symmetric hS hG hsym hx z v w,
    derivative_metric_symmetric hS hG hsym hx w v z]
  ring

theorem contDiffOn_metric_inverse (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v) :
    ContDiffOn ℝ ∞ (fun x => (G x).inverse) S := by
  intro x hx
  obtain ⟨e, he⟩ := metric_invertible (hpos x hx)
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (G x) := by
    rw [← he]
    exact contDiffAt_map_inverse e
  exact (hi.comp x ((hG x hx).contDiffAt (hS.mem_nhds hx))).contDiffWithinAt

theorem contDiffOn_geodesicSpray (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v) :
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
    (contDiffOn_metric_inverse hS hG hpos).comp contDiffOn_fst (fun q hq => hq.1)
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

omit [FiniteDimensional ℝ E] in
theorem hasDerivAt_metric_pairing {c V W : ℝ → E} {t : ℝ} {c' V' W' : E}
    (hG : DifferentiableAt ℝ G (c t)) (hc : HasDerivAt c c' t)
    (hV : HasDerivAt V V' t) (hW : HasDerivAt W W' t) :
    HasDerivAt (fun r => G (c r) (V r) (W r))
      (fderiv ℝ G (c t) c' (V t) (W t) + G (c t) V' (W t) + G (c t) (V t) W') t := by
  have hgc : HasFDerivAt (fun r => G (c r))
      ((fderiv ℝ G (c t)).comp (ContinuousLinearMap.toSpanSingleton ℝ c')) t :=
    HasFDerivAt.comp (f := c) (g := G) t hG.hasFDerivAt hc.hasFDerivAt
  have hgv := hgc.clm_apply hV.hasFDerivAt
  have hd := (hgv.clm_apply hW.hasFDerivAt).hasDerivAt
  convert! hd using 1
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]
  ring

theorem geodesic_energy_hasDerivAt_zero (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ → E} {t : ℝ} (ht : c t ∈ S)
    (hc : HasDerivAt c (V t) t)
    (hV : HasDerivAt V (-christoffel G (c t) (V t) (V t)) t) :
    HasDerivAt (fun r => G (c r) (V r) (V r)) 0 t := by
  have hd := hasDerivAt_metric_pairing ((hG (c t) ht).differentiableAt (hS.mem_nhds ht)) hc hV hV
  have hm := metric_compatible hS hG hsym hpos ht (V t) (V t) (V t)
  convert! hd using 1
  simp only [map_neg, neg_apply]
  linarith

theorem geodesic_energy_constant (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {c V : ℝ → E} {a b : ℝ}
    (hmem : ∀ t ∈ Icc a b, c t ∈ S)
    (hc : ∀ t ∈ Icc a b, HasDerivAt c (V t) t)
    (hV : ∀ t ∈ Icc a b, HasDerivAt V (-christoffel G (c t) (V t) (V t)) t) :
    ∀ t ∈ Icc a b, G (c t) (V t) (V t) = G (c a) (V a) (V a) := by
  have hd := fun t ht => geodesic_energy_hasDerivAt_zero hS hG hsym hpos (hmem t ht) (hc t ht) (hV t ht)
  exact constant_of_has_deriv_right_zero (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

omit [FiniteDimensional ℝ E] in
@[simp] theorem christoffel_zero_left (G : E → MetricTensor E) (x v : E) :
    christoffel G x 0 v = 0 := by
  simp [christoffel, lowerChristoffel]

omit [FiniteDimensional ℝ E] in
@[simp] theorem christoffel_zero_right (G : E → MetricTensor E) (x v : E) :
    christoffel G x v 0 = 0 := by
  simp [christoffel, lowerChristoffel]

omit [FiniteDimensional ℝ E] in
@[simp] theorem geodesicSpray_zero (G : E → MetricTensor E) (x : E) :
    geodesicSpray G (x, 0) = 0 := by
  simp [geodesicSpray]

end
end CoordinateGeometry

open Set Filter
open scoped Topology ContDiff

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_CurveCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace VariationCalculus

variable {P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_time_slice {Φ : ℝ × P → F} {t : ℝ} {x : P}
    (hΦ : DifferentiableAt ℝ Φ (t, x)) :
    HasDerivAt (fun r => Φ (r, x)) (fderiv ℝ Φ (t, x) (1, 0)) t := by
  have hd := hΦ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  convert! hd using 1

end VariationCalculus

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_FlowLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace FlowLinearization
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem unique_Icc {f : E → E} {u v : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hf : ∀ z ∈ u '' Icc a b ∪ v '' Icc a b, ContDiffAt ℝ 1 f z)
    (hdu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t)
    (hdv : ∀ t ∈ Icc a b, HasDerivWithinAt v (f (v t)) (Icc a b) t)
    (h0 : u a = v a) : EqOn u v (Icc a b) := by
  let S := u '' Icc a b ∪ v '' Icc a b
  have hS : IsCompact S := (isCompact_Icc.image_of_continuousOn hu).union
    (isCompact_Icc.image_of_continuousOn hv)
  have hloc : LocallyLipschitzOn S f := by
    intro z hz
    obtain ⟨K, A, hA, hLip⟩ := (hf z hz).exists_lipschitzOnWith
    exact ⟨K, A, mem_nhdsWithin_of_mem_nhds hA, hLip⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc_right (fun _ _ => hK) hu
    (fun t ht => (hdu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inl (mem_image_of_mem _ (Ico_subset_Icc_self ht))) hv
    (fun t ht => (hdv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inr (mem_image_of_mem _ (Ico_subset_Icc_self ht))) h0

end
end FlowLinearization

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_InitialScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace GeodesicScaling
open Set Filter CoordinateGeometry
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lowerChristoffel_smul_left (D : E →L[ℝ] MetricTensor E) (a : ℝ) (v w : E) :
    lowerChristoffel D (a • v) w = a • lowerChristoffel D v w := by
  ext z
  simp [lowerChristoffel_apply]
  ring

theorem lowerChristoffel_smul_right (D : E →L[ℝ] MetricTensor E) (a : ℝ) (v w : E) :
    lowerChristoffel D v (a • w) = a • lowerChristoffel D v w := by
  ext z
  simp [lowerChristoffel_apply]
  ring

theorem christoffel_smul_smul (G : E → MetricTensor E) (x : E) (a : ℝ) (v w : E) :
    christoffel G x (a • v) (a • w) = a • a • christoffel G x v w := by
  simp only [christoffel, lowerChristoffel_smul_left, lowerChristoffel_smul_right, map_smul]

def scalePhase (s : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E).prod (s • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem scalePhase_apply (s : ℝ) (q : E × E) : scalePhase s q = (q.1, s • q.2) := rfl
@[simp] theorem scalePhase_one (q : E × E) : scalePhase 1 q = q := by simp

theorem scale_spray (G : E → MetricTensor E) (s : ℝ) (q : E × E) :
    scalePhase s (s • geodesicSpray G q) = geodesicSpray G (scalePhase s q) := by
  simp [scalePhase, geodesicSpray, christoffel_smul_smul]

end
end GeodesicScaling

end

end WeakMTWGlobalSupport

end OAI
end


