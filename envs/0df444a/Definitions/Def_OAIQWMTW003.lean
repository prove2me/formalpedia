-- Prove2me | Definitions.Def_OAIQWMTW003
-- name    : OAIQWMTW003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T03:09:24.977788+00:00
-- url     : https://prove2.me/theorems/82963f99-6318-4c72-b4e5-240fb78c8e14
-- title:
--   OpenAI weak MTW split: definitions bundle OAIQWMTW003
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakMTWGlobalSupport.current_main_convexity`. That theorem says that on a compact connected Riemannian manifold of dimension at least two satisfying the weak Ma–Trudinger–Wang condition, every tangent injectivity domain is convex (Villani's conjecture in this setting).
--
--   The bundle holds OpenAI's Lean definitions, structures and predicates from the modules `Coordinates_ChartGlobalVariation`, `Coordinates_FanCoordinates`, `Coordinates_PairExpCoordinates`, `Geodesics_CompactGeodesic`, `Geodesics_CompleteExistence`, `Geodesics_GeodesicFlow`, `Geodesics_IntrinsicExp`, `Geodesics_IntrinsicGlue`, `Geodesics_IntrinsicOn`, `Geodesics_IntrinsicUniqueness`, `Geodesics_ShortChartAction`, `Geodesics_ShortFlowCoordinates`, `Variations_ActionBranch`, `Variations_ActionHessian`, `Variations_BranchAction`, `Variations_BranchHessian`, `Variations_GeneratingAction`, `Variations_GeneratingHessian`, `Variations_GeneratingNeighborhood` of `lean/OAI/Geometry/WeakMTW` (OpenAI, *Global Support and Convex Injectivity Domains under Weak MTW*, OpenAI Math Release, September 25, 2026, result family 360, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. It also imports the bundles `OAIQWMTW001`, `OAIQWMTW002` of this split.
--
--   Among its definitions:
--   - the complete geodesic with given initial data on a compact manifold and the geodesic flow (`geodesic`, `geodesicFlow`). `geodesic` is chosen from the existence theorem `completeGeodesic_exists`, which the bundle proves;
--   - geodesic fans and their coordinates (`geodesicFan`, `fanCoordinates`, `fanDomain`, `fanMomentum`, `flowCoordinates`, `crossFlowCoordinates`);
--   - exponential coordinates on pairs of points (`pairExpCoordinates`, `pairExpDomain`);
--   - minimizing branches, their action and Hessians (`ActionBranch`, `branchAction`, `actionHessian`, `branchHessianDiag`, `ShortChartAction`, `chartKinetic`);
--   - generating actions and their Hessians (`generatingAction`, `GeneratingChartAction`, `generatingHessian`).
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakMTW at commit adc7f12

import Mathlib
import Definitions.Def_WeakMTWGlobalSupport
import Definitions.Def_OAIQWMTW001
import Definitions.Def_OAIQWMTW002

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
 theorem curveState_congr {γ η : ℝ → M} {a : ℝ} (h : γ =ᶠ[𝓝 a] η) :
    curveState (E := E) γ a = curveState (E := E) η a := by
  refine TotalSpace.ext h.eq_of_nhds ?_
  apply heq_of_eq
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ a (1 : ℝ) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η a (1 : ℝ)
  rw [h.mfderiv_eq]
  rfl

 theorem curveState_chart_deriv (x : M) {γ : ℝ → M} {a : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ a)
    (ha : γ a ∈ (chartAt E x).source) :
    deriv ((chartAt E x) ∘ γ) a =
      (tangentMap 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) (curveState (E := E) γ a)).2 := by
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
  rw [mfderiv_comp a (mdifferentiableAt_atlas (chart_mem_atlas E x) ha) hγ]
  rfl

end

end
end RiemannianLocal

end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem intrinsic_germ_unique_on {V : Set ℝ} (hV : IsOpen V) {γ η : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ V)
    (hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ η V)
    {a C D : ℝ} (haV : a ∈ V) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hcDist : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (γ s) (γ t) = C * |s - t|)
    (hdDist : ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball a ε, ∀ t ∈ Metric.ball a ε,
      dist (η s) (η t) = D * |s - t|)
    (he : curveState (E := E) γ a = curveState (E := E) η a) : γ =ᶠ[𝓝 a] η := by
  let x := γ a
  let e := chartAt E x
  have hpoint : γ a = η a := congrArg TotalSpace.proj he
  have hγa : γ a ∈ e.source := mem_chart_source E (γ a)
  have hηa : η a ∈ e.source := by rw [← hpoint]; exact hγa
  obtain ⟨ε, hε, hcs⟩ := hcDist
  obtain ⟨δ, hδ, hds⟩ := hdDist
  let U : Set ℝ := V ∩ (Metric.ball a ε ∩ Metric.ball a δ ∩
    (γ ⁻¹' e.source ∩ η ⁻¹' e.source))
  have hU : IsOpen U := by
    have hc := hγ.continuousOn.isOpen_inter_preimage hV e.open_source
    have hd := hη.continuousOn.isOpen_inter_preimage hV e.open_source
    convert! (hc.inter hd).inter ((Metric.isOpen_ball (x := a) (ε := ε)).inter (Metric.isOpen_ball (x := a) (ε := δ))) using 1
    ext t
    simp only [U, mem_inter_iff, mem_preimage]
    tauto
  have ha : a ∈ U := ⟨haV, ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hδ⟩, hγa, hηa⟩
  let c : ℝ → E := e ∘ γ
  let d : ℝ → E := e ∘ η
  have hc : ContDiffOn ℝ ∞ c U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp (hγ.mono inter_subset_left) (fun t ht => ht.2.2.1))
  have hd : ContDiffOn ℝ ∞ d U := contMDiffOn_iff_contDiffOn.mp
    (contMDiffOn_chart.comp (hη.mono inter_subset_left) (fun t ht => ht.2.2.2))
  have hct : ∀ t ∈ U, c t ∈ e.target := fun t ht => e.map_source ht.2.2.1
  have hdt : ∀ t ∈ U, d t ∈ e.target := fun t ht => e.map_source ht.2.2.2
  have he' : deriv c a = deriv d a := by
    rw [curveState_chart_deriv x (((hγ a haV).contMDiffAt (hV.mem_nhds haV)).mdifferentiableAt (by simp)) hγa,
      curveState_chart_deriv x (((hη a haV).contMDiffAt (hV.mem_nhds haV)).mdifferentiableAt (by simp)) hηa, he]
  have hh := coordinate_germ_unique x hU hc hd hct hdt ha hC hD
    (fun s hs t ht => by
      change dist (e.symm (e (γ s))) (e.symm (e (γ t))) = _
      rw [e.left_inv hs.2.2.1, e.left_inv ht.2.2.1]
      exact hcs s hs.2.1.1 t ht.2.1.1)
    (fun s hs t ht => by
      change dist (e.symm (e (η s))) (e.symm (e (η t))) = _
      rw [e.left_inv hs.2.2.2, e.left_inv ht.2.2.2]
      exact hds s hs.2.1.2 t ht.2.1.2)
    (congrArg e hpoint) he'
  filter_upwards [hh, hU.mem_nhds ha] with t ht htU
  have hh' := congrArg e.symm ht
  change e.symm (e (γ t)) = e.symm (e (η t)) at hh'
  rwa [e.left_inv htU.2.2.1, e.left_inv htU.2.2.2] at hh'

section
omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

theorem curveState_continuousOn {U : Set ℝ} (hU : IsOpen U) {γ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ U) :
    ContinuousOn (curveState (E := E) γ) U := by
  have h := hγ.continuousOn_tangentMapWithin (by simp : (1 : ℕ∞ω) ≤ ∞) hU.uniqueMDiffOn
  have hs : Continuous (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hc := h.comp hs.continuousOn (fun t ht => ht)
  apply hc.congr
  intro t ht
  dsimp only [curveState, tangentMapWithin, Function.comp_def]
  rw [mfderivWithin_of_isOpen hU ht]

end

 theorem intrinsic_unique_on {γ η : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C U)
    (hη : IsIntrinsicGeodesicOn (E := E) η D U)
    {a : ℝ} (ha : a ∈ U) (he : curveState (E := E) γ a = curveState (E := E) η a) :
    EqOn γ η U := by
  let : T2Space (TangentBundle 𝓘(ℝ, E) M) := tangentBundle_t2Space
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hUc
  let A : Set U := {t | curveState (E := E) γ t = curveState (E := E) η t}
  have hclosed : IsClosed A := isClosed_eq
    (continuousOn_iff_continuous_domRestrict.mp (curveState_continuousOn hU hγ.1))
    (continuousOn_iff_continuous_domRestrict.mp (curveState_continuousOn hU hη.1))
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hh := intrinsic_germ_unique_on hU hγ.1 hη.1 t.property hC hD
      (hγ.2 t t.property) (hη.2 t t.property) ht
    have hs := hh.eventuallyEq_nhds.mono (fun s hs => curveState_congr (E := E) hs)
    exact continuous_subtype_val.continuousAt hs
  have huniv := (show IsClopen A from ⟨hclosed, hopen⟩).eq_univ ⟨⟨a, ha⟩, he⟩
  intro t ht
  have h : (⟨t, ht⟩ : U) ∈ A := by rw [huniv]; exact mem_univ _
  exact congrArg TotalSpace.proj h

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

section
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem intrinsic_speed_eq_of_germ {γ η : ℝ → M} {C D t : ℝ}
    (hγ : IsIntrinsicGeodesicAt (E := E) γ C t)
    (hη : IsIntrinsicGeodesicAt (E := E) η D t) (he : γ =ᶠ[𝓝 t] η) : C = D := by
  obtain ⟨ε, hε, hc⟩ := hγ.2
  obtain ⟨δ, hδ, hd⟩ := hη.2
  obtain ⟨r, hr, hre⟩ := Metric.eventually_nhds_iff.mp he
  let a := min ε (min δ r) / 2
  have ha : 0 < a := half_pos (lt_min hε (lt_min hδ hr))
  have haε : a < ε := (half_lt_self (lt_min hε (lt_min hδ hr))).trans_le (min_le_left _ _)
  have haδ : a < δ := (half_lt_self (lt_min hε (lt_min hδ hr))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have har : a < r := (half_lt_self (lt_min hε (lt_min hδ hr))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hdist : dist (t + a) t = a := by simp [abs_of_pos ha]
  have he₁ := hre (show dist (t + a) t < r by rw [hdist]; exact har)
  have h₁ := hc (t + a) (by change dist (t+a) t < ε; rwa [hdist]) t (Metric.mem_ball_self hε)
  have h₂ := hd (t + a) (by change dist (t+a) t < δ; rwa [hdist]) t (Metric.mem_ball_self hδ)
  rw [he₁, he.eq_of_nhds, h₂] at h₁
  have habs : |t + a - t| = a := by simp [abs_of_pos ha]
  rw [habs] at h₁
  exact (mul_right_cancel₀ ha.ne' h₁).symm

end

 theorem intrinsic_piecewise {γ η : ℝ → M} {C : ℝ} (hC : 0 ≤ C)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V) (hUV : IsPreconnected (U ∩ V))
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C U)
    (hη : IsIntrinsicGeodesicOn (E := E) η C V)
    {a : ℝ} (ha : a ∈ U ∩ V) (he : curveState (E := E) γ a = curveState (E := E) η a) :
    IsIntrinsicGeodesicOn (E := E) (U.piecewise γ η) C (U ∪ V) := by
  classical
  have heq := intrinsic_unique_on (hU.inter hV) hUV hC hC
    (hγ.mono inter_subset_left) (hη.mono inter_subset_right) ha he
  apply intrinsicOn_of_at
  intro t ht
  by_cases hu : t ∈ U
  · apply (hγ.at hU hu).congr
    filter_upwards [hU.mem_nhds hu] with s hs
    exact piecewise_eq_of_mem U γ η hs
  · have hv : t ∈ V := ht.resolve_left hu
    apply (hη.at hV hv).congr
    filter_upwards [hV.mem_nhds hv] with s hs
    by_cases hsU : s ∈ U
    · rw [piecewise_eq_of_mem U γ η hsU]
      exact heq ⟨hsU, hs⟩
    · exact piecewise_eq_of_notMem U γ η hsU

section
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem curveState_comp_sub {γ : ℝ → M} {t a : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t - a)) :
    curveState (E := E) (fun s => γ (s-a)) t = curveState (E := E) γ (t-a) := by
  refine TotalSpace.ext ?_ ?_
  · rfl
  apply heq_of_eq
  dsimp only [curveState]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ fun s => s-a) t 1 = _
  have hd : HasDerivAt (fun s : ℝ => s-a) 1 t := (hasDerivAt_id t).sub_const a
  have hs : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s-a) t :=
    mdifferentiableAt_iff_differentiableAt.mpr hd.differentiableAt
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (γ ∘ fun s : ℝ => s-a) t =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t-a)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s-a) t) :=
    mfderiv_comp t hγ hs
  rw [hcomp]
  simp only [mfderiv_eq_fderiv]
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (t-a) (fderiv ℝ (fun s : ℝ => s-a) t 1) = _
  rw [fderiv_apply_one_eq_deriv, hd.deriv]

end
end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_CompactGeodesic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem intrinsic_state_norm {γ : ℝ → M} {C t : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hC : 0 ≤ C) (hγ : IsIntrinsicGeodesicOn (E := E) γ C U) (ht : t ∈ U) :
    ‖(curveState (E := E) γ t).2‖ = C := by
  let v := (curveState (E := E) γ t).2
  obtain ⟨ε, hε, V, _, hxV, hlocal⟩ := uniformly_local_intrinsic (E := E) (γ t) (norm_nonneg v)
  obtain ⟨η, hη₀, hη⟩ := hlocal (γ t) hxV v le_rfl
  let η' : ℝ → M := fun s => η (s-t)
  let W : Set ℝ := (fun s : ℝ => s-t) ⁻¹' Metric.ball 0 ε
  have hW : IsOpen W := Metric.isOpen_ball.preimage (continuous_id.sub continuous_const)
  have htW : t ∈ W := by simpa [W] using (Metric.mem_ball_self hε : (0 : ℝ) ∈ Metric.ball 0 ε)
  have hη' : IsIntrinsicGeodesicOn (E := E) η' ‖v‖ W := hη.comp_sub
  have hstate : curveState (E := E) η' t = curveState (E := E) γ t := by
    have hh := curveState_comp_sub (γ := η) (t := t) (a := t) (by
      simpa only [sub_self] using (((hη.1 0 (Metric.mem_ball_self hε)).contMDiffAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))).mdifferentiableAt (by simp)))
    change curveState (E := E) (fun s => η (s-t)) t = _
    rw [hh, sub_self, hη₀]
    rfl
  have he := intrinsic_germ_unique_on (hU.inter hW)
    (hγ.1.mono inter_subset_left) (hη'.1.mono inter_subset_right) ⟨ht, htW⟩
    hC (norm_nonneg v) (hγ.2 t ht) (hη'.2 t htW) hstate.symm
  exact (intrinsic_speed_eq_of_germ (hγ.at hU ht) (hη'.at hW htW) he).symm

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_CompleteExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]

 theorem shifted_local_intrinsic {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hl : ∀ y : M, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
      ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
        IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Ioo (-ε) ε))
    {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C U) {t : ℝ} (ht : t ∈ U) :
    ∃ η : ℝ → M, curveState (E := E) η t = curveState (E := E) γ t ∧
      IsIntrinsicGeodesicOn (E := E) η C (Ioo (t-ε) (t+ε)) := by
  have hn := intrinsic_state_norm hU hC hγ ht
  obtain ⟨η, hη₀, hη⟩ := hl (γ t) (curveState (E := E) γ t).2 hn.le
  let η' : ℝ → M := fun s => η (s-t)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have he : (fun s : ℝ => s-t) ⁻¹' Ioo (-ε) ε = Ioo (t-ε) (t+ε) := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  refine ⟨η', ?_, ?_⟩
  · have hs := curveState_comp_sub (γ := η) (t := t) (a := t) (by
      simpa only [sub_self] using (((hη.1 0 h0).contMDiffAt
        (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt (by simp)))
    change curveState (E := E) (fun s => η (s-t)) t = _
    rw [hs, sub_self, hη₀]
    rfl
  · have hs := hη.comp_sub (a := t)
    rw [he] at hs
    exact (congrArg (fun speed : ℝ =>
      IsIntrinsicGeodesicOn (E := E) η' speed (Ioo (t-ε) (t+ε))) hn).mp hs

 theorem intrinsic_extend_interval {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hl : ∀ y : M, ∀ v : TangentSpace 𝓘(ℝ, E) y, ‖v‖ ≤ C →
      ∃ γ : ℝ → M, curveState (E := E) γ 0 = ⟨y, v⟩ ∧
        IsIntrinsicGeodesicOn (E := E) γ ‖v‖ (Ioo (-ε) ε))
    {a b : ℝ} (hab : a + ε < b) {γ : ℝ → M}
    (hγ : IsIntrinsicGeodesicOn (E := E) γ C (Ioo a b)) :
    ∃ η : ℝ → M, IsIntrinsicGeodesicOn (E := E) η C (Ioo (a-ε/2) (b+ε/2)) ∧
      EqOn η γ (Ioo a b) := by
  classical
  let t := b-ε/2
  have ht : t ∈ Ioo a b := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  obtain ⟨η, hs, hη⟩ := shifted_local_intrinsic hC hε hl isOpen_Ioo hγ ht
  let δ : ℝ → M := (Ioo a b).piecewise γ η
  have hδ : IsIntrinsicGeodesicOn (E := E) δ C (Ioo a (b+ε/2)) := by
    have hh := intrinsic_piecewise hC isOpen_Ioo isOpen_Ioo
      ((convex_Ioo a b).inter (convex_Ioo (t-ε) (t+ε))).isPreconnected hγ hη
      (show t ∈ Ioo a b ∩ Ioo (t-ε) (t+ε) from ⟨ht, by constructor <;> linarith⟩)
      hs.symm
    have hh' : IsIntrinsicGeodesicOn (E := E) δ C (Ioo a b ∪ Ioo (t-ε) (t+ε)) := by
      convert hh using 1
      funext parameter
      by_cases hparameter : parameter ∈ Ioo a b <;> simp [δ, hparameter]
    apply hh'.mono
    intro s hs
    by_cases hsb : s < b
    · exact Or.inl ⟨hs.1, hsb⟩
    · right
      dsimp [t]
      constructor <;> linarith [hs.2]
  have hδγ : EqOn δ γ (Ioo a b) := fun s hs => piecewise_eq_of_mem _ _ _ hs
  let r := a+ε/2
  have hr : r ∈ Ioo a (b+ε/2) := ⟨by dsimp [r]; linarith, by dsimp [r]; linarith⟩
  obtain ⟨ζ, hrs, hζ⟩ := shifted_local_intrinsic hC hε hl isOpen_Ioo hδ hr
  let β : ℝ → M := (Ioo a (b+ε/2)).piecewise δ ζ
  refine ⟨β, ?_, ?_⟩
  · have hh := intrinsic_piecewise hC isOpen_Ioo isOpen_Ioo
      ((convex_Ioo a (b+ε/2)).inter (convex_Ioo (r-ε) (r+ε))).isPreconnected hδ hζ
      (show r ∈ Ioo a (b+ε/2) ∩ Ioo (r-ε) (r+ε) from ⟨hr, by constructor <;> linarith⟩)
      hrs.symm
    have hh' : IsIntrinsicGeodesicOn (E := E) β C (Ioo a (b+ε/2) ∪ Ioo (r-ε) (r+ε)) := by
      convert hh using 1
      funext parameter
      by_cases hparameter : parameter ∈ Ioo a (b+ε/2) <;> simp [β, hparameter]
    apply hh'.mono
    intro s hs
    by_cases has : a < s
    · exact Or.inl ⟨has, hs.2⟩
    · right
      dsimp [r]
      constructor <;> linarith [hs.1]
  · intro s hs
    rw [show β s = δ s from piecewise_eq_of_mem _ _ _ ⟨hs.1, by linarith [hs.2]⟩]
    exact hδγ hs

 theorem intrinsic_arbitrarily_long [CompactSpace M] (p : TangentBundle 𝓘(ℝ, E) M) :
    ∀ R : ℝ, ∃ γ : ℝ → M, curveState (E := E) γ 0 = p ∧
      IsIntrinsicGeodesicOn (E := E) γ ‖p.2‖ (Ioo (-R) R) := by
  obtain ⟨ε, hε, hl⟩ := compact_uniform_intrinsic (E := E) (M := M) (norm_nonneg p.2)
  have he : ∀ n : ℕ, ∃ γ : ℝ → M, curveState (E := E) γ 0 = p ∧
      IsIntrinsicGeodesicOn (E := E) γ ‖p.2‖
        (Ioo (-(ε + n * (ε/2))) (ε + n * (ε/2))) := by
    intro n
    induction n with
    | zero => simpa using hl p.1 p.2 le_rfl
    | succ n ih =>
      obtain ⟨γ, hγ₀, hγ⟩ := ih
      have hn : 0 ≤ (n : ℝ) * (ε/2) := mul_nonneg (Nat.cast_nonneg _) (by positivity)
      obtain ⟨η, hη, heq⟩ := intrinsic_extend_interval (norm_nonneg p.2) hε hl
        (by linarith : -(ε + n * (ε/2)) + ε < ε + n * (ε/2)) hγ
      refine ⟨η, ?_, ?_⟩
      · rw [← hγ₀]
        apply curveState_congr
        filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(ε+n*(ε/2))) (ε+n*(ε/2))
          from ⟨by linarith, by linarith⟩)] with s hs
        exact heq hs
      · convert hη using 1
        push_cast
        congr 1 <;> ring
  intro R
  obtain ⟨n, hn⟩ := exists_nat_gt ((R - ε) / (ε/2))
  have hr : R < ε + n * (ε/2) := by
    have hh := (div_lt_iff₀ (show 0 < ε/2 by positivity)).mp hn
    linarith
  obtain ⟨γ, hγ₀, hγ⟩ := he n
  exact ⟨γ, hγ₀, hγ.mono (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)⟩

 theorem intrinsic_complete_exists [CompactSpace M] (p : TangentBundle 𝓘(ℝ, E) M) :
    ∃ γ : ℝ → M, curveState (E := E) γ 0 = p ∧
      IsIntrinsicGeodesicOn (E := E) γ ‖p.2‖ univ := by
  classical
  choose η hη₀ hη using intrinsic_arbitrarily_long p
  let γ : ℝ → M := fun t => η (|t|+1) t
  have heq : ∀ R : ℝ, 0 < R → EqOn γ (η R) (Ioo (-R) R) := by
    intro R hR t ht
    have hp : 0 < |t|+1 := by positivity
    have hu : IsOpen (Ioo (-R) R ∩ Ioo (-(|t|+1)) (|t|+1)) := isOpen_Ioo.inter isOpen_Ioo
    have hc := ((convex_Ioo (-R) R).inter (convex_Ioo (-(|t|+1)) (|t|+1))).isPreconnected
    have hz : (0 : ℝ) ∈ Ioo (-R) R ∩ Ioo (-(|t|+1)) (|t|+1) :=
      ⟨⟨by linarith, hR⟩, ⟨by linarith, hp⟩⟩
    have hh := intrinsic_unique_on hu hc (norm_nonneg p.2) (norm_nonneg p.2)
      ((hη (|t|+1)).mono inter_subset_right) ((hη R).mono inter_subset_left) hz
      ((hη₀ (|t|+1)).trans (hη₀ R).symm)
    exact hh ⟨ht, ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩⟩
  have hgerm : ∀ t : ℝ, γ =ᶠ[𝓝 t] η (|t|+1) := by
    intro t
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-(|t|+1)) (|t|+1)
      from ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)] with s hs
    exact heq (|t|+1) (by positivity) hs
  refine ⟨γ, ?_, ?_⟩
  · exact (curveState_congr (hgerm 0)).trans (hη₀ _)
  · apply intrinsicOn_of_at
    intro t _
    exact ((hη (|t|+1)).at isOpen_Ioo
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩).congr (hgerm t)

end
end RiemannianLocal

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

 theorem completeGeodesic_exists [CompactSpace M] (x : M) (v : TangentSpace (model n) x) :
    ∃ γ : ℝ → M, CompleteGeodesicWithInitialData x v γ := by
  obtain ⟨γ, hs, hγ⟩ := intrinsic_complete_exists (E := Model n) (⟨x,v⟩ : TangentBundle (model n) M)
  have hpair := TotalSpace.ext_iff.mp hs
  refine ⟨γ, contMDiffOn_univ.mp hγ.1, hpair.1, ?_, fun t => hγ.2 t (mem_univ t)⟩
  exact eq_of_heq (eqRec_heq_iff.mpr hpair.2)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_IntrinsicExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold

namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M]

variable [CompactSpace M]

noncomputable def geodesic (p : TangentBundle (model n) M) : ℝ → M :=
  Classical.choose (completeGeodesic_exists p.1 p.2)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_GeodesicFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

noncomputable def geodesicFlow (t : ℝ) (p : TangentBundle (model n) M) : TangentBundle (model n) M :=
  curveState (E := Model n) (geodesic p) t

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_FanCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def geodesicFan (P : ℝ → TangentBundle (model n) M) (z : ℝ × ℝ) : TangentBundle (model n) M :=
   geodesicFlow z.1 (P z.2)

 def fanCoordinates (x : M) (P : ℝ → TangentBundle (model n) M) (z : ℝ × ℝ) : Model n × Model n :=
   stateChart x (geodesicFan P z)

 def fanDomain (x : M) (P : ℝ → TangentBundle (model n) M) : Set (ℝ × ℝ) :=
   (geodesicFan P) ⁻¹' (stateChart x).source

 def fanMomentum (P : ℝ → TangentBundle (model n) M) (t : ℝ) : ℝ :=
   inner ℝ (geodesicFlow t (P 0)).2
     (mfderiv 𝓘(ℝ, ℝ) (model n) (fun s => geodesic (P s) t) 0 (1 : ℝ))

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_ChartGlobalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def chartKinetic (x : M) (q : Model n × Model n) : ℝ := metric x q.1 q.2 q.2 / 2

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_ShortFlowCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def flowCoordinates (x : M) (t : ℝ) (q : Model n × Model n) : Model n × Model n :=
   stateChart x (geodesicFlow t ((stateChart x).symm q))

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Geodesics_ShortChartAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def ShortChartAction (x : M) (t : ℝ) (q : Model n × Model n) : Prop :=
   q ∈ (stateChart x).target ∧
   geodesicFlow t ((stateChart x).symm q) ∈ (stateChart x).source ∧
   ContDiffAt ℝ ∞ (chartCost x) (q.1,(flowCoordinates x t q).1) ∧
   ∀ w : Model n × Model n,
     fderiv ℝ (chartCost x) (q.1,(flowCoordinates x t q).1) w = t *
       (metric x (flowCoordinates x t q).1 (flowCoordinates x t q).2 w.2 - metric x q.1 q.2 w.1)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Coordinates_PairExpCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def pairExpCoordinates (x y : M) (q : Model n × Model n) : Model n × Model n :=
  (q.1,(stateChart y (geodesicFlow 1 ((stateChart x).symm q))).1)

 def pairExpDomain (x y : M) : Set (Model n × Model n) :=
  {q | q ∈ (stateChart x).target ∧ geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source}

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BranchAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def branchAction (x : M) (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (q : Model n × Model n) : ℝ := chartKinetic x (e.symm q)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_ActionHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def actionHessian (x : M) (v : TangentSpace (model n) x) :
    LinearMap.BilinForm ℝ (TangentSpace (model n) x) :=
  (actionForm (metric x) (initialCost x (exp x v)) (chartAt (Model n) x x)
    (tangentChartLinear x v)).compl₁₂ (tangentChartLinear x).toLinearMap (tangentChartLinear x).toLinearMap

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def crossFlowCoordinates (x y : M) (t : ℝ) (q : Model n × Model n) : Model n × Model n :=
    stateChart y (geodesicFlow t ((stateChart x).symm q))

 def generatingAction (x y : M) (ε : ℝ) (Q : (Model n × Model n) × Model n) : ℝ :=
    (1-ε)*chartKinetic x Q.1 + ε⁻¹ * chartCost y ((crossFlowCoordinates x y (1-ε) Q.1).1,Q.2)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_BranchHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def branchHessianDiag (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (v ξ : TangentSpace (model n) x) : ℝ :=
    fderiv ℝ (fderiv ℝ (branchAction x e)) (chartAt (Model n) x x,chartAt (Model n) y (exp x v))
      (tangentChartLinear x ξ,0) (tangentChartLinear x ξ,0) +
    lowerChristoffel (fderiv ℝ (metric x) (chartAt (Model n) x x))
      (tangentChartLinear x ξ) (tangentChartLinear x ξ) (tangentChartLinear x v)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_ActionBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 structure ActionBranch (x y : M) where
  coord : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n)
  map_eq : (coord : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y
  domain : coord.source ⊆ pairExpDomain (n := n) x y
  smooth : ContDiffOn ℝ ∞ coord.symm coord.target

 namespace ActionBranch
 variable {x y : M}

 def value (B : ActionBranch (n := n) x y) : Model n × Model n → ℝ := branchAction x B.coord

 end ActionBranch
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def GeneratingChartAction (x y : M) (ε : ℝ) (q : Model n × Model n) : Prop :=
    q ∈ (stateChart x).target ∧
    geodesicFlow (1-ε) ((stateChart x).symm q) ∈ (stateChart y).source ∧
    geodesicFlow 1 ((stateChart x).symm q) ∈ (stateChart y).source ∧
    ShortChartAction y ε (crossFlowCoordinates x y (1-ε) q)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end

section
-- module Solutions.OAIQW_WeakMTW.Variations_GeneratingHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry DiscreteVariational
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def generatingHessian (x y : M) (ε : ℝ) (q : Model n × Model n) :
    ((Model n × Model n) × Model n) →L[ℝ] ((Model n × Model n) × Model n) →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ (generatingAction x y ε)) (q,(crossFlowCoordinates x y 1 q).1)

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
end


