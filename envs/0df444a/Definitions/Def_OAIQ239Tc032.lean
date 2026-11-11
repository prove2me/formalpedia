-- Prove2me | Definitions.Def_OAIQ239Tc032
-- name    : OAIQ239Tc032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:01:51.279231+00:00
-- url     : https://prove2.me/theorems/897c0bb2-03b7-4baa-bcdf-453a04581cf9
-- title:
--   Definitions bundle OAIQ239Tc032 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 3 definitions and 13 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothingCover`, `OAI.TamingCompatibility.GeometricHilbert.localHodgeSmoothing`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_HeatFlow_HodgeResolventDifferential`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/HeatFlow/HodgeResolventDifferential.lean), [`TamingCompatibility_Hodge_HodgeGraphSmoothing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGraphSmoothing.lean), [`TamingCompatibility_Hodge_HodgeLocalEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeLocalEvaluation.lean), [`TamingCompatibility_Hodge_HodgePairAllTests`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgePairAllTests.lean), [`TamingCompatibility_Hodge_HodgeRawRegular`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeRawRegular.lean), [`TamingCompatibility_Hodge_HodgeScaleH3`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScaleH3.lean), [`TamingCompatibility_Hodge_HodgeScaleSmoothing`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeScaleSmoothing.lean), [`TamingCompatibility_Hodge_HodgeSmoothCommutator`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothCommutator.lean), [`TamingCompatibility_Hodge_HodgeSmoothLimit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothLimit.lean), [`TamingCompatibility_Hodge_HodgeSmoothingCover`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothingCover.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundles `OAIQ239Tc029`, `OAIQ239Tc030` and `OAIQ239Tc035` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ239Tc033`; the statements `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto`, `OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily_anti_cross_tendsto` and `OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_angularNear_point`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_positive_cross_lower`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_mass_lower`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_angular_moment`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.subprob_anti_cross_tendsto` and `OAI.TamingCompatibility.GeometricHilbert.hodge_lift_local_estimate`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc029
import Definitions.Def_OAIQ239Tc030
import Definitions.Def_OAIQ239Tc035

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRawRegular
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeRegularization_raw_H5 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∀ f : L2 A J α hs ht true, MemSobolevLoc V 5
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeRegularizedGraph A J α hs ht r hr f)) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hWgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hU hUD hτ q hqU r hr
  obtain ⟨V,hV,hqV,hVW,hVgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hW (hWU.trans hUD) (fun z hz => hτ z (hWU hz)) q hqW r hr
  refine ⟨τ,V,hV,hqV,hVW.trans (hWU.trans hUD),fun z hz => hτ z (hWU (hVW hz)),?_⟩
  intro f
  let u₁ := hodgeWeakSolution A J α hs ht r hr f
  let u₂ := hodgeWeakSolution A J α hs ht r hr (hodgeInclusion A J α hs ht u₁)
  have h₁ : MemSobolevLoc U (1:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u₁) :=
    memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u₁) U
  have h₂ : MemSobolevLoc W (3:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u₂) := by
    simpa only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num] using hWgain 1 u₁ (by simpa only [Nat.cast_one] using h₁)
  have h₃ := hVgain 3 u₂ (by simpa only [Nat.cast_ofNat] using h₂)
  have he₁ : hodgeInclusion A J α hs ht u₁ = hodgeResolvent A J α hs ht r f := by
    exact congrArg (fun L => L f) (hodgeResolvent_eq A J α hs ht r hr).symm
  have he₂ : hodgeInclusion A J α hs ht u₂ =
      hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f) := by
    change hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr _) = _
    rw [← ContinuousLinearMap.comp_apply,← hodgeResolvent_eq A J α hs ht r hr,he₁]
  rw [he₂] at h₃
  change MemSobolevLoc V 5 (hodgeRawDistribution A J α hs ht D hD p τ
    (hodgeWeakSolution A J α hs ht r hr (hodgeResolvent A J α hs ht r (hodgeResolvent A J α hs ht r f))))
  simpa only [Nat.cast_ofNat,show (3:ℝ)+2=5 by norm_num] using h₃
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeLocalEvaluation
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma exists_localHodgeSmoothing (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0)
    (r : ℝ) (hr : 0 < r) : Nonempty (LocalHodgeSmoothing A J α hs ht D hD p q r hr) := by
  obtain ⟨τ,V,hV,hqV,hVD,hτ,hreg⟩ := hodgeRegularization_raw_H5 A J α hs ht D hD p q hq hwq r hr
  obtain ⟨φ,hφ,hφV,U,hU,hqU,hUV,hφone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.ofRealCLM) φ
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχV : tsupport (χ : Space → ℂ) ⊆ V := hχs.trans hφV
  let L := hodgeLocalizedRegularization A J α hs ht D hD p τ χ r hr
  have hL : ∀ f, MemSobolev 5 2 (L f) := fun f => hreg f χ hχc hχV
  exact ⟨{
    reciprocal := τ
    cutoff := χ
    neighborhood := U
    neighborhood_open := hU
    center_mem := hqU
    neighborhood_subset := hUV.trans hVD
    reciprocal_eq := fun z hz => hτ z (hUV hz)
    cutoff_eq := fun z hz => by simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hφone z hz,Complex.ofReal_one]
    lift := realSobolevLift 5 L hL
    lift_spec := realSobolevLift_spec 5 L hL }⟩

def localHodgeSmoothing (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0)
    (r : ℝ) (hr : 0 < r) : LocalHodgeSmoothing A J α hs ht D hD p q r hr :=
  Classical.choice (exists_localHodgeSmoothing A J α hs ht D hD p q hq hwq r hr)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothingCover
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma exists_hodgeSmoothingPatch (r : ℝ) (hr : 0 < r) (x : X) :
    ∃ P : HodgeSmoothingPatch A J α hs ht D hD r hr, x ∈ P.source := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  let L := localHodgeSmoothing A J α hs ht D hD p (extChartAt Model p.val x) hxp hw r hr
  exact ⟨⟨p,extChartAt Model p.val x,L⟩,hxs,L.center_mem⟩

lemma hodgeSmoothingCover_nonempty (r : ℝ) (hr : 0 < r) :
    Nonempty (HodgeSmoothingCover A J α hs ht D hD r hr) := by
  classical
  choose P hP using exists_hodgeSmoothingPatch A J α hs ht D hD r hr
  obtain ⟨s,hcover⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (P x).source)
    (fun x => (P x).source_open) (fun x _ => mem_iUnion_of_mem x (hP x))
  have hc : (univ : Set X) ⊆ ⋃ i : s, (P i.val).source := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion_of_mem ⟨i,hi⟩ hxi
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun i : s => (P i.val).source) (fun i => (P i.val).source_open) hc
  exact ⟨⟨s,fun i => P i.val,ρ,hρ⟩⟩

def hodgeSmoothingCover (r : ℝ) (hr : 0 < r) : HodgeSmoothingCover A J α hs ht D hD r hr :=
  Classical.choice (hodgeSmoothingCover_nonempty A J α hs ht D hD r hr)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventDifferential
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.HodgeNormalSymbol.symbolMap_apply _root_.OAI.TamingCompatibility.HodgeStarGeometry.starMap_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set HilbertSobolev ComplexMatrix TemperedDistribution
open scoped Manifold ContDiff SchwartzMap BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraphResolvent_all_orders (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ (f : PreL2 A J α hs ht true) (n : ℕ),
        MemSobolevLoc V n (hodgeRawDistribution A J α hs ht D hD p τ
          ((hodgeGraphResolvent A J α hs ht r hr ^ j) (hodgeSmooth A J α hs ht f))) := by
  induction j with
  | zero =>
    refine ⟨U,hU,hq,Subset.rfl,fun f n => ?_⟩
    simp only [pow_zero,one_apply_eq_self]
    rw [hodgeRawDistribution_smooth]
    exact schwartz_memSobolevLoc _ n U
  | succ j ih =>
    obtain ⟨V,hV,hqV,hVU,hall⟩ := ih
    obtain ⟨W,hW,hqW,hWV,hgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
      hV (hVU.trans hUD) (fun z hz => hτ z (hVU hz)) q hqV r hr
    refine ⟨W,hW,hqW,hWV.trans hVU,fun f n => ?_⟩
    rw [pow_succ',mul_apply_eq_comp]
    exact (hgain n _ (hall f n)).mono (by simp)

lemma hodgeGraphResolvent_local_smooth (p : A.centers) (τ : 𝓢(Space,ℝ))
    {U : Set Space} (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (q : Space) (hq : q ∈ U) (r : ℝ) (hr : 0 < r) (j : ℕ)
    (f : PreL2 A J α hs ht true) :
    ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧ ∃ g : Space →ᵇ C 6,
      ContDiff ℝ ∞ (g : Space → C 6) ∧ ∀ χ : 𝓢(Space,ℂ),
        HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ V →
        smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
          ((hodgeGraphResolvent A J α hs ht r hr ^ j) (hodgeSmooth A J α hs ht f))) =
          smulLeftCLM (C 6) χ (EuclideanSobolev.boundedDistribution g) := by
  obtain ⟨W,hW,hqW,hWU,hall⟩ :=
    hodgeGraphResolvent_all_orders A J α hs ht D hD p τ hU hUD hτ q hq r hr j
  obtain ⟨V,hV,hqV,hVW,g,hg,he⟩ := exists_local_smooth_representative hW hqW (hall f)
  exact ⟨V,hV,hqV,hVW.trans hWU,g,hg,he⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGraphSmoothing
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraphResolvent_raw_H5 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∀ u : hodgeEnergy A J α hs ht, MemSobolevLoc V 5
        (hodgeRawDistribution A J α hs ht D hD p τ
          ((hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2) u)) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hWgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hU hUD hτ q hqU 1 zero_lt_one
  obtain ⟨V,hV,hqV,hVW,hVgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hW (hWU.trans hUD) (fun z hz => hτ z (hWU hz)) q hqW 1 zero_lt_one
  refine ⟨τ,V,hV,hqV,hVW.trans (hWU.trans hUD),fun z hz => hτ z (hWU (hVW hz)),?_⟩
  intro u
  have h₁ : MemSobolevLoc U (1:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u) :=
    memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u) U
  have h₂ : MemSobolevLoc W (3:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)) := by
    simpa only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num,hodgeGraphResolvent,ContinuousLinearMap.comp_apply] using hWgain 1 u (by simpa only [Nat.cast_one] using h₁)
  have h₃ := hVgain 3 (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)
    (by simpa only [Nat.cast_ofNat] using h₂)
  change MemSobolevLoc V 5 (hodgeRawDistribution A J α hs ht D hD p τ
    (hodgeGraphResolvent A J α hs ht 1 zero_lt_one (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)))
  simpa only [Nat.cast_ofNat,show (3:ℝ)+2=5 by norm_num,hodgeGraphResolvent,ContinuousLinearMap.comp_apply] using h₃

lemma exists_hodgeGraphResolvent_lift (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ L : hodgeEnergy A J α hs ht →L[ℝ] H Space (C 6) 5,
        ∀ u, toDistribution Space (C 6) 5 (L u) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            ((hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2) u)) := by
  obtain ⟨τ,V,hV,hqV,hVD,hτ,hreg⟩ := hodgeGraphResolvent_raw_H5 A J α hs ht D hD p q hq hwq
  obtain ⟨φ,hφ,hφV,U,hU,hqU,hUV,hφone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.ofRealCLM) φ
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχV : tsupport (χ : Space → ℂ) ⊆ V := hχs.trans hφV
  let F : hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,C 6) :=
    ((smulLeftCLM (C 6) χ).restrictScalars ℝ).comp
      ((hodgeRawDistribution A J α hs ht D hD p τ).comp (hodgeGraphResolvent A J α hs ht 1 zero_lt_one ^ 2))
  have hF : ∀ u, MemSobolev 5 2 (F u) := fun u => hreg u χ hχc hχV
  refine ⟨τ,χ,U,hU,hqU,hUV.trans hVD,fun z hz => hτ z (hUV hz),?_,
    realSobolevLift 5 F hF,realSobolevLift_spec 5 F hF⟩
  intro z hz
  simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hφone z hz,Complex.ofReal_one]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairAllTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert

section LocalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set ComplexMatrix
open scoped Manifold ContDiff SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open HilbertSobolev
variable (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodge_exists_weak_patch (r : ℝ) (hr : 0 < r) (j : ℕ)
    (f : PreL2 A J α hs ht true) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ w : PreL2 A J α hs ht true,
      ∀ (ρ : X → ℝ) (hρ : ContMDiff Model 𝓘(ℝ,ℝ) ∞ ρ), tsupport ρ ⊆ V →
        ∀ a : PreL2 A J α hs ht true,
          ⟪hodgeInclusion A J α hs ht ((hodgeGraphResolvent A J α hs ht r hr ^ j)
            (hodgeSmooth A J α hs ht f)),smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ =
          ⟪smoothL2 A J α hs ht true w,smoothL2 A J α hs ht true (hodgeMultiply A J α hs ht ρ hρ a)⟫ := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,-,-,U,hU,hxU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hxp hw
  obtain ⟨V,hV,hxV,hVU,g,hgs,hgd⟩ := hodgeGraphResolvent_local_smooth A J α hs ht D hD p τ
    hU hUD hτ (extChartAt Model p.val x) hxU r hr j f
  obtain ⟨W,hW,hxW,hWV,w,hw⟩ := hodge_exists_patch A J α hs ht D p hV (hVU.trans hUD) hxV g hgs
  let Z := (extChartAt Model p.val).source ∩ (extChartAt Model p.val) ⁻¹' W
  have hZ : IsOpen Z := (continuousOn_extChartAt p.val).isOpen_inter_preimage (isOpen_extChartAt_source p.val) hW
  refine ⟨Z,hZ,⟨hxs,hxW⟩,w,fun ρ hρ hρZ a => ?_⟩
  obtain ⟨q,hqc,hqW,hq⟩ := hodge_supported_test A J α hs ht D p hW
    (hWV.trans (hVU.trans hUD)) ρ hρ hρZ a
  rw [← hq]
  refine hodge_pair_all_tests_eq A J α hs ht D p (hWV.trans (hVU.trans hUD)) _ _ ?_ q hqc hqW
  intro φ hc hφW k
  exact hodge_local_pairing_eq A J α hs ht D hD p τ hW (hWV.trans (hVU.trans hUD))
    (fun z hz => hτ z (hVU (hWV hz))) _ g
    (fun χ hc hχ => tests_eq_of_localize hV hgd χ hc (hχ.trans hWV)) w hw φ hc hφW k
end LocalCharts

open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutator
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeGraphResolvent_raw_H3 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ V : Set Space, IsOpen V ∧ q ∈ V ∧ V ⊆ (D p).domain ∧
      (∀ z ∈ V, τ z * coordinateWeight A p z = 1) ∧
      ∀ u : hodgeEnergy A J α hs ht, MemSobolevLoc V 3
        (hodgeRawDistribution A J α hs ht D hD p τ
          (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)) := by
  obtain ⟨τ,-,-,U,hU,hqU,hUD,hτ⟩ := SchwartzCutoff.exists_reciprocal
    (D p).domain_open ((coordinateWeight_smooth A p).mono (D p).domain_subset) hq hwq
  obtain ⟨W,hW,hqW,hWU,hWgain⟩ := hodge_resolvent_raw_gain A J α hs ht D hD p τ
    hU hUD hτ q hqU 1 zero_lt_one
  refine ⟨τ,W,hW,hqW,hWU.trans hUD,fun z hz => hτ z (hWU hz),?_⟩
  intro u
  have h₁ : MemSobolevLoc U (1:ℝ) (hodgeRawDistribution A J α hs ht D hD p τ u) :=
    memSobolevLoc_one_of_global (hodgeRawDistribution_H1 A J α hs ht D hD p τ u) U
  simpa only [Nat.cast_one,show (1:ℝ)+2=3 by norm_num,hodgeGraphResolvent,ContinuousLinearMap.comp_apply]
    using hWgain 1 u (by simpa only [Nat.cast_one] using h₁)

lemma exists_hodgeGraphResolvent_H3_lift (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ L : hodgeEnergy A J α hs ht →L[ℝ] H Space (C 6) 3,
        ∀ u, toDistribution Space (C 6) 3 (L u) =
          smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
            (hodgeGraphResolvent A J α hs ht 1 zero_lt_one u)) := by
  obtain ⟨τ,V,hV,hqV,hVD,hτ,hreg⟩ := hodgeGraphResolvent_raw_H3 A J α hs ht D hD p q hq hwq
  obtain ⟨φ,hφ,hφV,U,hU,hqU,hUV,hφone⟩ := SchwartzCutoff.exists_one_near hV hqV
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
  have hχs : tsupport (χ : Space → ℂ) ⊆ tsupport φ :=
    tsupport_comp_subset (map_zero Complex.ofRealCLM) φ
  have hχc : HasCompactSupport (χ : Space → ℂ) :=
    hφ.of_isClosed_subset (isClosed_tsupport χ) hχs
  have hχV : tsupport (χ : Space → ℂ) ⊆ V := hχs.trans hφV
  let F : hodgeEnergy A J α hs ht →L[ℝ] 𝓢'(Space,C 6) :=
    ((smulLeftCLM (C 6) χ).restrictScalars ℝ).comp
      ((hodgeRawDistribution A J α hs ht D hD p τ).comp (hodgeGraphResolvent A J α hs ht 1 zero_lt_one))
  have hF : ∀ u, MemSobolev 3 2 (F u) := fun u => hreg u χ hχc hχV
  refine ⟨τ,χ,U,hU,hqU,hUV.trans hVD,fun z hz => hτ z (hUV hz),?_,
    realSobolevLift 3 F hF,realSobolevLift_spec 3 F hF⟩
  intro z hz
  simp only [χ,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply,hφone z hz,Complex.ofReal_one]
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleH3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeRegularization_uniform_local_H3 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 3,
          (∀ f, toDistribution Space (C 6) 3 (L f) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
          ∀ f, ‖L f‖ ≤ B*(r⁻¹)^3*‖f‖ := by
  obtain ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,L,hL⟩ := exists_hodgeGraphResolvent_H3_lift A J α hs ht D hD p q hq hwq
  refine ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,4*‖L‖,by positivity,fun r hr hr1 => ?_⟩
  refine ⟨L.comp (hodgeScaleH3Input A J α hs ht r hr),?_,?_⟩
  · intro f
    rw [ContinuousLinearMap.comp_apply,hL,hodgeScaleH3Input_spec]
  · intro f
    calc
      _ ≤ ‖L‖*‖hodgeScaleH3Input A J α hs ht r hr f‖ := L.le_opNorm _
      _ ≤ ‖L‖*(4*(r⁻¹)^3*‖f‖) := mul_le_mul_of_nonneg_left
        (hodgeScaleH3Input_bound A J α hs ht r hr hr1 f) (norm_nonneg L)
      _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScaleSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight coordinateWeight_smooth)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma hodgeRegularization_uniform_local_H5 (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) 5,
          (∀ f, toDistribution Space (C 6) 5 (L f) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
          ∀ f, ‖L f‖ ≤ B*(r⁻¹)^5*‖f‖ := by
  obtain ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,L,hL⟩ := exists_hodgeGraphResolvent_lift A J α hs ht D hD p q hq hwq
  refine ⟨τ,χ,U,hU,hqU,hUD,hτ,hχ,8*‖L‖,by positivity,fun r hr hr1 => ?_⟩
  refine ⟨L.comp (hodgeScaleInput A J α hs ht r hr),?_,?_⟩
  · intro f
    rw [ContinuousLinearMap.comp_apply,hL,hodgeScaleInput_spec]
  · intro f
    calc
      _ ≤ ‖L‖*‖hodgeScaleInput A J α hs ht r hr f‖ := L.le_opNorm _
      _ ≤ ‖L‖*(8*(r⁻¹)^5*‖f‖) := mul_le_mul_of_nonneg_left
        (hodgeScaleInput_bound A J α hs ht r hr hr1 f) (norm_nonneg L)
      _ = _ := by ring
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

def hodgePositiveCurrentFamily
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) (r : ℝ) : L2 A J α hs ht true :=
  if hr : 0 < r then (hodgeSmoothingCover A J α hs ht D hD r hr).regularize g μ else 0

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


