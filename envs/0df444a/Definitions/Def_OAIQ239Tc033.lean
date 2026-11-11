-- Prove2me | Definitions.Def_OAIQ239Tc033
-- name    : OAIQ239Tc033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T01:13:44.30805+00:00
-- url     : https://prove2.me/theorems/e5b9c327-2542-497a-81d3-f54bcd15e968
-- title:
--   Definitions bundle OAIQ239Tc033 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 6 definitions and 7 theorems. The definitions and types are `OAI.TamingCompatibility.GeometricHilbert.hodgeCommutatorCover`, `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrectionFamily`, `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrectionRegularize`, `OAI.TamingCompatibility.GeometricHilbert.hodgeDistributionInverse`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothFamily`, `OAI.TamingCompatibility.GeometricHilbert.hodgeSmoothInverse`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`TamingCompatibility_Hodge_HodgeCommutatorCover`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCommutatorCover.lean), [`TamingCompatibility_Hodge_HodgeCorrectionLimit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCorrectionLimit.lean), [`TamingCompatibility_Hodge_HodgeCorrectionRegularization`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeCorrectionRegularization.lean), [`TamingCompatibility_Hodge_HodgeGlobalSmooth`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeGlobalSmooth.lean), [`TamingCompatibility_Hodge_HodgeSmoothCommutation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothCommutation.lean), [`TamingCompatibility_Hodge_HodgeSmoothInverse`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeSmoothInverse.lean), [`TamingCompatibility_Hodge_HodgeUniformCommutator`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeUniformCommutator.lean), [`TamingCompatibility_Hodge_HodgeUniformOdd`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Hodge/HodgeUniformOdd.lean).
--
--   **Imports.** It imports the published bundle `Def_TamingCompatibility`; the bundle `OAIQ239Tc032` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrected_energy_identity`; the proofs of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_current_quantitative`, `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_wedge_kernel`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingGammaTail_integral`, `OAI.TamingCompatibility.GeometricHilbert.HodgeSmoothingCover.pairingHeatVector_star`, `OAI.TamingCompatibility.GeometricHilbert.hodgeCorrected_energy_identity`, `OAI.TamingCompatibility.GeometricHilbert.hodgePositiveCurrentFamily_anti_cross_tendsto`, `OAI.TamingCompatibility.GeometricHilbert.hodge_regularized_positive_current_cross`, `OAI.TamingCompatibility.GeometricHilbert.hodge_residual_energy_zero`, `OAI.TamingCompatibility.GeometricHilbert.separating_current_L2_correction` and `OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc032

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalSmooth
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J) (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in

theorem hodgeGraphResolvent_smooth (r : ℝ) (hr : 0 < r) (j : ℕ)
    (f : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true, hodgeSmooth A J α hs ht b =
      (hodgeGraphResolvent A J α hs ht r hr ^ j) (hodgeSmooth A J α hs ht f) := by
  classical
  choose V hV hxV w hw using hodge_exists_weak_patch A J α hs ht D hD r hr j f
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion_of_mem x (hxV x))
  have hc : (univ : Set X) ⊆ ⋃ p : s, V p.val := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => V p.val) (fun p => hV p.val) hc
  apply hodge_glue_weak_patches A J α hs ht (fun p : s => ρ p) (fun p => (ρ p).contMDiff)
    (fun x => ?_) _ (fun p : s => w p.val) (fun p => hw p.val (ρ p) (ρ p).contMDiff (hρ p))
  simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodgeRegularization_smooth (r : ℝ) (hr : 0 < r) (f : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true, smoothL2 A J α hs ht true b =
      hodgeRegularization A J α hs ht r (smoothL2 A J α hs ht true f) := by
  obtain ⟨b,hb⟩ := hodgeGraphResolvent_smooth A J α hs ht D hD r hr 3 f
  refine ⟨b,?_⟩
  have h := congrArg (hodgeInclusion A J α hs ht) hb
  simpa only [hodgeInclusion_smooth,hodgeGraphResolvent_inclusion_power,hodgeRegularization] using h
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUniformOdd
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

lemma hodgeRegularization_uniform_local_odd (k : ℕ) (hk : k ≤ 2) (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ χ : 𝓢(Space,ℂ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      (∀ z ∈ U, χ z = 1) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        ∃ L : L2 A J α hs ht true →L[ℝ] H Space (C 6) (2*k+1:ℕ),
          (∀ f, toDistribution Space (C 6) (2*k+1:ℕ) (L f) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
              (hodgeRegularizedGraph A J α hs ht r hr f))) ∧
          ∀ f, ‖L f‖ ≤ B*(r⁻¹)^(2*k+1)*‖f‖ := by
  interval_cases k
  · simp only [mul_zero,zero_add,pow_one]
    obtain ⟨τ,U,hU,hqU,hUD,hτ,B,hB,hreg⟩ :=
      hodgeRegularization_uniform_local_H1 A J α hs ht D hD p q hq hwq
    obtain ⟨φ,-,-,W,hW,hqW,hWU,hφone⟩ := SchwartzCutoff.exists_one_near hU hqU
    let χ := SchwartzMap.postcompCLM Complex.ofRealCLM φ
    let P := (HilbertSobolev.product (F := C 6) 1 χ).restrictScalars ℝ
    refine ⟨τ,χ,W,hW,hqW,hWU.trans hUD,fun z hz => hτ z (hWU hz),?_,
      ‖P‖*B,mul_nonneg (norm_nonneg _) hB,fun r hr hr1 => ?_⟩
    · intro z hz
      change (φ z : ℂ) = 1
      rw [hφone z hz,Complex.ofReal_one]
    · obtain ⟨L,hL,hb⟩ := hreg r hr hr1
      refine ⟨P.comp L,?_,?_⟩
      · intro f
        have hh : toDistribution Space (C 6) 1 (product 1 χ (L f)) =
            smulLeftCLM (C 6) χ (toDistribution Space (C 6) 1 (L f)) := by
          simpa only [toDistribution, Nat.cast_one] using
            toDistribution_product (F := C 6) 1 χ (L f)
        rw [hL f] at hh
        simpa [P,toDistribution] using hh
      · intro f
        calc
          _ ≤ ‖P‖*‖L f‖ := P.le_opNorm _
          _ ≤ ‖P‖*(B*r⁻¹*‖f‖) := mul_le_mul_of_nonneg_left (hb f) (norm_nonneg P)
          _ = _ := by ring
  · simpa using hodgeRegularization_uniform_local_H3 A J α hs ht D hD p q hq hwq
  · simpa using hodgeRegularization_uniform_local_H5 A J α hs ht D hD p q hq hwq
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUniformCommutator
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

lemma hodge_commutator_uniform_local_bound (k : ℕ) (hk : k ≤ 2) (p : A.centers) (q : Space)
    (hq : q ∈ (D p).domain) (hwq : coordinateWeight A p q ≠ 0) :
    ∃ τ : 𝓢(Space,ℝ), ∃ U : Set Space,
      IsOpen U ∧ q ∈ U ∧ U ⊆ (D p).domain ∧
      (∀ z ∈ U, τ z * coordinateWeight A p z = 1) ∧
      ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ U →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
          ∃ T : L2 A J α hs ht true →L[ℝ] H Space (C 6) 0,
            (∀ f : PreL2 A J α hs ht true,
              toDistribution Space (C 6) 0
                (T (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f))) =
                smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD p τ
                  (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht (k+1) f)))) ∧
            ∀ v, ‖T v‖ ≤ B * (r⁻¹)^(2*k+1) * ‖v‖ := by
  obtain ⟨τ,ψ,V,hV,hqV,hVD,hτ,hψ,B,hB,hreg⟩ :=
    hodgeRegularization_uniform_local_odd A J α hs ht D hD k hk p q hq hwq
  obtain ⟨U,hU,hqU,hUV,a,b,ρ,θ,G,ha,hb,hρ,hθ,hG⟩ :=
    exists_hodge_local_coefficients A J α hs ht D p hV hVD q hqV
  refine ⟨τ,U,hU,hqU,hUV.trans hVD,fun z hz => hτ z (hUV hz),?_⟩
  intro χ hc hχ
  let N : H Space (C 6) (2*k+1:ℕ) →L[ℝ] H Space (C 6) 0 :=
    normalizedFullSquare_power_commutator_lift k 0 a b ρ θ G hG antiMatrix
  let P : H Space (C 6) 0 →L[ℝ] H Space (C 6) 0 :=
    (HilbertSobolev.product (F := C 6) 0 χ).restrictScalars ℝ
  refine ⟨‖P‖*‖N‖*B,mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB,?_⟩
  intro r hr hr1
  obtain ⟨L,hL,hLb⟩ := hreg r hr hr1
  refine ⟨P.comp (N.comp L),?_,?_⟩
  · intro f
    generalize hv0 : smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f) = v
    have hv : hodgeRegularizedGraph A J α hs ht r hr v = hodgeSmooth A J α hs ht f := by
      rw [← hv0]
      exact hodgeRegularizedGraph_smoothShift_cube A J α hs ht r hr f
    have hLv := hL v
    rw [hv] at hLv
    have hcut := LocallyEqual.cutoff_self ψ (fun z hz => hψ z (hUV hz))
      (hodgeRawDistribution A J α hs ht D hD p τ (hodgeSmooth A J α hs ht f))
    have h1 := normalizedFullSquare_power_local_congr a b ρ θ G hG hU (k+1)
      (hcut.fiberMap antiMatrix)
    have h2 := (normalizedFullSquare_power_local_congr a b ρ θ G hG hU (k+1) hcut).fiberMap antiMatrix
    have he := (h1.sub h2).trans
      (hodge_commutator_local_distribution A J α hs ht D hD p τ hU (hUV.trans hVD)
        (fun z hz => hτ z (hUV hz)) a b ρ ha hb hρ θ hθ G hG (k+1) f)
    dsimp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',P,N]
    clear_value P N
    generalize hu0 : hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht f) = u at he hLv
    generalize hw0 : hodgeRawDistribution A J α hs ht D hD p τ
      (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht (k+1) f)) = w at he ⊢
    have heχ := he χ hc hχ
    have hs' := normalized_commutator_localized_spec (m := 8) k a b ρ θ G hG antiMatrix χ (L v)
      (smulLeftCLM (C 6) ψ u) _ hLv rfl
    generalize hE : normalizedFullSquare a b ρ θ = E at hs' heχ
    generalize hM : fiberMap (E := Space) antiMatrix = M at hs' heχ
    generalize hz : normalizedFullSquare_power_commutator_lift k 0 a b ρ θ G hG antiMatrix (L v) = z at hs' ⊢
    have hfinal := hs'.trans heχ
    exact hfinal
  · clear_value P N
    exact bounded_triple_composition P N L B ((r⁻¹)^(2*k+1)) hLb
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCommutatorCover
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter _root_.MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

lemma exists_hodgeCommutatorPatch (k : ℕ) (hk : k ≤ 2) (x : X) :
    ∃ P : HodgeCommutatorPatch A J α hs ht D hD k, x ∈ P.source := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,U,hU,hqU,hUD,hτ,hbound⟩ :=
    hodge_commutator_uniform_local_bound A J α hs ht D hD k hk p _ hxp hw
  exact ⟨⟨p,τ,U,hU,hUD,hτ,hbound⟩,hxs,hqU⟩

lemma hodgeCommutatorCover_nonempty (k : ℕ) (hk : k ≤ 2) :
    Nonempty (HodgeCommutatorCover A J α hs ht D hD k) := by
  classical
  choose P hP using exists_hodgeCommutatorPatch A J α hs ht D hD k hk
  obtain ⟨s,hcover⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (P x).source)
    (fun x => (P x).source_open) (fun x _ => mem_iUnion_of_mem x (hP x))
  have hc : (univ : Set X) ⊆ ⋃ i : s, (P i.val).source := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion_of_mem ⟨i,hi⟩ hxi
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun i : s => (P i.val).source) (fun i => (P i.val).source_open) hc
  exact ⟨⟨s,fun i => P i.val,ρ,hρ⟩⟩

def hodgeCommutatorCover (k : ℕ) (hk : k ≤ 2) : HodgeCommutatorCover A J α hs ht D hD k :=
  Classical.choice (hodgeCommutatorCover_nonempty A J α hs ht D hD k hk)
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothInverse
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
include D hD in
lemma hodgeSmoothShift_cube_bijective (r : ℝ) (hr : 0 < r) :
    Function.Bijective (fun a : PreL2 A J α hs ht true => (hodgeSmoothShift A J α hs ht r ^ 3) a) := by
  constructor
  · intro a b hab
    dsimp only at hab
    apply (smoothL2 A J α hs ht true).injective
    rw [← hodgeRegularization_smoothShift_cube A J α hs ht r hr a,
      ← hodgeRegularization_smoothShift_cube A J α hs ht r hr b,hab]
  · intro b
    obtain ⟨a,ha⟩ := hodgeRegularization_smooth A J α hs ht D hD r hr b
    exact ⟨a,hodgeRegularization_smooth_inverse A J α hs ht r hr b a ha⟩

def hodgeSmoothInverse (r : ℝ) (hr : 0 < r) :
    PreL2 A J α hs ht true ≃ₗ[ℝ] PreL2 A J α hs ht true :=
  (LinearEquiv.ofBijective (hodgeSmoothShift A J α hs ht r ^ 3)
    (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).symm

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeDistributionInverse (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) : L2 A J α hs ht true :=
  (InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm
    ((F.comp (hodgeSmoothInverse A J α hs ht D hD r hr).toLinearMap).extendOfNorm
      (smoothL2 A J α hs ht true).toLinearMap)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCorrectionRegularization
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

def hodgeCorrectionRegularize
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (r : ℝ) (hr : 0 < r) :
    L2 A J α hs ht true :=
  hodgeDistributionInverse A J α hs ht D hD r hr (hodgeCorrectionSource A J α hs ht B g μ)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCorrectionLimit
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Filter
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

def hodgeCorrectionFamily
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (r : ℝ) : L2 A J α hs ht true :=
  if hr : 0 < r then hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr else 0

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothCommutation
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
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

def hodgeSmoothFamily (r : ℝ) : PreL2 A J α hs ht true →ₗ[ℝ] PreL2 A J α hs ht true :=
  if hr : 0 < r then (hodgeSmoothInverse A J α hs ht D hD r hr).toLinearMap else LinearMap.id

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end


