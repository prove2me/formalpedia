-- Prove2me | Definitions.Def_OAIQ091C027
-- name    : OAIQ091C027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:26:27.435716+00:00
-- url     : https://prove2.me/theorems/0cbc0c00-8e60-4680-a114-6a66e8e597da
-- title:
--   Definitions bundle OAIQ091C027 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 5 definitions and 65 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneNormalizedResidual`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneNormalizedResidualZero`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneResidual`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.operatorColumn`, `OAI.PositiveEinsteinFour.Geometry.twoFormWeightedComponentL2`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory06.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C042` and `OAIQ091C024` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C044`, `OAIQ091C045`, `OAIQ091C047`, `OAIQ091C048`, `OAIQ091C049` and `OAIQ091C056`; the proofs of `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_norm` and `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_pairing`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C042
import Definitions.Def_OAIQ091C024

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual chart integral formulas for the L2 and covariant energy
pairings against a compactly supported orthonormal-frame test. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set Function
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGramTest_pairing (u : smoothTwoForms o)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormCovariantPairing o u.val (twoFormGramTest o c S a ha hK hKt has).val
      ((chartAt FourSpace c).symm z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        inner ℝ (twoFormLocalNabla (g := g) c S (twoFormChartValue o u.val c S hS) i z)
          (twoFormLocalNabla (g := g) c S a j z) := by
  by_cases hzU : z ∈ U
  · rw [u.property.covariantPairing_chart (twoFormGramTest o c S a ha hK hKt has).property
      c S hS U hU hUt hp z hzU]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [twoFormGramTest_nabla c S hS a ha hK hKt has z hz j]
  · have hzK : z ∉ K := fun h => hzU (hKU h)
    have hxK : (chartAt FourSpace c).symm z ∉ (chartAt FourSpace c).symm '' K := by
      rintro ⟨w, hw, he⟩
      have he' := congrArg (chartAt FourSpace c) he
      rw [(chartAt FourSpace c).right_inv (hKt hw), (chartAt FourSpace c).right_inv hz] at he'
      exact hzK (he' ▸ hw)
    have hleft : twoFormCovariantPairing o u.val (twoFormGramTest o c S a ha hK hKt has).val
        ((chartAt FourSpace c).symm z) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxK
        (twoFormGramTest_support c S a ha hK hKt has
          (twoFormCovariantPairing_tsupport_right _ _ h)))
    rw [hleft]
    have hn (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z
      (fun h => hzK (has h)) j
    simp only [hn, inner_zero_right, mul_zero, Finset.sum_const_zero]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormCovariantEnergy_gramTest (u : smoothTwoForms o)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (has : tsupport a ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive) :
    smoothTwoFormCovariantEnergy u (twoFormGramTest o c S a ha hK hKt has) =
      (normalizedChartFactor g).toReal * ∫ z in (chartAt FourSpace c).target,
        chartVolumeDensity g c z * (∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
          inner ℝ (twoFormLocalNabla (g := g) c S (twoFormChartValue o u.val c S hS) i z)
            (twoFormLocalNabla (g := g) c S a j z)) := by
  unfold smoothTwoFormCovariantEnergy
  rw [normalizedVolume_integral_chart g c _ (by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    obtain ⟨z, hz, rfl⟩ := twoFormGramTest_support c S a ha hK hKt has
      (twoFormCovariantPairing_tsupport_right _ _ h)
    exact hx ((chartAt FourSpace c).map_target (hKt hz)))]
  congr 1
  apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
  intro z hz
  exact congrArg (fun r : ℝ => chartVolumeDensity g c z * r)
    (twoFormGramTest_pairing u c S hS a ha hK hKt has U hU hUt hKU hp z hz)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The local six-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleOperator_transport_residual_at (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (t : ℝ) (ht : 0 < t)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x)
    (hB : ∀ k l, (∑ i : Fin 4, x i * B i k l) = 0) (k : Fin 6) :
    deriv (fun s => fourHeatGaussian s x * u x k) t +
      fourHeatBundleOperator a b B C (fun y l => fourHeatGaussian t y * u y l) x k =
    fourHeatGaussian t x *
      (fourHeatBundleOperator a b B C u x k +
        fourHeatRadialTransport a b (fun y => u y k) x / t +
        fourHeatEikonalDefect a x / t ^ 2 * u x k) := by
  unfold fourHeatBundleOperator
  rw [fourHeatBundleFirst_gaussian B t ht.ne' u x
      (fun l => (hu l).differentiableAt (by norm_num)) hB,
    fourHeatBundleZero_gaussian]
  have hs := fourHeatLocalOperator_transport_residual_at a b 0 t ht
    (fun y => u y k) x (hu k)
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every smooth two-form supported in one chart is exactly the compact
orthonormal-frame test constructed from its own coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem twoForm_supported_gramTest (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K Z : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hZK : Z ⊆ K) (w : smoothTwoForms o)
    (hs : tsupport w.val ⊆ (chartAt FourSpace c).symm '' Z) :
    ∃ (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
      (has : tsupport a ⊆ Z), twoFormGramTest o c S a ha hK hKt (has.trans hZK) = w := by
  let a := twoFormChartValue o w.val c S hS
  have ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target :=
    fun z hz => (w.property.chartValue_contDiffAt c S hS z hz).contDiffWithinAt
  have hsource : tsupport w.val ⊆ (chartAt FourSpace c).source := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := hs hx
    exact (chartAt FourSpace c).map_target (hKt (hZK hz))
  let L := (chartAt FourSpace c) '' tsupport w.val
  have hL : IsCompact L :=
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport w.val) (subset_univ _)).image_of_continuousOn
      ((chartAt FourSpace c).continuousOn.mono hsource)
  have hLZ : L ⊆ Z := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hs hx
    rw [← he, (chartAt FourSpace c).right_inv (hKt (hZK hy))]
    exact hy
  have hasL : tsupport a ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro z hz
    have hzt : z ∈ (chartAt FourSpace c).target := by
      by_contra hn
      apply hz
      exact dite_eq_right hn
    have hw : w.val ((chartAt FourSpace c).symm z) ≠ 0 := by
      intro hw
      have hn := twoFormChartValue_norm o w.val c S hS z hzt
      rw [hw, norm_zero] at hn
      exact hz (norm_eq_zero.mp hn)
    exact ⟨(chartAt FourSpace c).symm z, subset_tsupport w.val hw,
      (chartAt FourSpace c).right_inv hzt⟩
  let has := hasL.trans hLZ
  let v := twoFormGramTest o c S a ha hK hKt (has.trans hZK)
  refine ⟨a, ha, has, ?_⟩
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ (chartAt FourSpace c).source
  · let z := chartAt FourSpace c x
    have hz : z ∈ (chartAt FourSpace c).target := (chartAt FourSpace c).map_source hx
    have he := twoFormGramTest_value (o := o) c S hS a ha hK hKt (has.trans hZK) z hz
    change twoFormChartValue o v.val c S hS z = twoFormChartValue o w.val c S hS z at he
    let e := chartGramSection g c S hS ⟨z, hz⟩
    have hf : twoFormFrameValue o v.val e = twoFormFrameValue o w.val e := by
      simpa only [twoFormChartValue, dite_eq_left hz] using he
    have hi := (twoFormFrameIsometry ((o.frame e.base).changeMatrix e.frame)
      ((o.frame e.base).changeMatrix_orthogonal e.frame)).injective hf
    change v.val ((chartAt FourSpace c).symm z) = w.val ((chartAt FourSpace c).symm z) at hi
    simpa only [z, (chartAt FourSpace c).left_inv hx] using hi
  · have hw : w.val x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsource h))
    have hv : v.val x = 0 := twoFormChartTest_zero_off c _ _ _ hK hKt _ x (by
      rintro ⟨z, hz, rfl⟩
      exact hx ((chartAt FourSpace c).map_target (hKt hz)))
    exact hv.trans hw.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrary alternating tensor coordinates are fixed linear combinations
of the six actual two-form components, also after H1 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

include hS in
theorem twoFormGramValue_component_expansion (v : Fin 2 → Fin 4) (u : TwoFormH1 o) :
    twoFormGramValueL2 c S hK hKt χ hχ hc hs v u =
      ∑ r : Fin 6, twoFormTensor (EuclideanSpace.basisFun (Fin 6) ℝ r) v •
        twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u := by
  let C : Fin 6 → ℝ := fun r => twoFormTensor (EuclideanSpace.basisFun (Fin 6) ℝ r) v
  let L : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
    ∑ r : Fin 6, C r • twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r)
  change twoFormGramValueL2 c S hK hKt χ hχ hc hs v u = L u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (twoFormGramValueL2 c S hK hKt χ hχ hc hs v).continuous L.continuous) ?_
  intro w
  let F := fun r : Fin 6 => C r • twoFormGramValueL2 c S hK hKt χ hχ hc hs
    (twoFormComponentIndex r) (smoothTwoFormToH1 w)
  have he : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ r : Fin 6,
      F r z = C r * (χ z * twoFormChartValue o (w : smoothTwoForms o).val c S hS z r) := by
    apply Filter.eventually_all.mpr
    intro r
    filter_upwards [Lp.coeFn_smul (C r) (twoFormGramValueL2 c S hK hKt χ hχ hc hs
        (twoFormComponentIndex r) (smoothTwoFormToH1 w)),
      twoFormGramValue_tensor_coe c S hS hK hKt χ hχ hc hs (twoFormComponentIndex r) w]
      with z hmul hval
    change (C r • twoFormGramValueL2 c S hK hKt χ hχ hc hs
      (twoFormComponentIndex r) (smoothTwoFormToH1 w)) z = _
    rw [hmul]
    change C r * twoFormGramValueL2 c S hK hKt χ hχ hc hs
      (twoFormComponentIndex r) (smoothTwoFormToH1 w) z = _
    rw [hval, twoFormTensor_component]
  change twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w) = ∑ r : Fin 6, F r
  apply Lp.ext
  filter_upwards [twoFormGramValue_tensor_coe c S hS hK hKt χ hχ hc hs v w,
    Lp.coeFn_finsetSum Finset.univ F, he] with z hleft hright hall
  rw [hleft, hright]
  change χ z * twoFormTensor (twoFormChartValue o (w : smoothTwoForms o).val c S hS z) v =
    ∑ r : Fin 6, F r z
  rw [twoFormTensor_coordinate_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [hall r]
  dsimp only [C]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial gauge forces the connection and its diagonal derivatives
to vanish at the center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.twoForm_connection_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) : heatTwoFormConnection g c D.point i 0 = 0 := by
  apply heat_radial_connection_center
  · intro i k l
    exact (D.twoForm_connection_regular i k l).continuousAt
  · filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.twoForm_connection_radial x hx

theorem HeatNormalFrameData.twoForm_connection_diagonal_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) (k l : Fin 6) :
    partialDeriv (fun x => heatTwoFormConnection g c D.point i x k l) i 0 = 0 := by
  apply heat_radial_connection_diagonal
  · intro i k l
    exact (D.twoForm_connection_regular i k l).differentiableAt (by norm_num)
  · filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.twoForm_connection_radial x hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! At the center of the normal frame, the zeroth-order bundle coefficient
is precisely the intrinsic Weitzenböck potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.bundleFirst_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) : heatNormalBundleFirst D 0 i = 0 := by
  simp [heatNormalBundleFirst, fourHeatConnectionFirst, D.twoForm_connection_zero]

theorem HeatNormalFrameData.bundleZero_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e) :
    heatNormalBundleZero D 0 = heatNormalPotential g c D.point 0 := by
  ext k l
  simp [heatNormalBundleZero, fourHeatConnectionZero, heatNormalMetric_zero,
    D.twoForm_connection_zero, D.twoForm_connection_diagonal_zero, Matrix.one_apply]

theorem HeatNormalFrameData.bundleZero_intrinsic_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    heatNormalBundleZero D 0 = twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) := by
  rw [D.bundleZero_center, heatNormalPotential, D.curvature_center he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact cancellation of the first four matrix heat amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundlePolynomial_gaussian_residual (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6)
    (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (hu : ∀ i k, ContDiff ℝ 2 (fun y => u i y k))
    (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (hB : ∀ k l, (∑ i : Fin 4, x i * B i k l) = 0)
    (hE : fourHeatEikonalDefect a x = 0)
    (h0 : ∀ k, fourHeatRadialTransport a b (fun y => u 0 y k) x = 0)
    (h1 : ∀ k, fourHeatRadialTransport a b (fun y => u 1 y k) x + u 1 x k =
      -fourHeatBundleOperator a b B C (u 0) x k)
    (h2 : ∀ k, fourHeatRadialTransport a b (fun y => u 2 y k) x + 2 * u 2 x k =
      -fourHeatBundleOperator a b B C (u 1) x k)
    (h3 : ∀ k, fourHeatRadialTransport a b (fun y => u 3 y k) x + 3 * u 3 x k =
      -fourHeatBundleOperator a b B C (u 2) x k) (k : Fin 6) :
    deriv (fun s => fourHeatGaussian s x * fourHeatBundlePolynomial u s x k) t +
      fourHeatBundleOperator a b B C
        (fun y l => fourHeatGaussian t y * fourHeatBundlePolynomial u t y l) x k =
      fourHeatGaussian t x * t ^ 3 * fourHeatBundleOperator a b B C (u 3) x k := by
  have hP (l : Fin 6) : ContDiff ℝ 2 (fun y => fourHeatBundlePolynomial u t y l) :=
    fourHeatPolynomial_contDiff (fun m y => u m y l) (fun m => hu m l) t
  have hd := (fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt (fun m y => u m y k) t x)
  change HasDerivAt (fun s => fourHeatGaussian s x * fourHeatBundlePolynomial u s x k) _ t at hd
  have hr := fourHeatBundleOperator_transport_residual_at a b B C t ht
    (fourHeatBundlePolynomial u t) x (fun l => (hP l).contDiffAt) hB k
  rw [(fourHeatGaussian_amplitude_time t ht (fun y => fourHeatBundlePolynomial u t y k) x).deriv,
    hE, zero_div, zero_mul, add_zero] at hr
  rw [fourHeatBundlePolynomial_operator a b B C u hu t x k] at hr
  have hT := fourHeatPolynomial_transport a b (fun m y => u m y k) (fun m => hu m k) t x
  change fourHeatRadialTransport a b (fun y => fourHeatBundlePolynomial u t y k) x = _ at hT
  rw [hT, h0] at hr
  have h1' : fourHeatRadialTransport a b (fun y => u 1 y k) x =
      -fourHeatBundleOperator a b B C (u 0) x k - u 1 x k := by linarith only [h1 k]
  have h2' : fourHeatRadialTransport a b (fun y => u 2 y k) x =
      -fourHeatBundleOperator a b B C (u 1) x k - 2 * u 2 x k := by linarith only [h2 k]
  have h3' : fourHeatRadialTransport a b (fun y => u 3 y k) x =
      -fourHeatBundleOperator a b B C (u 2) x k - 3 * u 3 x k := by linarith only [h3 k]
  rw [h1', h2', h3'] at hr
  rw [hd.deriv]
  calc
    _ = fourHeatGaussian t x * (‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) *
          fourHeatBundlePolynomial u t x k +
        fourHeatBundleOperator a b B C
          (fun y l => fourHeatGaussian t y * fourHeatBundlePolynomial u t y l) x k +
        fourHeatGaussian t x * (u 1 x k + 2 * t * u 2 x k + 3 * t ^ 2 * u 3 x k) := by
          dsimp only [fourHeatBundlePolynomial]
          ring
    _ = _ := by rw [hr]; field_simp [ht.ne']; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first diagonal bundle amplitude is its scalar contribution minus
the actual Weitzenböck potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalBundleExtension.first_amplitude_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) :
    E.amplitude 1 0 =
      (-fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0) • (1 : HeatMat6) -
        heatNormalPotential g c D.point 0 := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hB : E.B 0 = fun _ => 0 := by
    funext i
    exact congrFun E.B_near.self_of_nhds i |>.trans (D.bundleFirst_zero i)
  have hC : E.C 0 = heatNormalPotential g c D.point 0 :=
    E.C_near.self_of_nhds.trans D.bundleZero_center
  ext k l
  have hrec := fourHeatBundleCoefficient_center 0 E.base.a E.base.b E.B E.C E.base.U
    (by rw [hU]; exact one_ne_zero) k l
  have hrec' : E.amplitude 1 0 k l =
    -fourHeatBundleOperator (E.base.a 0) (E.base.b 0) (E.B 0) (E.C 0)
      (fun y q => E.base.U y * (if q = l then 1 else 0)) 0 k := by
    simpa only [Nat.cast_zero, zero_add, one_mul] using! hrec
  rw [hB, hC, fourHeatBundleOperator_initial, hU] at hrec'
  change E.amplitude 1 0 k l =
    -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0 *
      (if k = l then 1 else 0) - heatNormalPotential g c D.point 0 k l
  linarith only [hrec']

theorem HeatNormalBundleExtension.first_amplitude_intrinsic_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    E.amplitude 1 0 =
      (-fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0) • (1 : HeatMat6) -
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) := by
  rw [E.first_amplitude_center, ← D.bundleZero_center, D.bundleZero_intrinsic_center he]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual second transport coefficient at the center, with its
quadratic Weitzenböck contribution to the signed trace isolated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.second_amplitude_center (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    (2 : ℝ) • E.amplitude 2 0 =
      -heatMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0 -
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) * E.amplitude 1 0 := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hB : E.B 0 = fun _ => 0 := by
    funext i
    exact congrFun E.B_near.self_of_nhds i |>.trans (D.bundleFirst_zero i)
  have hC : E.C 0 = twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) :=
    E.C_near.self_of_nhds.trans (D.bundleZero_intrinsic_center he)
  ext k l
  have hrec := fourHeatBundleCoefficient_center 1 E.base.a E.base.b E.B E.C E.base.U
    (by rw [hU]; exact one_ne_zero) k l
  have hrec' : (2 : ℝ) * E.amplitude 2 0 k l =
      -fourHeatBundleOperator (E.base.a 0) (E.base.b 0) (E.B 0) (E.C 0)
        (fun y q => E.amplitude 1 y q l) 0 k := by
    simpa only [HeatNormalBundleExtension.amplitude, Nat.cast_one, one_add_one_eq_two] using hrec
  rw [hB, hC] at hrec'
  simp only [fourHeatBundleOperator, fourHeatBundleFirst, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, fourHeatBundleZero] at hrec'
  change 2 * E.amplitude 2 0 k l =
    -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 (fun y => E.amplitude 1 y k l) 0 -
      ∑ q, twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) k q * E.amplitude 1 0 q l
  linarith only [hrec']

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local weak rough equation: the H1 pairing against a
compact chart test equals the Euclidean L2 mass and covariant pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)

include hon

variable (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hU hKU hp

theorem twoFormGramNablaL2_energy (u : SmoothH1TwoForm o) :
    (∑ i : Fin 4, inner ℝ
      (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i (smoothTwoFormToH1 u))
      (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt) i)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (∑ i : Fin 4, ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j *
          inner ℝ (twoFormLocalNabla (g := g) c S
            (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z)
            (twoFormLocalNabla (g := g) c S a j z)) := by
  let N := fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i (smoothTwoFormToH1 u)
  let B := fun i => twoFormEnergyTestL2 (g := g) c S hS a ha
    (hK.of_isClosed_subset (isClosed_tsupport a) has) (has.trans hKt) i
  have hi (i : Fin 4) : Integrable (fun z => inner ℝ (N i z) (B i z)) :=
    L2.integrable_inner (N i) (B i)
  have he : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i : Fin 4,
      inner ℝ (N i z) (B i z) = chartVolumeDensity g c z * ∑ j : Fin 4,
        (metricInChart g c z)⁻¹ i j * inner ℝ
          (twoFormLocalNabla (g := g) c S (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z)
          (twoFormLocalNabla (g := g) c S a j z) := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [twoFormGramNablaL2_coe c S hS hK hKt χ hχ hc hs u U hU hUt hKU hp i,
      twoFormEnergyTestL2_coe (g := g) c S hS a ha
        (hK.of_isClosed_subset (isClosed_tsupport a) has) (has.trans hKt) i] with z hn hb
    rw [hn, hb]
    exact energy_pairing c S χ a hon _ i z
  change (∑ i : Fin 4, inner ℝ (N i) (B i)) = _
  simp only [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ = ∫ z, chartVolumeDensity g c z *
        (∑ i : Fin 4, ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j * inner ℝ
          (twoFormLocalNabla (g := g) c S (twoFormChartValue o (u : smoothTwoForms o).val c S hS) i z)
          (twoFormLocalNabla (g := g) c S a j z)) := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      simp_rw [hz]
      exact (Finset.mul_sum ..).symm
    _ = _ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z
        (fun h => hz (hKt (has h))) j
      simp only [hzero, inner_zero_right, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic weak rough equation in actual local orthonormal-frame
coefficients. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)
  (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hon hU hKU hp

theorem twoFormLocalPairing_smooth (u : SmoothH1TwoForm o) :
    inner ℝ (smoothTwoFormToH1 u)
      (smoothTwoFormToH1 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has)) =
      twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has (smoothTwoFormToH1 u) := by
  rw [smoothTwoFormToH1.inner_map_map]
  change smoothTwoFormL2Inner (u : smoothTwoForms o) (twoFormGramTest o c S a ha hK hKt has) +
    smoothTwoFormCovariantEnergy (u : smoothTwoForms o) (twoFormGramTest o c S a ha hK hKt has) = _
  rw [smoothTwoFormL2Inner_gramTest (u : smoothTwoForms o) c S hS a ha hK hKt has,
    smoothTwoFormCovariantEnergy_gramTest (u : smoothTwoForms o) c S hS a ha hK hKt has U hU hUt hKU hp]
  unfold twoFormLocalPairing
  rw [twoFormGramVectorL2_mass c S hS hK hKt χ hχ hc hs a ha has hon u,
    twoFormGramNablaL2_energy c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp u]
  ring

theorem twoFormH1_localPairing (u : TwoFormH1 o) :
    inner ℝ u (smoothTwoFormToH1 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has)) =
      twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has u := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (continuous_id.inner continuous_const)
      (twoFormLocalPairing_continuous c S hS hK hKt χ hχ hc hs a ha has)) ?_
  intro v
  change inner ℝ (smoothTwoFormToH1 v)
    (smoothTwoFormToH1 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has)) =
      twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has (smoothTwoFormToH1 v)
  exact twoFormLocalPairing_smooth c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp v

theorem twoFormRough_localEquation (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) :
    twoFormLocalPairing c S hS hK hKt χ hχ hc hs a ha has u =
      inner ℝ f (smoothTwoFormToL2 (smoothH1ToL2 (twoFormLocalTestH1 (o := o) c S hK hKt a ha has))) := by
  rw [← twoFormH1_localPairing c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp,
    hu, twoFormRoughSolution_weak, twoFormH1ToL2_smooth]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The residual of every member of the common family is the same jointly
continuous last transport coefficient, times its explicit Gaussian factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.parametrix_residual (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (t : ℝ) (ht : 0 < t) (k l : Fin 6) :
    deriv (fun s => heatNormalBundleParametrix N.extension s x k l) t +
      fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
        (N.extension.B x) (N.extension.C x)
        (fun y q => heatNormalBundleParametrix N.extension t y q l) x k =
    fourHeatGaussian t x * t ^ 3 * E.lastCoefficient (x, frameCoordinateState g c e) k l := by
  obtain ⟨_, _, hEik, hU, hrad⟩ := N.transport hRic he x hx
  have hreg (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => N.extension.amplitude m y q l) :=
    (N.extension.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have hzero (q : Fin 6) : fourHeatRadialTransport (N.extension.base.a x) (N.extension.base.b x)
      (fun y => N.extension.amplitude 0 y q l) x = 0 := by
    by_cases hql : q = l
    · subst q
      simpa [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient] using hU
    · have hz : (fun y => N.extension.amplitude 0 y q l) = fun _ => (0 : ℝ) := by
        funext y
        simp [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient, hql]
      rw [hz]
      simpa only [zero_mul] using
        fourHeatRadialTransport_const_mul (N.extension.base.a x) (N.extension.base.b x) 0 N.extension.base.U x
  have hh := fourHeatBundlePolynomial_gaussian_residual (N.extension.base.a x) (N.extension.base.b x)
    (N.extension.B x) (N.extension.C x) (fun m y q => N.extension.amplitude m y q l) hreg t ht x hrad hEik hzero
    (by intro q; simpa using N.amplitude_transport hRic he x hx 0 (by omega) q l)
    (by intro q; convert N.amplitude_transport hRic he x hx 1 (by omega) q l using 1 <;> norm_num)
    (by intro q; convert N.amplitude_transport hRic he x hx 2 (by omega) q l using 1 <;> norm_num) k
  refine hh.trans ?_
  congr 1
  change fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
    (N.extension.B x) (N.extension.C x) (fun y q => N.extension.amplitude 3 y q l) x k = _
  rw [show N.extension.amplitude 3 = fun y => E.amplitude 3 (y, frameCoordinateState g c e)
    from N.amplitude_family 3 (by omega)]
  rw [N.a_family, N.b_family, N.B_family, N.C_family]
  exact (heatFamilyBundleOperator_slice E.a E.b E.B E.C _
    (fun q => (E.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) _ k).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local weak two-form equation with actual L2 coefficients on
both sides, including the localized forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

variable (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
  (has : tsupport a ⊆ K) (hon : ∀ z ∈ tsupport a, χ z = 1)

variable (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hon hU hKU hp

theorem twoFormRough_localL2Equation (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) :
    inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) +
      ∑ i : Fin 4, inner ℝ (twoFormGramNablaL2 c S hS hK hKt χ hχ hc hs i u)
        (twoFormEnergyTestL2 (g := g) c S hS a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
          (has.trans hKt) i) =
    inner ℝ (twoFormL2GramValue c S hK hKt χ hχ hc hs hS f)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) has)
        (has.trans hKt)) := by
  have he := twoFormRough_localEquation c S hS hK hKt χ hχ hc hs a ha has hon U hU hUt hKU hp u f hu
  rw [twoFormL2_localTest c S hS hK hKt χ hχ hc hs a ha has hon] at he
  exact mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne' he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar component divergence equations with actual L2 flux and source,
deduced from the intrinsic weak rough equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (χ ψ : FourSpace → ℝ)
  (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hχs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψs : tsupport ψ ⊆ (chartAt FourSpace c).target)
  (hon : ∀ z ∈ tsupport ψ, χ z = 1) (b : TwoFormFour)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
  {o : FrameOrientation g}

variable {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hχK : tsupport χ ⊆ K) (hψK : tsupport ψ ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)

include hon hU hKU hp hψK in
theorem twoFormRough_scalarWeakEquation (u : TwoFormH1 o) (f : TwoFormL2 o)
    (hu : u = twoFormRoughSolution f) :
    (∑ j : Fin 4, inner ℝ
      (twoFormDivergenceFlux (g := g) c χ hχ hcχ (hχK.trans hKt) b
        (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hcχ hχK i u) j)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
    inner ℝ (twoFormDivergenceSource (g := g) c S hS χ hχ hcχ (hχK.trans hKt) b
      (twoFormGramVectorL2 c S hK hKt χ hχ hcχ hχK u)
      (twoFormL2GramValue c S hK hKt χ hχ hcχ hχK hS f)
      (fun i => twoFormGramNablaL2 c S hS hK hKt χ hχ hcχ hχK i u))
      (twoFormScalarTestL2 ψ hψ hcψ) := by
  let a : FourSpace → TwoFormFour := fun z => ψ z • b
  have ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target := (hψ.smul contDiff_const).contDiffOn
  have has : tsupport a ⊆ K := (tsupport_smul_subset_left _ _).trans hψK
  have hona : ∀ z ∈ tsupport a, χ z = 1 :=
    fun z hz => hon z (tsupport_smul_subset_left _ _ hz)
  have he := twoFormRough_localL2Equation c S hS hK hKt χ hχ hcχ hχK a ha has hona
    U hU hUt hKU hp u f hu
  change inner ℝ _ (twoFormMassTestL2 (g := g) c a ha _ _) +
    (∑ i : Fin 4, inner ℝ _ (twoFormEnergyTestL2 (g := g) c S hS a ha _ _ i)) =
    inner ℝ _ (twoFormMassTestL2 (g := g) c a ha _ _) at he
  rw [twoFormMassPair_scalarTest c χ ψ hχ hcχ (hχK.trans hKt) hψ hcψ (hψK.trans hKt) hon b,
    twoFormMassPair_scalarTest c χ ψ hχ hcχ (hχK.trans hKt) hψ hcψ (hψK.trans hKt) hon b] at he
  have hi (i : Fin 4) := twoFormEnergyPair_scalarTest (g := g) c S hS χ ψ hχ hcχ (hχK.trans hKt)
    hψ hcψ (hψK.trans hKt) hon b (twoFormGramNablaL2 c S hS hK hKt χ hχ hcχ hχK i u) i
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hi i)
  rw [hsum] at he
  rw [Finset.sum_add_distrib] at he
  unfold twoFormDivergenceFlux twoFormDivergenceSource
  simp only [map_sub, inner_sub_left, sum_inner]
  rw [Finset.sum_comm]
  linarith only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts converts the ordinary two-form principal flux
into the scalar chart divergence acting on compact tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (χ ψ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
  {o : FrameOrientation g}

theorem twoFormPrincipalFlux_integrationByParts (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hcχ : HasCompactSupport χ) (hχK : tsupport χ ⊆ K)
    (u : TwoFormH1 o) (r : Fin 6) :
    (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt χ hχ hcχ hχK
      (EuclideanSpace.basisFun (Fin 6) ℝ r) u j)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
    -inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hcχ hχK (twoFormComponentIndex r) u)
      (twoFormPrincipalDivergenceTestL2 (g := g) c χ ψ hχ (hχK.trans hKt) hψ hcψ) := by
  have hterm (i j : Fin 4) : inner ℝ
      (twoFormFluxPair (g := g) c χ hχ hcχ (hχK.trans hKt)
        (EuclideanSpace.basisFun (Fin 6) ℝ r) i j
        (twoFormGramPartialVectorL2 c S hK hKt χ hχ hcχ hχK i u))
      (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
        (hcψ.fderiv_apply ℝ (coordinateVector j))) =
      -inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hcχ hχK (twoFormComponentIndex r) u)
        (twoFormPrincipalDerivativeTestL2 (g := g) c χ ψ hχ (hχK.trans hKt) hψ hcψ i j) := by
    have hpair := twoFormFluxPair_basis_test (g := g) c χ hχ hcχ (hχK.trans hKt)
      (twoFormGramPartialVectorL2 c S hK hKt χ hχ hcχ hχK i u)
      (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
      (hcψ.fderiv_apply ℝ (coordinateVector j)) i j r
    refine hpair.trans ?_
    dsimp only [twoFormGramPartialVectorL2]
    rw [twoFormVectorComponentL2_assemble]
    have he := twoFormGram_weak_partial c S hK hKt χ hχ hcχ hχK (twoFormComponentIndex r) i u
      (twoFormPrincipalTest (g := g) c χ ψ i j)
      (twoFormPrincipalTest_smooth c χ ψ hχ (hχK.trans hKt) hψ i j)
      (twoFormPrincipalTest_compact c χ ψ hcψ i j)
    exact neg_eq_iff_eq_neg.mp he.symm
  change (∑ j : Fin 4, inner ℝ (∑ i : Fin 4, _) _) = _
  simp_rw [sum_inner]
  have ht := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hterm i j))
  rw [ht, Finset.sum_comm]
  simp only [twoFormPrincipalDivergenceTestL2, inner_sum, Finset.sum_neg_distrib]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual H1 density-weighted components and their chart-operator pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (r : Fin 6) (u : TwoFormH1 o)

def twoFormWeightedComponentL2 : Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormMassPair (g := g) c χ hχ hc (hs.trans hKt) (EuclideanSpace.basisFun (Fin 6) ℝ r)
    (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)

theorem twoFormWeightedComponent_H1 : MemSobolev 1 2
    (scalarComplexL2 (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u) : 𝓢'(FourSpace, ℂ)) :=
  twoFormGramCoefficient_memSobolev_one c S hK hKt χ hχ hc hs u
    (twoFormMassCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r))
    (twoFormMassCoefficient_smooth (g := g) c χ hχ (hs.trans hKt) _)
    hc.mul_right.smul_right

theorem twoFormWeightedComponent_coe :
    twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u =ᵐ[volume] fun z =>
      χ z * chartVolumeDensity g c z *
        twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z := by
  have hv := twoFormVectorComponentL2_coe r (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
  rw [twoFormGramVectorComponent] at hv
  have hp := twoFormCoefficientPair_coe
    (twoFormMassCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r))
    (twoFormMassCoefficient_smooth (g := g) c χ hχ (hs.trans hKt) _).continuous
    hc.mul_right.smul_right (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u)
  filter_upwards [hv, hp] with z hvz hpz
  have hp' : twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u z =
      inner ℝ (twoFormGramVectorL2 c S hK hKt χ hχ hc hs u z)
        (twoFormMassCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r) z) := hpz
  rw [hp']
  simp only [twoFormMassCoefficient, inner_smul_right, EuclideanSpace.inner_basisFun_real]
  rw [hvz]

theorem twoFormWeightedComponent_operator_pairing
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ (chartAt FourSpace c).target)
    (hon : ∀ z ∈ tsupport ψ, χ z = 1) :
    inner ℝ (twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u)
      (twoFormPrincipalDivergenceTestL2 (g := g) c χ ψ hχ (hs.trans hKt) hψ hcψ) =
    ∫ z, twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u z * scalarChartOperator g c ψ z := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  apply integral_congr_ae
  filter_upwards [twoFormWeightedComponent_coe c S hK hKt χ hχ hc hs r u,
    twoFormPrincipalDivergenceTestL2_coe c χ ψ hχ (hs.trans hKt) hψ hcψ hψt hon]
    with z hw hd
  rw [hw, hd]
  by_cases hz : z ∈ tsupport ψ
  · rw [hon z hz]
    ring
  · rw [scalarChartOperator_eq_zero_off_tsupport g c ψ hz]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Removing the actual density and affine normalization from the local
H2 two-form component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (r : Fin 6) (u : TwoFormH1 o)
  (z₀ : ChartTarget c) (t : ℝ) (ht : t ≠ 0)
  (hpoint : ∀ y ∈ closedBall (0 : FourSpace) 1,
    scalarRescaledPoint g c z₀ t y ∈ K ∧ χ (scalarRescaledPoint g c z₀ t y) = 1)

include hpoint in
theorem twoFormWeightedComponent_rescaled_coe :
    (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y) *
      twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u
        (scalarRescaledPoint g c z₀ t y)) =ᵐ[volume.restrict (ball (0 : FourSpace) 1)]
      scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht) z₀
        (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u) := by
  let A := scalarRescalingLinearEquiv g c z₀ t ht
  let W := twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u
  have hmp : Measure.QuasiMeasurePreserving (fun y : FourSpace => A y + z₀) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hw := hmp.ae_eq_comp (twoFormWeightedComponent_coe c S hK hKt χ hχ hc hs r u)
  filter_upwards [ae_restrict_of_ae hw,
    ae_restrict_of_ae (scalarAffinePullbackL2_coe A z₀ W),
    ae_restrict_mem isOpen_ball.measurableSet] with y hw hy hball
  dsimp only [Function.comp_apply] at hw
  have hA := scalarRescalingLinearEquiv_apply g c z₀ t ht y
  change W (A y + z₀) = _ at hw
  rw [hA] at hw
  change scalarAffinePullbackL2 A z₀ W y = W (A y + z₀) at hy
  rw [hA] at hy
  rw [(hpoint y (ball_subset_closedBall hball)).2, one_mul] at hw
  exact (hy.trans hw).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Removing the actual density and affine normalization from the local
integer-order two-form component. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (r : Fin 6) (u : TwoFormH1 o)
  (z₀ : ChartTarget c) (t : ℝ) (ht : t ≠ 0)
  (hpoint : ∀ y ∈ closedBall (0 : FourSpace) 1,
    scalarRescaledPoint g c z₀ t y ∈ K ∧ χ (scalarRescaledPoint g c z₀ t y) = 1)

include hpoint in
theorem twoFormInteger_unweight_unscale (n : ℕ)
    (hreg : ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
      tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
        (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht) z₀
          (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)) : 𝓢'(FourSpace, ℂ))))
    (β : FourSpace → ℝ) (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hsβ : tsupport β ⊆ ball (0 : FourSpace) (1 / 2)) :
    ∃ v : Lp ℂ 2 (volume : Measure FourSpace), MemSobolev (n : ℝ) 2 (v : 𝓢'(FourSpace, ℂ)) ∧
      (v : FourSpace → ℂ) =ᵐ[volume] fun z =>
        (β ((scalarRescalingLinearEquiv g c z₀ t ht).symm (z - z₀)) *
          twoFormGramValueL2 c S hK hKt χ hχ hc hs (twoFormComponentIndex r) u z : ℝ) := by
  let A := scalarRescalingLinearEquiv g c z₀ t ht
  let ρ : FourSpace → ℝ := fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ t y)
  let b : FourSpace → ℝ := fun z => twoFormGramValueL2 c S hK hKt χ hχ hc hs
    (twoFormComponentIndex r) u z
  let w := scalarAffinePullbackL2 A z₀ (twoFormWeightedComponentL2 c S hK hKt χ hχ hc hs r u)
  have hρ0 (y : FourSpace) (hy : y ∈ tsupport β) : ρ y ≠ 0 :=
    (chartVolumeDensity_pos g c _ (hKt (hpoint y
      (ball_subset_closedBall (ball_subset_ball (by norm_num) (hsβ hy)))).1)).ne'
  have hρ (y : FourSpace) (hy : y ∈ tsupport β) :
      ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y := by
    apply ContDiffAt.inv
    · exact (chartVolumeDensity_contDiffAt g c _ (hKt (hpoint y
        (ball_subset_closedBall (ball_subset_ball (by norm_num) (hsβ hy)))).1)).comp y (by
          unfold scalarRescaledPoint
          fun_prop)
    · exact hρ0 y hy
  obtain ⟨v, hv, he⟩ := scalar_integer_density_division n ρ
    (fun y => b (scalarRescaledPoint g c z₀ t y)) w
    (twoFormWeightedComponent_rescaled_coe c S hK hKt χ hχ hc hs r u z₀ t ht hpoint)
    (fun φ hcφ hsφ => hreg φ hcφ (hsφ.trans ball_subset_closedBall)) β hβ hcβ hsβ hρ hρ0
  have he' : (v : FourSpace → ℂ) =ᵐ[volume] fun y => (β y * b (A y + z₀) : ℝ) := by
    filter_upwards [he] with y hy
    change v y = (β y * b (scalarRescaledPoint g c z₀ t y) : ℝ) at hy
    rw [scalarRescalingLinearEquiv_apply g c z₀ t ht y]
    exact hy
  exact scalar_integer_unscale n A z₀ b β v hv he'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inner cutoffs of the actual two-form coefficients inherit the
regularity of their local representatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a)
  (hca : HasCompactSupport a) (hsa : tsupport a ⊆ K)
  (hon : ∀ z ∈ tsupport a, χ z = 1) (v : Fin 2 → Fin 4) (u : TwoFormH1 o)

include hon in
theorem twoFormGram_cutoff_distribution :
    (scalarComplexL2 (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) : 𝓢'(FourSpace, ℂ)) =
      smulLeftCLM ℂ (fun z => (a z : ℂ))
        (scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u) : 𝓢'(FourSpace, ℂ)) := by
  let φ : 𝓢(FourSpace, ℂ) := (hca.toSchwartzMap ha).postcompCLM Complex.ofRealCLM
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] Lp ℂ 2 (volume : Measure FourSpace) :=
    Complex.ofRealCLM.compLpL 2 volume
  let P := (scalarL2Multiply (φ.toLp (∞ : ℝ≥0∞) volume)).restrictScalars ℝ
  have hC (f : Lp ℝ 2 (volume : Measure FourSpace)) : C f = scalarComplexL2 f := rfl
  have he : C (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) =
      P (C (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u)) := by
    refine UniformSpace.Completion.induction_on u
      (isClosed_eq (C.continuous.comp (twoFormGramValueL2 c S hK hKt a ha hca hsa v).continuous)
        (P.continuous.comp (C.continuous.comp
          (twoFormGramValueL2 c S hK hKt χ hχ hc hs v).continuous))) ?_
    intro w
    apply Lp.ext
    filter_upwards [scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt a ha hca hsa v (smoothTwoFormToH1 w)),
      twoFormGramValueL2_coe c S hK hKt a ha hca hsa v w,
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp (∞ : ℝ≥0∞) volume)
        (scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w))),
      φ.coeFn_toLp (∞ : ℝ≥0∞) volume,
      scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)),
      twoFormGramValueL2_coe c S hK hKt χ hχ hc hs v w] with z hl hal hp hφ hr hχv
    change scalarComplexL2 (twoFormGramValueL2 c S hK hKt a ha hca hsa v (smoothTwoFormToH1 w)) z =
      ((φ.toLp (∞ : ℝ≥0∞) volume) •
        scalarComplexL2 (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) :
          Lp ℂ 2 volume) z
    rw [hl, hal, hp, Complex.ofReal_mul]
    change (a z * frameTensor (chartGramMatrix g c S z)
      (twoFormCoordinates o (w : smoothTwoForms o).val c z) v : ℂ) =
        φ.toLp (∞ : ℝ≥0∞) volume z * scalarComplexL2
          (twoFormGramValueL2 c S hK hKt χ hχ hc hs v (smoothTwoFormToH1 w)) z
    rw [hφ, hr, hχv]
    have hφz : φ z = (a z : ℂ) := rfl
    rw [hφz, Complex.ofReal_mul]
    by_cases hz : a z = 0
    · simp only [hz, zero_mul, Complex.ofReal_zero]
    · rw [hon z (subset_tsupport a hz), Complex.ofReal_one, one_mul]
  change (C (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) : 𝓢'(FourSpace, ℂ)) = _
  rw [he]
  exact scalarL2Multiply_distribution φ φ.hasTemperateGrowth (φ.memLp (∞ : ℝ≥0∞) volume)
    (C (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u))

include hon in
theorem twoFormGram_cutoff_memSobolev (n : ℕ) (V : Set FourSpace) (hV : MeasurableSet V)
    (w : Lp ℂ 2 (volume : Measure FourSpace)) (hw : MemSobolev (n : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)))
    (he : (w : FourSpace → ℂ) =ᵐ[volume.restrict V] fun z =>
      (twoFormGramValueL2 c S hK hKt χ hχ hc hs v u z : ℂ)) (haV : tsupport a ⊆ V) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hca hsa v u) : 𝓢'(FourSpace, ℂ)) := by
  rw [twoFormGram_cutoff_distribution c S hK hKt χ hχ hc hs a ha hca hsa hon v u]
  exact scalar_local_sobolev_transfer n _ w hw V hV he a ha hca haV

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth partitions act linearly on the actual H1 chart
coefficients, so local regularity estimates can be assembled. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGram_cutoff_sum {ι : Type*} [Fintype ι]
    (c : M) (S : Mat4) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hsa : tsupport a ⊆ K) (b : ι → FourSpace → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hcb : ∀ i, HasCompactSupport (b i))
    (hsb : ∀ i, tsupport (b i) ⊆ K) (hsum : a = fun z => ∑ i : ι, b i z)
    (v : Fin 2 → Fin 4) (u : TwoFormH1 o) :
    twoFormGramValueL2 c S hK hKt a ha hca hsa v u =
      ∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v u := by
  let L : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
    twoFormGramValueL2 c S hK hKt a ha hca hsa v
  let R : TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
    ∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v
  have he : L u = R u := by
    refine UniformSpace.Completion.induction_on u (isClosed_eq L.continuous R.continuous) ?_
    intro w
    change twoFormGramValueL2 c S hK hKt a ha hca hsa v (smoothTwoFormToH1 w) =
      R (smoothTwoFormToH1 w)
    simp only [R, _root_.sum_apply]
    let T : FourSpace → ℝ := fun z => frameTensor (chartGramMatrix g c S z)
      (twoFormCoordinates o (w : smoothTwoForms o).val c z) v
    apply Lp.ext
    have hbe : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i : ι,
        twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v (smoothTwoFormToH1 w) z =
          b i z * frameTensor (chartGramMatrix g c S z)
            (twoFormCoordinates o (w : smoothTwoForms o).val c z) v := by
      apply Filter.eventually_all.mpr
      intro i
      exact twoFormGramValueL2_coe c S hK hKt (b i) (hb i) (hcb i) (hsb i) v w
    filter_upwards [twoFormGramValueL2_coe c S hK hKt a ha hca hsa v w,
      Lp.coeFn_finsetSum Finset.univ (fun i : ι =>
        twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v (smoothTwoFormToH1 w)),
      hbe] with z haz hsz hbz
    have hsz' : (∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v
        (smoothTwoFormToH1 w)) z = ∑ i : ι,
      twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v (smoothTwoFormToH1 w) z := by
      simpa only [Finset.sum_apply] using hsz
    calc
      _ = a z * T z := haz
      _ = ∑ i : ι, b i z * T z := by rw [hsum]; exact Finset.sum_mul ..
      _ = ∑ i : ι, twoFormGramValueL2 c S hK hKt (b i) (hb i) (hcb i) (hsb i) v
          (smoothTwoFormToH1 w) z := Finset.sum_congr rfl (fun i _ => (hbz i).symm)
      _ = _ := hsz'.symm
  simpa only [L, R, _root_.sum_apply] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! All alternating coordinates of inner cutoffs have actual H2 regularity.
This includes the coordinates used by the connection correction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)

include hS in
theorem twoFormGram_order_of_six (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ K) (u : TwoFormH1 o)
    (hreg : ∀ r : Fin 6, MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc hs (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)))
    (v : Fin 2 → Fin 4) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc hs v u) : 𝓢'(FourSpace, ℂ)) := by
  rw [twoFormGramValue_component_expansion c S hS hK hKt a ha hc hs v u]
  apply scalarReal_memSobolev_finset
  intro r _
  rw [scalarComplexL2_real_smul_distribution]
  exact (hreg r).smul _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local representatives in possibly different inner cutoffs give
integer Sobolev regularity for every compactly supported chart cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_local_sobolev_assembly (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hVK : V ⊆ K) (u : TwoFormH1 o)
    (hloc : ∀ r : Fin 6, ∀ x ∈ V,
      ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
        (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ x ∈ W ∧
          (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
            MemSobolev (n : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
            (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
              (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ))
    (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (haV : tsupport a ⊆ V) (v : Fin 2 → Fin 4) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hca (haV.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  apply twoFormGram_order_of_six c S hS hK hKt n a ha hca (haV.trans hVK) u
  intro r
  let X := {x : FourSpace // x ∈ tsupport a}
  have hx (x : X) := hloc r x (haV x.property)
  choose η hη hcη hηK W hW hxW hone w hw he using hx
  have hcover : tsupport a ⊆ ⋃ x : X, W x := by
    intro x hx
    exact mem_iUnion_of_mem ⟨x, hx⟩ (hxW ⟨x, hx⟩)
  obtain ⟨s, hs⟩ := hca.elim_finite_subcover W hW hcover
  let ι := {x : X // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : tsupport a ⊆ ⋃ i : ι, W i.val := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨i, hi⟩ hxi
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (M := FourSpace) hca.isClosed (fun i : ι => W i.val)
      (fun i => hW i.val) hfinite
  let b : ι → FourSpace → ℝ := fun i z => a z * ρ i z
  have hb (i : ι) : ContDiff ℝ ∞ (b i) := ha.mul (ρ i).contMDiff.contDiff
  have hbc (i : ι) : HasCompactSupport (b i) := hca.mul_right
  have hbK (i : ι) : tsupport (b i) ⊆ K := tsupport_mul_subset_left.trans (haV.trans hVK)
  have hbW (i : ι) : tsupport (b i) ⊆ W i.val := tsupport_mul_subset_right.trans (hρ i)
  have hparts (i : ι) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt (b i) (hb i) (hbc i) (hbK i)
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormGram_cutoff_memSobolev c S hK hKt (η i.val) (hη i.val) (hcη i.val) (hηK i.val)
      (b i) (hb i) (hbc i) (hbK i) (fun z hz => hone i.val z (hbW i hz))
      (twoFormComponentIndex r) u n (W i.val) (hW i.val).measurableSet
      (w i.val) (hw i.val) (he i.val) (hbW i)
  have hsum : a = fun z => ∑ i : ι, b i z := by
    funext z
    by_cases hz : a z = 0
    · simp only [b, hz, zero_mul, Finset.sum_const_zero]
    · have hρz : (∑ i : ι, ρ i z) = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (subset_tsupport a hz)
      change a z = ∑ i : ι, a z * ρ i z
      rw [← Finset.mul_sum, hρz, mul_one]
  rw [twoFormGram_cutoff_sum c S hK hKt a ha hca (haV.trans hVK) b hb hbc hbK hsum]
  exact scalarReal_memSobolev_finset n Finset.univ _ (fun i _ => hparts i)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The linear-eigenvalue Hodge equation has actual integer-order forcing in its scalar
principal part. No regularity of the weak solution is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (κ : ℝ)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormEigen_principalWeakInteger (b : TwoFormFour) :
    ∃ R : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 R : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ) := by
  obtain ⟨D, hD, hDH⟩ := twoFormFluxCorrection_integer_derivatives n c S hS hK hKt hVK u hreg
    η hη hcη hηV b
  let F := fun j => twoFormDivergenceFlux (g := g) c η hη hcη ((hηV.trans hVK).trans hKt) b
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u) j
  let C := fun j => twoFormFluxCorrection c S hS hK hKt η hη hcη (hηV.trans hVK) b u j
  let R₀ := twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
    (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
    (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)
  refine ⟨R₀ - ∑ j : Fin 4, D j, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (_ - _))
    rw [map_sub]
    have hsum : MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ j : Fin 4, D j) :
        𝓢'(FourSpace, ℂ)) := by
      apply scalarReal_memSobolev_finset n
      intro j _
      exact hDH j
    exact (twoFormEigenDivergenceSource_integer n c S hS hK hKt hV hVK u κ hreg
      η hη hcη hηV b).sub hsum
  · intro ψ hψ hcψ hψK hon
    have hF := twoFormRough_scalarWeakEquation c S hS η ψ hη hcη hψ hcψ hon b
      hK hKt (hηV.trans hVK) hψK U hU hUt hKU hp u
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u) hu
    have he := scalar_divergence_corrected_flux F C D R₀ hD ψ hψ hcψ hF
    have heq : (∑ j : Fin 4, inner ℝ (F j + C j)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) =
        ∑ j : Fin 4, inner ℝ (twoFormPrincipalFlux c S hK hKt η hη hcη (hηV.trans hVK) b u j)
          (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
            (hcψ.fderiv_apply ℝ (coordinateVector j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun v => inner ℝ v (twoFormScalarTestL2 (fun z => partialDeriv ψ j z)
        (twoFormCutoffPartial_smooth ψ hψ j) (hcψ.fderiv_apply ℝ (coordinateVector j))))
        (twoFormPrincipalFlux_eq c S hS hK hKt η hη hcη (hηV.trans hVK) b u j)
    rw [heq] at he
    exact he

include hV hU hKU hp hu hreg in
theorem twoFormEigen_weightedWeakInteger (r : Fin 6) :
    ∃ F : Lp ℝ 2 (volume : Measure FourSpace),
      MemSobolev (n : ℝ) 2 (scalarComplexL2 F : 𝓢'(FourSpace, ℂ)) ∧
      ∀ (ψ : FourSpace → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hcψ : HasCompactSupport ψ),
      tsupport ψ ⊆ K → (∀ z ∈ tsupport ψ, η z = 1) →
      (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = ∫ z, F z * ψ z := by
  obtain ⟨R, hRH, hR⟩ := twoFormEigen_principalWeakInteger n c S hS hK hKt hV hVK U hU hUt hKU hp u κ hu hreg η hη hcη hηV
      (EuclideanSpace.basisFun (Fin 6) ℝ r)
  refine ⟨-R, ?_, ?_⟩
  · let T : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
      ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
        (Complex.ofRealCLM.compLpL 2 volume)
    change MemSobolev (n : ℝ) 2 (T (-R))
    rw [map_neg]
    exact hRH.neg
  · intro ψ hψ hcψ hψK hon
    have he := hR ψ hψ hcψ hψK hon
    rw [twoFormPrincipalFlux_integrationByParts c η ψ hη hψ hcψ S hK hKt hcη (hηV.trans hVK) u r,
      twoFormWeightedComponent_operator_pairing c S hK hKt η hη hcη (hηV.trans hVK) r u
        ψ hψ hcψ (hψK.trans hKt) hon] at he
    have hv : (∫ z, twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u z *
        scalarChartOperator g c ψ z) = inner ℝ (-R) (twoFormScalarTestL2 ψ hψ hcψ) := by
      rw [inner_neg_left]
      linarith only [he]
    rw [hv, L2.inner_def]
    simp only [RCLike.inner_apply', conj_trivial]
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => (-R) z * t) hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual local elliptic step for linear-eigenvalue Hodge two-forms at any finite
Sobolev order, with the metric coefficients and forcing from the Hodge equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K)
  (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
  (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (u : TwoFormH1 o) (κ : ℝ)
  (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hU hKU hp hu hreg in
theorem twoFormEigen_weighted_integer (r : Fin 6) (z₀ : ChartTarget c)
    (hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val) :
    ∃ (t : ℝ) (ht : 0 < t),
      (∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ t y ∈ K ∧ η (scalarRescaledPoint g c z₀ t y) = 1) ∧
      ∀ φ : 𝓢(FourSpace, ℂ), HasCompactSupport (φ : FourSpace → ℂ) →
        tsupport (φ : FourSpace → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ t ht.ne') z₀
            (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u)) :
              𝓢'(FourSpace, ℂ))) := by
  obtain ⟨F, hFH, hF⟩ := twoFormEigen_weightedWeakInteger n c S hS hK hKt hV hVK
    U hU hUt hKU hp u κ hu hreg η hη hcη hηV r
  apply scalarEuclidean_local_integer n g c z₀ {z | z ∈ K ∧ η z = 1} hnear
    (twoFormWeightedComponentL2 c S hK hKt η hη hcη (hηV.trans hVK) r u) F
    (twoFormWeightedComponent_H1 c S hK hKt η hη hcη (hηV.trans hVK) r u) hFH
  intro ψ hψ hcψ hsψ
  exact hF ψ hψ hcψ (fun z hz => (hsψ hz).1) (fun z hz => (hsψ hz).2)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A linear-eigenvalue Hodge two-form with local H^(n+1) control has actual H^(n+2)
representatives near each point, in the original chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_improved_representative (n : ℕ) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) {K V : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
    (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
    (r : Fin 6) (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ w : Lp ℂ 2 (volume : Measure FourSpace),
          MemSobolev ((n + 2 : ℕ) : ℝ) 2 (w : 𝓢'(FourSpace, ℂ)) ∧
          (w : FourSpace → ℂ) =ᵐ[volume.restrict W] fun z =>
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u z : ℂ) := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hnear : {z | z ∈ K ∧ η z = 1} ∈ 𝓝 z₀.val := by
    filter_upwards [η.eventuallyEq_one] with z hz
    exact ⟨hηK (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [show η z = 1 from hz]; norm_num)), hz⟩
  obtain ⟨t, ht, hpoint, hgain⟩ := twoFormEigen_weighted_integer n c S hS hK hKt hV hVK
    U hU hUt hKU hp u κ hu hreg η η.contDiff η.hasCompactSupport hηV r z₀ hnear
  let A := scalarRescalingLinearEquiv g c z₀ t ht.ne'
  let β : ContDiffBump (0 : FourSpace) :=
    { rIn := 1 / 8
      rOut := 1 / 4
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  have hsβ : tsupport (β : FourSpace → ℝ) ⊆ ball (0 : FourSpace) (1 / 2) := by
    rw [β.tsupport_eq]
    exact closedBall_subset_ball (by norm_num)
  obtain ⟨w, hw, he⟩ := twoFormInteger_unweight_unscale c S hK hKt η η.contDiff η.hasCompactSupport
    hηK r u z₀ t ht.ne' hpoint (n + 2) hgain β β.contDiff β.hasCompactSupport hsβ
  let W : Set FourSpace := (fun z => A.symm (z - z₀)) ⁻¹' ball 0 (1 / 8)
  have hW : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have hzW : z₀.val ∈ W := by
    dsimp only [W]
    simp only [Set.mem_preimage, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ t (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ t ht.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hone (z : FourSpace) (hz : z ∈ W) : η z = 1 := by
    have hpz := hpoint (A.symm (z - z₀))
      (closedBall_subset_closedBall (by norm_num) (ball_subset_closedBall hz))
    rw [hinv] at hpz
    exact hpz.2
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, W, hW, hzW, ?_, hone, w, hw, ?_⟩
  · intro z hz
    exact hηV (subset_tsupport (η : FourSpace → ℝ)
      (by change η z ≠ 0; rw [hone z hz]; norm_num))
  · filter_upwards [ae_restrict_of_ae he, ae_restrict_mem hW.measurableSet] with z hz hzW
    rw [hz, β.one_of_mem_closedBall (ball_subset_closedBall hzW), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart cutoff of an actual weak linear-eigenvalue Hodge two-form has
all integer Sobolev orders. The bootstrap stays on a fixed open set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_local_all_orders (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u)) :
    ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
  have hreg : ∀ (n : ℕ) (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
        (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)) := by
    intro n
    induction n with
    | zero =>
        intro a ha hc hs v
        simpa only [Nat.zero_add, Nat.cast_one] using
          twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u
    | succ n ih =>
        intro a ha hc hs v
        change MemSobolev ((n + 2 : ℕ) : ℝ) 2 _
        apply twoForm_local_sobolev_assembly (n + 2) c S hS hK hKt hVK u _ a ha hc hs v
        intro r x hx
        let z₀ : ChartTarget c := ⟨x, hKt (hVK hx)⟩
        obtain ⟨η, hη, hcη, hηK, W, hW, hxW, _, hone, w, hw, he⟩ :=
          twoFormEigen_improved_representative n c S hS hK hKt hV hVK U hU hUt hKU hp
            u κ hu ih r z₀ hx
        exact ⟨η, hη, hcη, hηK, W, hW, hxW, hone, w, hw, he⟩
  intro n a ha hc hs v
  exact (hreg n a ha hc hs v).mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth representatives of the six actual linear-eigenvalue Hodge chart coefficients,
on one common neighborhood. All Sobolev estimates come from the weak
harmonic equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution Metric
open scoped BigOperators Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_smooth_coefficients (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hV : IsOpen V) (hVK : V ⊆ K)
    (U : Set FourSpace) (hU : IsOpen U) (hUt : U ⊆ (chartAt FourSpace c).target)
    (hKU : K ⊆ U)
    (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
    (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u))
    (z₀ : ChartTarget c) (hzV : z₀.val ∈ V) :
    ∃ (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hηK : tsupport η ⊆ K), ∃ W : Set FourSpace, IsOpen W ∧ z₀.val ∈ W ∧
        W ⊆ V ∧ (∀ z ∈ W, η z = 1) ∧ ∃ F : Fin 6 → FourSpace → ℝ,
          (∀ r, ContDiff ℝ ∞ (F r)) ∧ ∀ r,
            (twoFormGramValueL2 c S hK hKt η hη hcη hηK (twoFormComponentIndex r) u :
              FourSpace → ℝ) =ᵐ[volume] F r := by
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hzV)
  let η : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hηV : tsupport (η : FourSpace → ℝ) ⊆ V := by rw [η.tsupport_eq]; exact hdV
  let hηK := hηV.trans hVK
  have hreg (r : Fin 6) (n : ℕ) : MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u) : 𝓢'(FourSpace, ℂ)) :=
    twoFormEigen_local_all_orders c S hS hK hKt hV hVK U hU hUt hKU hp u κ hu n
      η η.contDiff η.hasCompactSupport hηV (twoFormComponentIndex r)
  have hrep (r : Fin 6) : ∃ f : FourSpace → ℝ, ContDiff ℝ ∞ f ∧
      (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u : FourSpace → ℝ) =ᵐ[volume] f := by
    obtain ⟨f, hf, he⟩ := scalar_L2_sobolev_smooth_real_representative
      (scalarComplexL2 (twoFormGramValueL2 c S hK hKt η η.contDiff η.hasCompactSupport hηK
        (twoFormComponentIndex r) u)) (hreg r)
    refine ⟨f, hf, ?_⟩
    filter_upwards [he, scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η η.contDiff
      η.hasCompactSupport hηK (twoFormComponentIndex r) u)] with z hz hc
    simpa only [hc, Complex.ofReal_re] using hz
  choose F hF he using hrep
  refine ⟨η, η.contDiff, η.hasCompactSupport, hηK, ball z₀.val (d / 2), isOpen_ball,
    mem_ball_self (half_pos hd), ?_, ?_, F, hF, he⟩
  · exact (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hd.le))).trans hdV
  · intro z hz
    exact η.one_of_mem_closedBall (ball_subset_closedBall hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth local representatives of completed two-forms, characterized
by their actual L2 pairings with compactly supported chart tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_smooth_local_representative (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K W : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηK : tsupport η ⊆ K) (hW : IsOpen W) (hWK : W ⊆ K)
    (hone : ∀ z ∈ W, η z = 1) (u : TwoFormH1 o)
    (F : FourSpace → TwoFormFour) (hF : ContDiff ℝ ∞ F)
    (hrep : twoFormGramVectorL2 c S hK hKt η hη hcη hηK u =ᵐ[volume] F)
    (z₀ : FourSpace) (hzW : z₀ ∈ W) :
    ∃ (Z : Set FourSpace) (v : smoothTwoForms o), IsOpen Z ∧ z₀ ∈ Z ∧ ∃ hZW : Z ⊆ W,
      ∀ (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
        (has : tsupport a ⊆ Z),
        inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (twoFormGramTest o c S a ha hK hKt (has.trans (hZW.trans hWK)))) =
        inner ℝ (smoothTwoFormToL2 v)
          (smoothTwoFormToL2 (twoFormGramTest o c S a ha hK hKt (has.trans (hZW.trans hWK)))) := by
  obtain ⟨d, hd, hdW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hzW)
  let ψ : ContDiffBump z₀ :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  let B : FourSpace → TwoFormFour := fun z => ψ z • F z
  have hB : ContDiff ℝ ∞ B := ψ.contDiff.smul hF
  have hBK : tsupport B ⊆ K := by
    apply (tsupport_smul_subset_left (ψ : FourSpace → ℝ) F).trans
    rw [ψ.tsupport_eq]
    exact hdW.trans hWK
  let v := twoFormGramTest o c S B hB.contDiffOn hK hKt hBK
  let Z := ball z₀ (d / 2)
  have hZW : Z ⊆ W :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hd.le))).trans hdW
  refine ⟨Z, v, isOpen_ball, mem_ball_self (half_pos hd), hZW, ?_⟩
  intro a ha has
  let hasK := has.trans (hZW.trans hWK)
  have hon : ∀ z ∈ tsupport a, η z = 1 := fun z hz => hone z (hZW (has hz))
  have hl := twoFormL2_localTest c S hS hK hKt η hη hcη hηK a ha hasK hon
    (twoFormH1ToL2 u)
  have hr := twoFormL2_localTest c S hS hK hKt η hη hcη hηK a ha hasK hon
    (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
  rw [twoFormL2GramValue_H1] at hl
  have hv : twoFormL2GramValue c S hK hKt η hη hcη hηK hS
      (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) =ᵐ[volume]
      fun z => η z • twoFormChartValue o v.val c S hS z := by
    have he := twoFormL2GramValue_smooth c S hK hKt η hη hcη hηK hS
      (v : SmoothL2TwoForm o)
    have hae : (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) : FourSpace → TwoFormFour) =ᵐ[volume]
        smoothTwoFormGramL2Linear c S hK hKt η hη hcη hηK (v : SmoothL2TwoForm o) :=
      Filter.Eventually.of_forall (fun z => congrArg
        (fun w : Lp TwoFormFour 2 (volume : Measure FourSpace) => w z) he)
    exact hae.trans (twoFormGramVectorL2_coe c S hS hK hKt η hη hcη hηK (smoothL2AsH1 v))
  have he : inner ℝ (twoFormGramVectorL2 c S hK hKt η hη hcη hηK u)
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) hasK)
        (hasK.trans hKt)) =
      inner ℝ (twoFormL2GramValue c S hK hKt η hη hcη hηK hS
        (smoothTwoFormToL2 (v : SmoothL2TwoForm o)))
      (twoFormMassTestL2 (g := g) c a ha (hK.of_isClosed_subset (isClosed_tsupport a) hasK)
        (hasK.trans hKt)) := by
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrep, hv, twoFormMassTestL2_coe (g := g) c a ha
      (hK.of_isClosed_subset (isClosed_tsupport a) hasK) (hasK.trans hKt)] with z hu hv hm
    rw [hu, hv, hm]
    by_cases hz : z ∈ tsupport a
    · have hzZ := has hz
      have hzK := hasK hz
      have hψ : ψ z = 1 := ψ.one_of_mem_closedBall (ball_subset_closedBall hzZ)
      have hvz : twoFormChartValue o v.val c S hS z = B z :=
        twoFormGramTest_value c S hS B hB.contDiffOn hK hKt hBK z (hKt hzK)
      rw [hvz, hon z hz, one_smul]
      change inner ℝ (F z) _ = inner ℝ (ψ z • F z) _
      rw [hψ, one_smul]
    · have haz := image_eq_zero_of_notMem_tsupport hz
      simp only [twoFormMassTest, haz, smul_zero, inner_zero_right]
  exact hl.trans ((congrArg (fun r : ℝ => (normalizedChartFactor g).toReal * r) he).trans hr.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual weak linear-eigenvalue Hodge two-form agrees locally, in all smooth
test pairings, with a constructed smooth global section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_local_smooth (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u)) (x : M) :
    ∃ (O : Set M) (v : smoothTwoForms o), IsOpen O ∧ x ∈ O ∧
      ∀ w : smoothTwoForms o, tsupport w.val ⊆ O →
        inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
          inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o))
            (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) := by
  let z₀ : ChartTarget x := ⟨chartAt FourSpace x x, mem_chart_target FourSpace x⟩
  obtain ⟨S, hS, U, hU, hUt, hp, χ, hχ, hcχ, hχU, hnear⟩ :=
    twoForm_regularity_cutoff o x z₀
  let K := tsupport χ
  have hKt : K ⊆ (chartAt FourSpace x).target := hχU.trans hUt
  obtain ⟨V, hVKχ, hV, hzV⟩ := _root_.mem_nhds_iff.mp hnear
  have hVK : V ⊆ K := fun z hz => (hVKχ hz).1
  obtain ⟨η, hη, hcη, hηK, W, hW, hzW, hWV, hone, F, hF, heF⟩ :=
    twoFormEigen_smooth_coefficients x S hS hcχ hKt hV hVK U hU hUt hχU hp u κ hu z₀ hzV
  let B : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun r => F r z)
  have hB : ContDiff ℝ ∞ B := (contDiff_piLp (p := 2)).mpr hF
  have hrep : twoFormGramVectorL2 x S hcχ hKt η hη hcη hηK u =ᵐ[volume] B :=
    twoFormAssembleL2_coe _ u B heF
  obtain ⟨Z, v, hZ, hzZ, hZW, he⟩ := twoForm_smooth_local_representative x S hS hcχ hKt
    η hη hcη hηK hW (hWV.trans hVK) hone u B hB hrep z₀ hzW
  let O := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' Z
  refine ⟨O, v, (chartAt FourSpace x).isOpen_inter_preimage hZ,
    ⟨mem_chart_source FourSpace x, hzZ⟩, ?_⟩
  intro w hw
  have hws : tsupport w.val ⊆ (chartAt FourSpace x).symm '' Z := by
    intro y hy
    exact ⟨chartAt FourSpace x y, (hw hy).2, (chartAt FourSpace x).left_inv (hw hy).1⟩
  obtain ⟨a, ha, has, haw⟩ := twoForm_supported_gramTest x S hS hcχ hKt
    (hZW.trans (hWV.trans hVK)) w hws
  have he' := he a ha has
  have hl : smoothTwoFormToL2 (twoFormGramTest o x S a ha hcχ hKt
      (has.trans (hZW.trans (hWV.trans hVK)))) = smoothTwoFormToL2 (w : SmoothL2TwoForm o) :=
    congrArg (fun t : smoothTwoForms o => smoothTwoFormToL2 (t : SmoothL2TwoForm o)) haw
  exact (congrArg (fun t : TwoFormL2 o => inner ℝ (twoFormH1ToL2 u) t) hl).symm.trans
    (he'.trans (congrArg (fun t : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) t) hl))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual weak linear-eigenvalue Hodge two-forms have smooth global representatives.
A finite partition of unity assembles the local test-pairing identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigen_smooth_representative (u : TwoFormH1 o) (κ : ℝ)
    (hu : u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + κ • twoFormH1ToL2 u)) :
    ∃ v : smoothTwoForms o, twoFormH1ToL2 u = smoothTwoFormToL2 (v : SmoothL2TwoForm o) := by
  choose O v hO hx he using twoFormEigen_local_smooth u κ hu
  have hcover : (univ : Set M) ⊆ ⋃ x : M, O x := by
    intro x _
    exact mem_iUnion_of_mem x (hx x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcover
  let ι := {x : M // x ∈ s}
  let : Fintype ι := Finset.Subtype.fintype s
  have hfinite : (univ : Set M) ⊆ ⋃ i : ι, O i.val := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨y, hy⟩ hxy
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ (fun i : ι => O i.val)
      (fun i => hO i.val) hfinite
  let R : ι → SmoothScalar (M := M) := fun i => ⟨ρ i, (ρ i).contMDiff⟩
  have hR (x : M) : ∑ i : ι, (R i).val x = 1 := by
    simpa only [R, finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let V : smoothTwoForms o := ∑ i : ι, smoothTwoFormProduct (R i) (v i.val)
  refine ⟨V, twoFormL2_eq_of_smooth_pairings _ _ ?_⟩
  intro w
  have hpart := smoothTwoForm_partition_weights R hR (w : smoothTwoForms o)
  have hsum : smoothTwoFormToL2 w = ∑ i : ι,
      smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o) := by
    have heq := congrArg (fun a : smoothTwoForms o => smoothTwoFormToL2 (a : SmoothL2TwoForm o)) hpart
    exact heq.symm.trans (map_sum smoothTwoFormToL2 _ _)
  calc
    inner ℝ (twoFormH1ToL2 u) (smoothTwoFormToL2 w) =
        ∑ i : ι, inner ℝ (twoFormH1ToL2 u)
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      rw [hsum, inner_sum]
    _ = ∑ i : ι, inner ℝ (smoothTwoFormToL2 (v i.val : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (w : smoothTwoForms o) : SmoothL2TwoForm o)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply he i.val
      exact (tsupport_smul_subset_left (R i).val (w : smoothTwoForms o).val).trans (hρ i)
    _ = ∑ i : ι, inner ℝ
          (smoothTwoFormToL2 (smoothTwoFormProduct (R i) (v i.val) : SmoothL2TwoForm o))
          (smoothTwoFormToL2 w) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (smoothTwoForm_product_inner (R i) (v i.val) (w : smoothTwoForms o)).symm
    _ = inner ℝ (smoothTwoFormToL2 (V : SmoothL2TwoForm o)) (smoothTwoFormToL2 w) := by
      rw [← sum_inner]
      congr 1
      exact (map_sum smoothTwoFormToL2 _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every eigenvector of the actual compact Hodge resolvent has a smooth
representative satisfying the geometric Hodge eigenvalue equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_weakEigen_rough (u : TwoFormH1 o) (κ : ℝ)
    (hu : ∀ v, twoFormHodgeForm u v = κ * inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v)) :
    u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
      κ • twoFormH1ToL2 u) := by
  apply twoFormRoughSolution_unique
  intro v
  have he := hu v
  unfold twoFormHodgeForm at he
  rw [inner_add_left, real_inner_smul_left]
  linarith only [he]

theorem twoForm_weakEigen_smooth (hRic : RicciThree g) (u : TwoFormH1 o) (κ : ℝ)
    (hu : ∀ v, twoFormHodgeForm u v = κ * inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v)) :
    ∃ w : smoothTwoForms o, u = smoothTwoFormToH1 (w : SmoothH1TwoForm o) ∧
      smoothHodgeLaplacian hRic w = κ • w := by
  obtain ⟨w, hw⟩ := twoFormEigen_smooth_representative u κ (twoForm_weakEigen_rough u κ hu)
  have he : u = smoothTwoFormToH1 (w : SmoothH1TwoForm o) :=
    twoFormH1ToL2_injective hRic (hw.trans (twoFormH1ToL2_smooth _).symm)
  refine ⟨w, he, smoothTwoForm_eq_of_pairings _ _ ?_⟩
  intro v
  have hQ := hu (smoothTwoFormToH1 (v : SmoothH1TwoForm o))
  rw [he] at hQ
  have hpair : inner ℝ (twoFormH1ToL2 (smoothTwoFormToH1 (w : SmoothH1TwoForm o)))
      (twoFormH1ToL2 (smoothTwoFormToH1 (v : SmoothH1TwoForm o))) =
      smoothTwoFormL2Inner w v := by
    exact (congrArg₂ (fun a b : TwoFormL2 o => inner ℝ a b)
      (twoFormH1ToL2_smooth (w : SmoothH1TwoForm o))
      (twoFormH1ToL2_smooth (v : SmoothH1TwoForm o))).trans
        (smoothTwoFormToL2.inner_map_map _ _)
  calc
    _ = twoFormHodgeForm (smoothTwoFormToH1 (w : SmoothH1TwoForm o))
        (smoothTwoFormToH1 (v : SmoothH1TwoForm o)) := smoothHodgeLaplacian_pairing hRic w v
    _ = κ * smoothTwoFormL2Inner w v := hQ.trans (congrArg (κ * ·) hpair)
    _ = _ := (smoothTwoFormL2Inner_smul κ w v).symm

theorem twoFormResolvent_eigenvector_smooth (hRic : RicciThree g) {μ : ℝ} {f : TwoFormL2 o}
    (hf : Module.End.HasEigenvector (twoFormShiftedResolvent hRic).toLinearMap μ f) :
    ∃ w : smoothTwoForms o, f = smoothTwoFormToL2 (w : SmoothL2TwoForm o) ∧
      smoothHodgeLaplacian hRic w = (μ⁻¹ - 1) • w := by
  obtain ⟨u, hu, he⟩ := twoFormResolvent_eigenvector_weak hRic hf
  obtain ⟨w, hw, hL⟩ := twoForm_weakEigen_smooth hRic u (μ⁻¹ - 1) (fun v => by
    rw [he v, hu])
  exact ⟨w, hu.symm.trans ((congrArg twoFormH1ToL2 hw).trans (twoFormH1ToL2_smooth _)), hL⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! A complete orthonormal basis of actual smooth Hodge eigenforms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigenvector_smooth (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    ∃ w : smoothTwoForms o, twoFormEigenvector hRic i = smoothTwoFormToL2 (w : SmoothL2TwoForm o) ∧
      smoothHodgeLaplacian hRic w = (i.1.val⁻¹ - 1) • w :=
  twoFormResolvent_eigenvector_smooth hRic (twoFormEigenvector_hasEigenvector hRic i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! An L2 distributional Hodge equation against actual smooth sections
lies in the domain of the Hodge generator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodge_resolvent_of_distribution (hRic : RicciThree g)
    (f h : TwoFormL2 o)
    (hweak : ∀ v : smoothTwoForms o,
      inner ℝ f (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) =
        inner ℝ h (smoothTwoFormToL2 (v : SmoothL2TwoForm o))) :
    twoFormShiftedResolvent hRic (f + h) = f := by
  apply (twoFormEigenbasis hRic).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simp only [twoFormEigenbasis, HilbertBasis.coe_mk]
  obtain ⟨v, hv, hLv⟩ := twoFormEigenvector_smooth hRic i
  have hL : smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
      (i.1.val⁻¹ - 1) • twoFormEigenvector hRic i := by
    have he : (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o) =
        (i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o) := hLv
    calc
      _ = smoothTwoFormToL2 ((i.1.val⁻¹ - 1) • (v : SmoothL2TwoForm o)) :=
        congrArg smoothTwoFormToL2 he
      _ = (i.1.val⁻¹ - 1) • smoothTwoFormToL2 (v : SmoothL2TwoForm o) :=
        smoothTwoFormToL2.map_smul _ _
      _ = _ := congrArg ((i.1.val⁻¹ - 1) • ·) hv.symm
  have hpair := hweak v
  rw [hL, ← hv, real_inner_smul_right] at hpair
  have hEig := Module.End.mem_eigenspace_iff.mp (twoFormEigenvector_hasEigenvector hRic i).1
  change twoFormShiftedResolvent hRic (twoFormEigenvector hRic i) =
    i.1.val • twoFormEigenvector hRic i at hEig
  calc
    _ = inner ℝ (twoFormShiftedResolvent hRic (f + h)) (twoFormEigenvector hRic i) :=
      real_inner_comm _ _
    _ = inner ℝ (f + h) (twoFormShiftedResolvent hRic (twoFormEigenvector hRic i)) :=
      twoFormShiftedResolvent_symmetric hRic _ _
    _ = i.1.val * (inner ℝ f (twoFormEigenvector hRic i) +
        inner ℝ h (twoFormEigenvector hRic i)) := by
      rw [hEig, real_inner_smul_right, inner_add_left]
    _ = inner ℝ f (twoFormEigenvector hRic i) := by
      rw [← hpair]
      have hne := (twoFormSpectralValue_bounds hRic i.1).1.ne'
      field_simp
      ring
    _ = _ := real_inner_comm _ _

theorem twoFormHodgeDomain_of_distribution (hRic : RicciThree g)
    (f h : TwoFormL2 o)
    (hweak : ∀ v : smoothTwoForms o,
      inner ℝ f (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) =
        inner ℝ h (smoothTwoFormToL2 (v : SmoothL2TwoForm o))) :
    ∃ hf : f ∈ twoFormHodgeDomain hRic, twoFormHodgeGenerator hRic ⟨f, hf⟩ = h := by
  have he := twoFormHodge_resolvent_of_distribution hRic f h hweak
  have hf : f ∈ twoFormHodgeDomain hRic := ⟨f + h, he⟩
  refine ⟨hf, ?_⟩
  have hi : (twoFormHodgeDomainEquiv hRic).symm ⟨f, hf⟩ = f + h := by
    apply (twoFormHodgeDomainEquiv hRic).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext he.symm
  change (twoFormHodgeDomainEquiv hRic).symm ⟨f, hf⟩ - f = h
  rw [hi]
  abel

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The time derivative and Hodge image are combined before estimation,
so the actual Gaussian transport cancellations are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneResidualColumn_regular (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 4) :
    ContDiff ℝ 2 (heatNormalOneResidualColumn E χ t l) :=
  (heatNormalOneTimeColumn_regular E χ (hχ.of_le (by norm_num)) t l).add
    (heatNormalOneOperatorAmplitude_regular E _ (heatNormalOneCutoffColumn_regular E χ hχ t l))

theorem heatNormalOneResidualColumn_support (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) :
    tsupport (heatNormalOneResidualColumn E χ t l) ⊆ tsupport χ :=
  (tsupport_add _ _).trans (union_subset (heatNormalOneTimeColumn_support E χ t l)
    ((heatNormalOneOperatorAmplitude_support E _).trans (heatNormalOneCutoffColumn_support E χ t l)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact component-integral pairing for compact normal amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneAmplitudeL2_pairing_sum
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      (normalizedChartFactor g).toReal * ∑ k : Fin 4, ∫ x,
        a x k * (frameExponentialJacobian g o e x *
          heatNormalOneValue c D.point v x k) := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalOneValue c D.point v x k
  have hV : ContinuousOn (heatNormalOneValue c D.point v)
      C.source := by
    intro x hx
    have hv : ContDiffAt ℝ 2 (heatNormalOneValue c D.point v) x := by
      apply (contDiffAt_piLp (p := 2)).mpr
      intro k
      exact heatNormalOneFormValue_regular 2 c D.point v x
        (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx)) k
    exact hv.continuousAt.continuousWithinAt
  have hf (k : Fin 4) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hi (k : Fin 4) : Integrable (fun x => a x k * f k x) := by
    have hak := ((contDiff_piLp (p := 2)).mp ha k).continuous
    have hck : HasCompactSupport (fun x => a x k) :=
      hc.of_isClosed_subset (isClosed_tsupport _) (heatOneAmplitude_component_support a k)
    have hfk (x : FourSpace) (hx : x ∈ tsupport (fun y => a y k)) : ContinuousAt (f k) x :=
      (hf k).continuousAt (C.open_source.mem_nhds (hs (heatOneAmplitude_component_support a k hx)))
    simpa only [mul_comm] using fourHeat_local_product_integrable (f k) (fun x => a x k) hak hck hfk
  have hpair := heatNormalOneAmplitudeL2_pairing_normal D C hE hCt hP hD a ha hc hs v
  apply hpair.trans
  congr 1
  calc
    _ = ∫ x, ∑ k : Fin 4, a x k * f k x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      change frameExponentialJacobian g o e x *
        (heatNormalOneValue c D.point v x k * a x k) = _
      dsimp only [f]
      ring
    _ = _ := integral_finsetSum _ (fun k _ => hi k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Hodge-domain membership for compact amplitudes throughout the
common normal ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.compact_hodge_domain (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 N.frameData.point C.source) (hD : C.source ⊆ Metric.ball 0 N.frameData.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (hsmall : tsupport a ⊆ Metric.ball 0 r) :
    ∃ hf : heatNormalAmplitudeL2 N.frameData C hCt hP hD a (ha.of_le (by norm_num)) hc hs ∈
        twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨heatNormalAmplitudeL2 N.frameData C hCt hP hD a
        (ha.of_le (by norm_num)) hc hs, hf⟩ = heatNormalHodgeImage N.extension C hCt hP hD a ha hc hs := by
  apply twoFormHodgeDomain_of_distribution hRic
  intro v
  have hleft := heatNormalAmplitudeL2_pairing_normal N.frameData C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)
  have hright := heatNormalAmplitudeL2_pairing_normal N.frameData C hE hCt hP hD
    (heatNormalOperatorAmplitude N.extension a) (heatNormalOperatorAmplitude_regular N.extension a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOperatorAmplitude_support N.extension a))
    ((heatNormalOperatorAmplitude_support N.extension a).trans hs) (v : SmoothL2TwoForm o)
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (N.compact_green hRic a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single genuine normal chart and compact cutoff for the time-dependent
parametrix. Its existence simultaneously enforces the domain and residual bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.operatorColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalHodgeImage E P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalCutoffColumn E P.cutoff t l)
    (heatNormalCutoffColumn_regular_four E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

end
end PositiveEinsteinFour.Geometry
end


section

/-! One genuine chart and cutoff for the actual one-form weak heat equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneResidual (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  P.oneTimeColumn E t l + P.oneOperatorColumn E t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common normal ball and fixed bump define actual compact
parametrix data, with the actual Hodge generator identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonNormalMember.parametrixData_generator (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) (hRic : RicciThree g) (t : ℝ) (l : Fin 6) :
    ∃ hf : (N.parametrixData hr).column N.extension t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨(N.parametrixData hr).column N.extension t l, hf⟩ =
        (N.parametrixData hr).operatorColumn N.extension t l := by
  let P := N.parametrixData hr
  apply N.compact_hodge_domain hRic P.chart P.exponential P.in_chart P.point_regular P.inside_radius
    (heatNormalCutoffColumn N.extension P.cutoff t l)
    (heatNormalCutoffColumn_regular_four N.extension P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support N.extension P.cutoff t l))
    ((heatNormalCutoffColumn_support N.extension P.cutoff t l).trans P.cutoff_support)
  rw [← N.parametrixData_source hr]
  exact (heatNormalCutoffColumn_support N.extension P.cutoff t l).trans P.cutoff_support

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cancellation of the differentiated first coefficient leaves the
actual quadratic Weitzenbock trace in the second Euler coefficient. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerSecondAmplitude_center
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    E.eulerSecondAmplitude 0 =
      ((twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72) / 2 := by
  let α := -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0
  have hU : E.base.U 0 ≠ 0 := (E.base.U_pos 0).ne'
  have hscalar := fourHeatCoefficient_center 1 E.base.a E.base.b (fun _ => 0) E.base.U hU
  have hfirst₁ : (E.oneCompanion.amplitude 1 0).trace = 4 * α - 12 := by
    rw [E.oneCompanion.first_amplitude_center]
    rw [show E.oneCompanion.base = E.base from rfl]
    norm_num [Matrix.trace_sub, Matrix.trace_smul, α]
    ring
  have hsecond₁ := congrArg Matrix.trace E.oneCompanion.second_amplitude_center
  rw [show E.oneCompanion.base = E.base from rfl] at hsecond₁
  simp only [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_neg,
    Matrix.smul_mul, Matrix.one_mul, smul_eq_mul] at hsecond₁
  rw [hfirst₁] at hsecond₁
  have hsecond₂ := congrArg Matrix.trace (E.second_amplitude_center he)
  rw [E.first_amplitude_intrinsic_center he] at hsecond₂
  simp only [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_neg,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_eq_mul] at hsecond₂
  rw [actual_twoFormPotential_trace hRic e] at hsecond₂
  have hcancel := E.eulerFirst_scalar_operator_zero hRic
  change 2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 2 0 -
    2 * (E.oneCompanion.amplitude 2 0).trace + (E.amplitude 2 0).trace = _
  norm_num only [Nat.cast_one, one_add_one_eq_two] at hscalar
  dsimp only [α] at hfirst₁
  dsimp only [α] at hsecond₁
  linarith only [hscalar, hsecond₁, hsecond₂, hcancel]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each actual smooth one-form eigenmode obeys the forced heat equation
for the genuinely constructed normal parametrix. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneNormalizedResidual (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.oneResidual E t l

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual one-form heat residual is combined before taking its L2 norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneResidual_as_amplitude
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) :
    P.oneResidual E t l =
      heatNormalOneAmplitudeL2 D P.chart P.in_chart P.point_regular P.inside_radius
        (heatNormalOneResidualColumn E P.cutoff t l)
        (heatNormalOneResidualColumn_regular E P.cutoff P.cutoff_regular t l)
        (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
          (heatNormalOneResidualColumn_support E P.cutoff t l))
        ((heatNormalOneResidualColumn_support E P.cutoff t l).trans P.cutoff_support) := by
  exact (heatNormalOneAmplitudeL2_add P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalOneTimeColumn E P.cutoff t l)
    (heatNormalOneOperatorAmplitude E (heatNormalOneCutoffColumn E P.cutoff t l))
    (heatNormalOneTimeColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (heatNormalOneOperatorAmplitude_regular E _ (heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneTimeColumn_support E P.cutoff t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      ((heatNormalOneOperatorAmplitude_support E _).trans (heatNormalOneCutoffColumn_support E P.cutoff t l)))
    ((heatNormalOneTimeColumn_support E P.cutoff t l).trans P.cutoff_support)
    (((heatNormalOneOperatorAmplitude_support E _).trans
      (heatNormalOneCutoffColumn_support E P.cutoff t l)).trans P.cutoff_support)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The surviving center coefficient of the actual Euler Gram expansion
is the Euler curvature polynomial with its exact Gaussian normalization. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerAmplitude_zero (E : HeatNormalBundleExtension D)
    (x : FourSpace) : E.eulerAmplitude 0 x = E.base.U x • heatEulerUnit := by
  apply Prod.ext
  · change E.base.U x = E.base.U x * 1
    ring
  · apply Prod.ext
    · exact E.oneCompanion.amplitude_zero x
    · exact E.amplitude_zero x

theorem HeatNormalBundleExtension.eulerAmplitude_first_gram
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    heatEulerGram (E.eulerAmplitude 1 0) (E.eulerAmplitude 1 0) =
      (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72 := by
  let α := -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0
  have hscalar : fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1 0 = α := by
    have h := fourHeatCoefficient_center 0 E.base.a E.base.b (fun _ => 0) E.base.U
      (E.base.U_pos 0).ne'
    simpa only [Nat.cast_zero, zero_add, one_mul, fourHeatCoefficient] using h
  have heq : E.eulerAmplitude 1 0 =
      (α, α • (1 : Mat4) - (3 : ℝ) • 1,
        α • (1 : HeatMat6) - twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)) := by
    apply Prod.ext
    · exact hscalar
    · apply Prod.ext
      · exact E.oneCompanion.first_amplitude_center
      · exact E.first_amplitude_intrinsic_center he
  rw [heq]
  exact heatEulerGram_scalar_potential α _ (heat_actual_potential_symmetric e)
    (actual_twoFormPotential_trace hRic e)

theorem HeatNormalBundleExtension.eulerSecondWeight_center
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) (χ : FourSpace → ℝ) (hχ : χ 0 = 1) :
    E.eulerSecondWeight χ 0 / (64 * Real.pi ^ 2) =
      curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have htr : heatEulerTrace (E.eulerAmplitude 2 0) = E.eulerSecondAmplitude 0 := rfl
  rw [eulerSecondWeight, frameExponentialJacobian_zero, hχ, hU, htr,
    E.eulerSecondAmplitude_center hRic he, E.eulerAmplitude_first_gram hRic he]
  convert heatEuler_potential_density hRic e using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time L2 continuity of the actual normal parametrix and residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneResidual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ContinuousOn (fun t => P.oneResidual E t l) (Ioi 0) := by
  have heq : (fun t => P.oneResidual E t l) = (fun t => heatNormalOneAmplitudeL2 D P.chart P.in_chart P.point_regular P.inside_radius
      (heatNormalOneResidualColumn E P.cutoff t l)
      (heatNormalOneResidualColumn_regular E P.cutoff P.cutoff_regular t l)
      (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneResidualColumn_support E P.cutoff t l))
      ((heatNormalOneResidualColumn_support E P.cutoff t l).trans P.cutoff_support)) :=
    funext (fun t => P.oneResidual_as_amplitude E t l)
  rw [heq]
  apply heatNormalOneAmplitudeL2_continuous_family P.chart P.in_chart P.point_regular P.inside_radius
    (fun t => heatNormalOneResidualColumn E P.cutoff t l)
    (fun t => heatNormalOneResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (fun t => P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneResidualColumn_support E P.cutoff t l))
    (fun t => (heatNormalOneResidualColumn_support E P.cutoff t l).trans P.cutoff_support)
    ?_ (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
    (fun t _ => heatNormalOneResidualColumn_support E P.cutoff t l)
  exact (heatNormalOneResidualColumn_joint_continuousOn E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) l).mono (prod_mono Subset.rfl (subset_univ _))

variable [SecondCountableTopology M]

theorem HeatNormalParametrixData.oneNormalizedResidual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ContinuousOn (fun t => P.oneNormalizedResidual E t l) (Ioi 0) := by
  exact (P.oneResidual_continuous E l).const_smul ((normalizedChartFactor g).toReal)⁻¹

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Euler polynomial and its vanishing lower-order term. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerPolynomial_gram (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) :
    frameExponentialJacobian g o e x * χ x ^ 2 *
      heatEulerGram (E.eulerPolynomial t x) (E.eulerPolynomial t x) =
        2 * t * E.eulerFirst χ x + t ^ 2 * E.eulerTail χ t x := by
  rw [eulerPolynomial, E.eulerAmplitude_zero, heatEulerGram_polynomial]
  unfold eulerFirst eulerTail
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local Euler polynomial has the Euler curvature density
as its squared-Gaussian limit. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.euler_gaussian_limit
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * χ x ^ 2 *
        heatEulerGram (E.eulerPolynomial t x) (E.eulerPolynomial t x)))
      (𝓝[>] 0) (𝓝 (curvatureEulerDensity (twoFormMetricCurvatureTensor g e))) := by
  have hz := E.eulerFirst_zero_near hRic χ
  have hreg : ContDiffAt ℝ 2 (E.eulerFirst χ) 0 :=
    (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hz
  have hd : fderiv ℝ (E.eulerFirst χ) 0 = 0 := by
    rw [hz.fderiv_eq]
    exact fderiv_const_apply _
  have hdn : fderiv ℝ (E.eulerFirst χ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hz.eventuallyEq_nhds] with x hx
    rw [hx.fderiv_eq]
    exact fderiv_const_apply _
  have hdd : fderiv ℝ (fderiv ℝ (E.eulerFirst χ)) 0 = 0 := by
    rw [hdn.fderiv_eq]
    exact fderiv_const_apply _
  obtain ⟨C, hC⟩ := (E.eulerFirst_compact χ hc).exists_bound_of_continuous
    (E.eulerFirst_continuous χ hχ)
  obtain ⟨B, _, hB⟩ := E.eulerTail_bound χ hχ hc
  have h := fourHeat_signed_gaussian_limit (E.eulerFirst χ)
    (E.eulerFirst_continuous χ hχ) hreg hz.self_of_nhds hd C hC
    (E.eulerTail χ) (E.eulerTail_continuous χ hχ) B 1 zero_lt_one hB
  have hcenter : (1 / (64 * Real.pi ^ 2)) * E.eulerTail χ 0 0 =
      curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
    rw [E.eulerTail_zero]
    convert E.eulerSecondWeight_center hRic he χ hχ0 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  simp only [hdd, _root_.zero_apply, Finset.sum_const_zero, zero_add, hcenter] at h
  simpa only [E.eulerPolynomial_gram] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized residual has a continuous zero-time extension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneNormalizedResidualZero (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatResidualAtZero (fun s => P.oneNormalizedResidual E s l) t

theorem HeatNormalParametrixData.oneNormalizedResidual_bound (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) :
    ‖P.oneNormalizedResidual E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.oneResidual E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hB t ht l) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem HeatNormalParametrixData.oneNormalizedResidualZero_continuous
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t) (l : Fin 4) :
    ContinuousOn (fun t => P.oneNormalizedResidualZero E t l) (Icc 0 1) :=
  heatResidualAtZero_continuous _ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) 1
    zero_lt_one (P.oneNormalizedResidual_continuous E l)
    (fun t ht => P.oneNormalizedResidual_bound E B hB t ht l)

theorem HeatNormalParametrixData.oneNormalizedResidualZero_eq
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (t : ℝ) (ht : 0 < t) (l : Fin 4) :
    P.oneNormalizedResidualZero E t l = P.oneNormalizedResidual E t l := by
  unfold oneNormalizedResidualZero heatResidualAtZero
  exact Function.update_of_ne ht.ne' _ _

theorem HeatNormalParametrixData.oneNormalizedResidualZero_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (l : Fin 4) :
    ‖P.oneNormalizedResidualZero E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t :=
  heatResidualAtZero_norm _ _ 1 (fun s hs => P.oneNormalizedResidual_bound E B hB s hs l) t ht

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


