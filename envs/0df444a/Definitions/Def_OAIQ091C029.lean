-- Prove2me | Definitions.Def_OAIQ091C029
-- name    : OAIQ091C029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:31:45.717994+00:00
-- url     : https://prove2.me/theorems/0eebe422-8b6f-429b-991f-d4f2a174bc94
-- title:
--   Definitions bundle OAIQ091C029 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 25 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry12`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry12.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C023`, `OAIQ091C024`, `OAIQ091C043` and `OAIQ091C026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C031`, `OAIQ091C033`, `OAIQ091C045`, `OAIQ091C047`, `OAIQ091C048`, `OAIQ091C049`, `OAIQ091C050` and `OAIQ091C052`; the statements `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_norm` and `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_pairing`; the proofs of `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_norm` and `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_pairing`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C023
import Definitions.Def_OAIQ091C024
import Definitions.Def_OAIQ091C043
import Definitions.Def_OAIQ091C026

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual exponential is a local coordinate chart along every radial
geodesic strictly before its first conjugate point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

/-- A local exponential chart centered at any positive preconjugate time. -/
theorem frameExponential_preconjugate_localChart (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (htc : t < actualFirstConjugateTime g hRic e) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      t • coordinateVector 0 ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  let d := (parallelFrameFlowMap g 0 t e).base
  let x := t • coordinateVector 0
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hx : frameExponential g o e x = d := frameExponential_first_ray g o e he t ht
  let L := Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
      jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t))
  have hL : IsUnit L := frameExponential_preconjugate_isUnit g hRic d e t ht htc hd
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hxsrc : frameExponential g o e x ∈ (chartAt FourSpace d).source := hx ▸ hd
  have hcont := frameExponential_chart_contDiffAt g o d e x hxsrc
  have hder : HasFDerivAt (fun v => chartAt FourSpace d (frameExponential g o e v)) L x :=
    frameExponential_hasFDerivAt g o hRic d e he t ht hd
  have hf : HasStrictFDerivAt
      (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e v))
      (E : FourSpace →L[ℝ] FourSpace) x := by
    rw [hE]
    exact hcont.hasStrictFDerivAt' hder one_ne_zero
  let C := hf.toOpenPartialHomeomorph _
  let U := (frameExponential g o e) ⁻¹' (chartAt FourSpace d).source
  have hU : IsOpen U := (chartAt FourSpace d).open_source.preimage
    (frameExponential_continuous g o e)
  let D := (C.trans (chartAt FourSpace d).symm).restrOpen U hU
  refine ⟨D, ?_, ?_⟩
  · change x ∈ (C.trans (chartAt FourSpace d).symm).source ∩ U
    refine ⟨⟨hf.mem_toOpenPartialHomeomorph_source, ?_⟩, hxsrc⟩
    exact (chartAt FourSpace d).map_source hxsrc
  · intro v hv
    change (chartAt FourSpace d).symm
      (chartAt FourSpace d (frameExponential g o e v)) = frameExponential g o e v
    exact (chartAt FourSpace d).left_inv hv.2

end
end PositiveEinsteinFour.Geometry
end


section

/-! The open polar parameter domain before the first conjugate point, and
actual local exponential charts in all of its directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_polar_localChart (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : Directions) (t : ℝ)
    (hp : (q, t) ∈ framePolarDomain g hRic e) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      t • q.val ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hf : e.rotate (orientedToOrthogonal Q) ∈ o.positive :=
    frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  obtain ⟨C, hx, hC⟩ := frameExponential_preconjugate_localChart g o hRic
    (e.rotate (orientedToOrthogonal Q)) hf t hp.1 hp.2
  let D := L.symm.toHomeomorph.toOpenPartialHomeomorph.trans C
  have hinv : L.symm (t • q.val) = t • coordinateVector 0 := by
    rw [← hfirst, map_smul, L.symm_apply_apply]
  refine ⟨D, ?_, ?_⟩
  · change t • q.val ∈ Set.univ ∩ L.symm ⁻¹' C.source
    refine ⟨Set.mem_univ _, ?_⟩
    change L.symm (t • q.val) ∈ C.source
    rw [hinv]
    exact hx
  · intro v hv
    change C (L.symm v) = frameExponential g o e v
    have h := hC hv.2
    change C (L.symm v) = frameExponential g o (e.rotate (orientedToOrthogonal Q)) (L.symm v) at h
    rw [frameExponential_rotate g o e Q] at h
    change C (L.symm v) = frameExponential g o e (L (L.symm v)) at h
    rwa [L.apply_symm_apply] at h

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

/-! Four-component cutoff commutator for the actual one-form heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology
noncomputable section

theorem fourHeatOneScaledCommutator_continuous (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) (k : Fin 4) :
    Continuous (fun z : ℝ × FourSpace => fourHeatOneScaledCommutator a b B χ u z.1 z.2 k) := by
  have hL : Continuous (fun x => fourHeatLocalOperator (a x) (b x) 0 χ x) :=
    (fourHeatLocalOperator_contDiff 0 a b (fun _ => 0) χ
      (fun i j => contDiff_zero.mpr (ha i j)) (fun i => contDiff_zero.mpr (hb i))
      contDiff_const hχ).continuous
  have hP (q : Fin 4) : Continuous (fun z : ℝ × FourSpace =>
      fourHeatOnePolynomial u z.1 z.2 q) :=
    fourHeatPolynomial_joint_continuous _ (fun m => (hu m q).continuous)
  have hD (q : Fin 4) (j : Fin 4) : Continuous (fun z : ℝ × FourSpace =>
      partialDeriv (fun y => fourHeatOnePolynomial u z.1 y q) j z.2) :=
    fourHeatPolynomial_partial_joint_continuous _
      (fun m => (hu m q).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × FourSpace => partialDeriv χ i z.2) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp continuous_snd
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × FourSpace => a z.2 i j) :=
    (ha i j).comp continuous_snd
  have hBB (i : Fin 4) (q : Fin 4) : Continuous (fun z : ℝ × FourSpace => B z.2 i k q) :=
    (hB i k q).comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × FourSpace => z.2 j) :=
    (EuclideanSpace.proj j).continuous.comp continuous_snd
  exact ((continuous_fst.mul (hL.comp continuous_snd)).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hBB i q).mul (hχi i)).mul (hP q)))))

theorem fourHeatOneScaledCommutator_bounded (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q)) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k,
      |fourHeatOneScaledCommutator a b B χ u t x k| ≤ C := by
  let S := fun z : ℝ × FourSpace => ∑ k : Fin 4,
    |fourHeatOneScaledCommutator a b B χ u z.1 z.2 k|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    (fourHeatOneScaledCommutator_continuous a b B χ u ha hb hB hχ hu k).abs)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hχc).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ tsupport χ
  · have hle : |fourHeatOneScaledCommutator a b B χ u t x k| ≤ S (t, x) :=
      Finset.single_le_sum (fun q _ => abs_nonneg
        (fourHeatOneScaledCommutator a b B χ u t x q)) (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx⟩)).trans (le_max_left _ _))
  · have hz := fourHeatOneScaledCommutator_zero_of_locally_const a b B χ u t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem fourHeatOneScaledCommutator_gaussian_bound (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (ha : ∀ i j, Continuous (fun x => a x i j))
    (hb : ∀ i, Continuous (fun x => b x i))
    (hB : ∀ i k q, Continuous (fun x => B x i k q))
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun x => u m x q))
    (r : ℝ) (hr : 0 < r) (hinner : ∀ x ∈ ball 0 r, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k,
      |(fourHeatGaussian t x / t) * fourHeatOneScaledCommutator a b B χ u t x k| ≤ C * t := by
  obtain ⟨C, hC, hbound⟩ := fourHeatOneScaledCommutator_bounded a b B χ u ha hb hB hχ hχc hu
  refine ⟨C * (384 / (Real.pi ^ 2 * r ^ 8)), by positivity, ?_⟩
  intro t ht x k
  by_cases hx : x ∈ ball 0 r
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    rw [fourHeatOneScaledCommutator_zero_of_locally_const a b B χ u t x 1 he k,
      mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hrx : r ≤ ‖x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩ x k)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * r ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time r t hr ht.1 x hrx) hC
      _ = _ := by ring
end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness bounds the one-form cutoff commutator over the common frame family. The Gaussian restores the small-time factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatFamilyOneCommutator_continuous (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (k l : Fin 4) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyOneCommutator E χ z.1 z.2 k l) := by
  have hP (q : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatOnePolynomial (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 z.2.1 q) :=
    heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) q l).continuous)
  have hD (q : Fin 4) (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fun y => fourHeatOnePolynomial
        (fun m x a => E.amplitude m (x, z.2.2) a l) z.1 y q) j z.2.1) :=
    heatFamilyPolynomial_partial_continuous _
      (fun m => (E.amplitude_regular m (by omega) q l).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => partialDeriv χ i z.2.1) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp (continuous_fst.comp continuous_snd)
  have hχij (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (partialDeriv χ i) j z.2.1) :=
    ((fourHeat_partial_contDiff 0 _ (fourHeat_partial_contDiff 1 χ hχ i) j).continuous).comp
      (continuous_fst.comp continuous_snd)
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.base.a z.2 i j) :=
    (E.base.a_regular i j).continuous.comp continuous_snd
  have hb (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.base.b z.2 i) :=
    (E.base.b_regular i).continuous.comp continuous_snd
  have hB (i : Fin 4) (q : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.B z.2 i k q) :=
    (E.B_regular i k q).continuous.comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2.1 j) :=
    (EuclideanSpace.proj j).continuous.comp (continuous_fst.comp continuous_snd)
  have hL : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatLocalOperator (E.base.a z.2) (E.base.b z.2) 0 χ z.2.1) := by
    have hn : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
        -(∑ i : Fin 4, ∑ j : Fin 4, E.base.a z.2 i j *
          partialDeriv (partialDeriv χ i) j z.2.1) +
        ∑ i : Fin 4, E.base.b z.2 i * partialDeriv χ i z.2.1) :=
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hA i j).mul (hχij i j)))).neg.add
          (continuous_finsetSum _ (fun i _ => (hb i).mul (hχi i)))
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [fourHeatLocalOperator, zero_mul, add_zero]
  exact ((continuous_fst.mul hL).mul (hP k)).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD k j)).sub (((hx j).div_const 2).mul (hP k))))))) |>.add
    (continuous_fst.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun q _ => ((hB i q).mul (hχi i)).mul (hP q)))))

theorem heatFamilyOneCommutator_bounded (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x k l,
      |heatFamilyOneCommutator E χ t (x, q) k l| ≤ C := by
  let S := fun z : ℝ × HeatRadialFrameSpace => ∑ k : Fin 4, ∑ l : Fin 4,
    |heatFamilyOneCommutator E χ z.1 z.2 k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (heatFamilyOneCommutator_continuous E χ hχ k l).abs))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ tsupport χ
  · have hle : |heatFamilyOneCommutator E χ t (x, q) k l| ≤ S (t, (x, q)) := by
      apply (Finset.single_le_sum (fun a _ => abs_nonneg
        (heatFamilyOneCommutator E χ t (x, q) k a)) (Finset.mem_univ l)).trans
      exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg (heatFamilyOneCommutator E χ t (x, q) a b)))
        (Finset.mem_univ k)
    exact hle.trans ((hC (mem_image_of_mem S ⟨ht, hx, hq⟩)).trans (le_max_left _ _))
  · have hz := fourHeatOneScaledCommutator_zero_of_locally_const
      (fun x => E.base.a (x, q)) (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) k
    change |fourHeatOneScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem heatFamilyOneCommutator_gaussian_bound (E : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
      |(fourHeatGaussian t x / t) * heatFamilyOneCommutator E χ t (x, q) k l| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := heatFamilyOneCommutator_bounded E χ hχ hc K hK
  refine ⟨C * (384 / (Real.pi ^ 2 * s ^ 8)), by positivity, ?_⟩
  intro q hq t ht x k l
  by_cases hx : x ∈ ball 0 s
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    have hz := fourHeatOneScaledCommutator_zero_of_locally_const
      (fun x => E.base.a (x, q)) (fun x => E.base.b (x, q)) (fun x => E.B (x, q)) χ
      (fun m x a => E.amplitude m (x, q) a l) t x 1 he k
    change |(fourHeatGaussian t x / t) * fourHeatOneScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hsx : s ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hb q hq t ⟨ht.1.le, ht.2⟩ x k l)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * s ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time s t hs ht.1 x hsx) hC
      _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar cutoff commutator has one bound over a compact frame family. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatFamilyScalarCommutator_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyScalarCommutator E χ z.1 z.2) := by
  simp only [heatFamilyScalarCommutator, fourHeatScaledCommutator, Pi.zero_apply,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  have hP : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatPolynomial (fun m x => E.scalarAmplitude m (x, z.2.2)) z.1 z.2.1) :=
    heatFamilyPolynomial_continuous _ (fun m => (E.scalarAmplitude_regular m (by omega)).continuous)
  have hD (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (fun y => fourHeatPolynomial
        (fun m x => E.scalarAmplitude m (x, z.2.2)) z.1 y) j z.2.1) :=
    heatFamilyPolynomial_partial_continuous _
      (fun m => (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) j
  have hχi (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => partialDeriv χ i z.2.1) :=
    ((fourHeat_partial_contDiff 1 χ hχ i).continuous).comp (continuous_fst.comp continuous_snd)
  have hχij (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      partialDeriv (partialDeriv χ i) j z.2.1) :=
    ((fourHeat_partial_contDiff 0 _ (fourHeat_partial_contDiff 1 χ hχ i) j).continuous).comp
      (continuous_fst.comp continuous_snd)
  have hA (i j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.a z.2 i j) :=
    (E.a_regular i j).continuous.comp continuous_snd
  have hb (i : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => E.b z.2 i) :=
    (E.b_regular i).continuous.comp continuous_snd
  have hx (j : Fin 4) : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2.1 j) :=
    (EuclideanSpace.proj j).continuous.comp (continuous_fst.comp continuous_snd)
  have hL : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      fourHeatLocalOperator (E.a z.2) (E.b z.2) 0 χ z.2.1) := by
    have hn : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
        -(∑ i : Fin 4, ∑ j : Fin 4, E.a z.2 i j *
          partialDeriv (partialDeriv χ i) j z.2.1) +
        ∑ i : Fin 4, E.b z.2 i * partialDeriv χ i z.2.1) :=
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
        (fun j _ => (hA i j).mul (hχij i j)))).neg.add
          (continuous_finsetSum _ (fun i _ => (hb i).mul (hχi i)))
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [fourHeatLocalOperator, zero_mul, add_zero]
  exact ((continuous_fst.mul hL).mul hP).sub
    (continuous_const.mul (continuous_finsetSum _ (fun i _ => continuous_finsetSum _
      (fun j _ => ((hA i j).mul (hχi i)).mul
        ((continuous_fst.mul (hD j)).sub (((hx j).div_const 2).mul hP))))))

theorem heatFamilyScalarCommutator_bounded (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      |heatFamilyScalarCommutator E χ t (x, q)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image
    (heatFamilyScalarCommutator_continuous E χ hχ).abs.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hC ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun _ => 0) χ
      (fun m x _ => E.scalarAmplitude m (x, q)) t x 0
      (notMem_tsupport_iff_eventuallyEq.mp hx) 0
    change |fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem heatFamilyScalarCommutator_gaussian_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1) :
    ∃ C ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
      |(fourHeatGaussian t x / t) * heatFamilyScalarCommutator E χ t (x, q)| ≤ C * t := by
  obtain ⟨C, hC, hb⟩ := heatFamilyScalarCommutator_bounded E χ hχ hc K hK
  refine ⟨C * (384 / (Real.pi ^ 2 * s ^ 8)), by positivity, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ ball 0 s
  · have he : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hinner y hy
    have hz := fourHeatScaledCommutator_zero_of_locally_const
      (fun x => E.a (x, q)) (fun x => E.b (x, q)) (fun _ => 0) χ
      (fun m x _ => E.scalarAmplitude m (x, q)) t x 1 he 0
    change |(fourHeatGaussian t x / t) * fourHeatScaledCommutator _ _ _ _ _ _ _ _| ≤ _
    rw [hz, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (by positivity)) ht.1.le
  · have hsx : s ≤ ‖x‖ := by simpa only [mem_ball_zero_iff, not_lt] using hx
    rw [abs_mul, abs_of_pos (div_pos (fourHeatGaussian_pos t ht.1 x) ht.1)]
    calc
      _ ≤ (fourHeatGaussian t x / t) * C :=
        mul_le_mul_of_nonneg_left (hb q hq t ⟨ht.1.le, ht.2⟩ x)
          (div_nonneg (fourHeatGaussian_pos t ht.1 x).le ht.1.le)
      _ ≤ ((384 / (Real.pi ^ 2 * s ^ 8)) * t) * C :=
        mul_le_mul_of_nonneg_right (fourHeatGaussian_away_inverse_time s t hs ht.1 x hsx) hC
      _ = _ := by ring

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

/-! The time derivative and exact cutoff residual of the actual normal
bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_residual_identity {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (hχ : ContDiffAt ℝ 2 χ x) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (ha : ∀ i j, a i j = a j i) (k l : Fin 4) :
    deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
      fourHeatOneOperator a b B C
        (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k =
    χ x * (deriv (fun s => heatNormalOneParametrix E s x k l) t +
      fourHeatOneOperator a b B C
        (fun y q => heatNormalOneParametrix E t y q l) x k) +
      fourHeatLocalOperator a b 0 χ x * heatNormalOneParametrix E t x k l -
      2 * (∑ i, ∑ j, a i j * partialDeriv χ i x *
        partialDeriv (fun y => heatNormalOneParametrix E t y k l) j x) +
      ∑ i, ∑ q, B i k q * partialDeriv χ i x * heatNormalOneParametrix E t x q l := by
  have hd := (heatNormalOneParametrix_time_differentiable E t ht x k l).hasDerivAt.const_mul
    (χ x)
  change HasDerivAt (fun s => heatNormalOneCutoffParametrix E χ s x k l) _ t at hd
  rw [hd.deriv]
  unfold heatNormalOneCutoffParametrix
  rw [fourHeatOneOperator_cutoff a b B C χ _ x ha hχ
    (fun q => ((heatNormalOneParametrix_space_regular E t q l).of_le (by norm_num)).contDiffAt) k]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Both terms of the cutoff heat residual vanish outside the spatial
support of the actual cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_residual_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace)
    (hx : x ∉ tsupport χ) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (k l : Fin 4) :
    deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
      fourHeatOneOperator a b B C
        (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k = 0 := by
  have hχ : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  have htime : (fun s => heatNormalOneCutoffParametrix E χ s x k l) = fun _ => (0 : ℝ) := by
    funext s
    simp only [heatNormalOneCutoffParametrix, hχ.self_of_nhds, zero_mul]
  have hspace (q : Fin 4) :
      (fun y => heatNormalOneCutoffParametrix E χ t y q l) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hχ] with y hy
    simp only [heatNormalOneCutoffParametrix, hy, zero_mul]
  rw [htime, deriv_const, fourHeatOneOperator_zero_of_locally_zero a b B C hspace k,
    zero_add]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Constant-curvature Jacobi fields for the round branch of model
identification. All coefficients are the actual metric curvature. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.L2Operator
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actualJacobiCurvature_eq_one_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (s : ℝ) :
    actualJacobiCurvature g e s = 1 := by
  let f := parallelFrameFlowMap g 0 s e
  have hf : f ∈ o.positive := (canonicalParallelMetricData_orientation o hRic 0 s e).mpr he
  have hP : plusWeyl g f.base f.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_plusNorm_frame o f hf]
    exact (plusNorm_eq_zero_iff o f.base).mpr (hplus f.base)
  have hM : minusWeyl g f.base f.frame = 0 := by
    apply (normalizedBlockNorm_eq_zero_iff _).mp
    rw [← actual_minusNorm_frame o f hf]
    exact (minusNorm_eq_zero_iff o f.base).mpr (hminus f.base)
  change 1 + normalCurvatureDeviation g f.base f.frame firstDirection = 1
  rw [normalCurvatureDeviation_eq_of_decomposition g f.base f.frame
    (actual_einstein_decomposition f.frame hRic), hP, hM]
  simp [normalDeviation, rotated]

theorem actualJacobi_eq_sine_of_weyl_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    (actualJacobiSolution g hRic e).J t = Real.sin t • (1 : NormalMatrix) ∧
      (actualJacobiSolution g hRic e).V t = Real.cos t • (1 : NormalMatrix) :=
  (actualJacobiSolution g hRic e).eq_sine_of_curvature_one
    (actualJacobiCurvature_eq_one_of_weyl_zero hRic hplus hminus e he) t

end
end PositiveEinsteinFour.Geometry
end


section

/-! At time pi the round exponential has zero derivative in every
angular direction, including after changing the initial direction. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Jacobi Angular
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem frameExponential_pi_first_tangent_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (c : M)
    (hc : (parallelFrameFlowMap g 0 Real.pi e).base ∈ (chartAt FourSpace c).source)
    (w : FourSpace) (hw : w 0 = 0) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v))
      (Real.pi • coordinateVector 0) w = 0 := by
  rw [(frameExponential_hasFDerivAt g o hRic c e he Real.pi Real.pi_pos hc).fderiv,
    (actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he Real.pi).1,
    Real.sin_pi, zero_smul, smul_zero]
  change WithLp.toLp 2 ((frameChartMatrix g c (parallelFrameFlowMap g 0 Real.pi e) *
    jacobiBlockMatrix 1 0) *ᵥ WithLp.ofLp w) = 0
  rw [← Matrix.mulVec_mulVec]
  have hz : jacobiBlockMatrix 1 (0 : NormalMatrix) *ᵥ WithLp.ofLp w = 0 := by
    rw [jacobiBlockMatrix_mulVec]
    ext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [hw]
  rw [hz, Matrix.mulVec_zero, WithLp.toLp_zero]

theorem frameExponential_pi_angular_derivative_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (c : M)
    (hc : frameExponential g o e (Real.pi • q.val) ∈ (chartAt FourSpace c).source)
    (w : FourSpace) (hw : inner ℝ q.val w = 0) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v))
      (Real.pi • q.val) w = 0 := by
  let Q := directionOrientedMatrix q
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let f := e.rotate (orientedToOrthogonal Q)
  let F := fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)
  let G := fun v : FourSpace => chartAt FourSpace c (frameExponential g o f v)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hLfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have hLpoint : L (Real.pi • coordinateVector 0) = Real.pi • q.val := by
    rw [map_smul, hLfirst]
  have hp : frameExponential g o e (Real.pi • q.val) =
      (parallelFrameFlowMap g 0 Real.pi f).base :=
    frameExponential_direction_ray g o e he q Real.pi
  have hfc : (parallelFrameFlowMap g 0 Real.pi f).base ∈ (chartAt FourSpace c).source := hp ▸ hc
  have hF := (frameExponential_chart_contDiffAt g o c e (Real.pi • q.val) hc).differentiableAt
    one_ne_zero
  rw [← hLpoint] at hF
  have hcomp := hF.hasFDerivAt.comp (Real.pi • coordinateVector 0)
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have heq : (fun v : FourSpace => F (L v)) = G := by
    funext v
    exact congrArg (chartAt FourSpace c) (frameExponential_rotate g o e Q v).symm
  change HasFDerivAt (fun v => F (L v))
    ((fderiv ℝ F (L (Real.pi • coordinateVector 0))).comp
      (L : FourSpace →L[ℝ] FourSpace)) (Real.pi • coordinateVector 0) at hcomp
  rw [heq, hLpoint] at hcomp
  have hfirst : (L.symm w) 0 = 0 := by
    have hinner := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property).inner_map_map (coordinateVector 0) (L.symm w)
    change inner ℝ (L (coordinateVector 0)) (L (L.symm w)) =
      inner ℝ (coordinateVector 0) (L.symm w) at hinner
    rw [hLfirst, L.apply_symm_apply, hw] at hinner
    simpa [PiLp.inner_apply, coordinateVector] using hinner.symm
  have hz := frameExponential_pi_first_tangent_zero hRic hplus hminus f hf c hfc
    (L.symm w) hfirst
  change fderiv ℝ G (Real.pi • coordinateVector 0) (L.symm w) = 0 at hz
  rw [hcomp.fderiv] at hz
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    L.apply_symm_apply] using hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual minimizing-domain integral retains the cut radius exactly
in the constant-curvature branch. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem round_actual_cut_mass (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) :
    (∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g e then
        ENNReal.ofReal |((actualJacobiSolution g hRic e).J r.val).det| else 0)
      ∂((volume : Measure ℝ).comap Subtype.val)) = roundRadialMass (actualCutTime g e) := by
  let F : ℝ → ℝ≥0∞ := fun r => if r ≤ actualCutTime g e then
    ENNReal.ofReal |((actualJacobiSolution g hRic e).J r).det| else 0
  change (∫⁻ r : Ioi (0 : ℝ), F r.val
    ∂((volume : Measure ℝ).comap Subtype.val)) = _
  rw [lintegral_subtype_comap measurableSet_Ioi F,
    ← lintegral_indicator measurableSet_Ioi]
  rw [roundRadialMass, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro r
  dsimp only [F]
  by_cases hr : 0 < r
  · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr)]
    by_cases hc : r ≤ actualCutTime g e
    · rw [ite_eq_left hc, Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) (actualCutTime g e) from ⟨hr, hc⟩),
        (actualJacobi_eq_sine_of_weyl_zero hRic hplus hminus e he r).1,
        Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
        abs_of_nonneg (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.le
          (hc.trans (actualCutTime_le_pi g hRic e))) 3)]
    · rw [ite_eq_right hc, Set.indicator_of_notMem (fun h => hc h.2)]
  · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr), Set.indicator_of_notMem (fun h => hr h.1)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The curvature operator is at most three on self-dual forms when the
remaining Weyl block is bounded above by two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian
open scoped BigOperators
noncomputable section

theorem halfFlat_curvature_matrix_bound (T : Mat)
    (hT : ((2 : ℝ) • (1 : Mat) - T).PosSemidef)
    (a : TwoFormFour) (ha : twoFormHodge a = a) :
    inner ℝ a (twoFormMatrixMul (twoFormCurvatureMatrix (fun v =>
      einsteinCurvatureTensor T 0 (v 0) (v 1) (v 2) (v 3))) a) ≤
        3 * inner ℝ a a := by
  rw [halfFlat_curvature_matrix_positive T a ha]
  have h3 : a 3 = a 2 := congrArg (fun v : TwoFormFour => v 2) ha
  have h4 : a 4 = -a 1 := by
    have h := congrArg (fun v : TwoFormFour => v 1) ha
    change -a 4 = a 1 at h
    linarith
  have h5 : a 5 = a 0 := congrArg (fun v : TwoFormFour => v 0) ha
  have h := hT.dotProduct_mulVec_nonneg ![a 0,a 1,a 2]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, star_trivial] at h
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp [Fin.sum_univ_succ, h3, h4, h5, Matrix.mulVec, dotProduct,
    Matrix.add_apply, Matrix.one_apply]
  nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vanishing angular derivatives imply that every radial geodesic in the
round branch reaches the same point at time pi. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundBoundaryEndpoint_chart_derivative_zero (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) (hv : v ≠ 0) (c : M)
    (hc : roundBoundaryEndpoint g o e v ∈ (chartAt FourSpace c).source) :
    HasFDerivAt (fun z => chartAt FourSpace c (roundBoundaryEndpoint g o e z))
      (0 : FourSpace →L[ℝ] FourSpace) v := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hq : roundBoundaryProjection v = Real.pi • q.val := rfl
  have hF := (frameExponential_chart_contDiffAt g o c e (roundBoundaryProjection v) hc).differentiableAt
    one_ne_zero
  have hcomp := hF.hasFDerivAt.comp v (roundBoundaryProjection_differentiableAt v hv).hasFDerivAt
  have hzero : (fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (roundBoundaryProjection v)).comp (fderiv ℝ roundBoundaryProjection v) = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    change fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z))
      (roundBoundaryProjection v) (fderiv ℝ roundBoundaryProjection v w) = 0
    rw [hq]
    apply frameExponential_pi_angular_derivative_zero hRic hplus hminus e he q c
      (by rwa [← hq])
    exact roundBoundaryProjection_derivative_tangent v hv w
  rw [hzero] at hcomp
  exact hcomp

theorem frameExponential_pi_independent_direction (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (q p : Directions) :
    frameExponential g o e (Real.pi • q.val) =
      frameExponential g o e (Real.pi • p.val) := by
  let U : Set FourSpace := {0}ᶜ
  have hPr : ContinuousOn roundBoundaryProjection U :=
    fun v hv => (roundBoundaryProjection_differentiableAt v hv).continuousAt.continuousWithinAt
  have hF : ContinuousOn (roundBoundaryEndpoint g o e) U :=
    (frameExponential_continuous g o e).comp_continuousOn hPr
  have hLC := zero_chart_derivative_locally_constant (roundBoundaryEndpoint g o e) U
    isOpen_compl_singleton hF
    (fun v hv c hc => roundBoundaryEndpoint_chart_derivative_zero hRic hplus hminus e he v hv c hc)
  have hrank : 1 < Module.rank ℝ FourSpace := by
    rw [← Module.finrank_eq_rank]
    norm_num [FourSpace]
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (isConnected_compl_singleton_of_one_lt_rank hrank (0 : FourSpace)).isPreconnected
  have hq : q.val ≠ 0 := by
    intro hz
    have h := q.property
    rw [hz, norm_zero] at h
    norm_num at h
  have hp : p.val ≠ 0 := by
    intro hz
    have h := p.property
    rw [hz, norm_zero] at h
    norm_num at h
  have h := hLC.apply_eq_of_preconnectedSpace ⟨q.val, hq⟩ ⟨p.val, hp⟩
  simpa only [roundBoundaryEndpoint, roundBoundaryProjection, q.property, p.property,
    inv_one, one_smul] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! In the unit-Weyl branch, actual self-dual harmonic forms are parallel.
The conclusion is derived from the global Bochner identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Matrix TraceHessian MeasureTheory
open scoped BigOperators Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance parallelHarmonicAddGroup_r8e3951_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
theorem halfFlat_unit_curvature_bound (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hnorm : ∀ x, plusNorm o x = 1) (x : M)
    (a : TwoFormFour) (ha : twoFormHodge a = a) :
    inner ℝ a (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩) a) ≤
      3 * inner ℝ a a := by
  let e : FrameBundle g := ⟨x,o.frame x⟩
  have hlast : ∀ i j k l, twoFormMetricCurvatureTensor g e ![i,j,l,k] =
      -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have heq : twoFormMetricCurvatureTensor g e = fun v =>
      einsteinCurvatureTensor (plusWeyl g x (o.frame x)) 0 (v 0) (v 1) (v 2) (v 3) := by
    funext v
    have hv : v = ![v 0,v 1,v 2,v 3] := by ext i; fin_cases i <;> rfl
    rw [hv]
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    rw [actual_einstein_decomposition e.frame hRic]
    rw [show minusWeyl g e.base e.frame = 0 from hminus x]
    rfl
  rw [← twoFormCurvatureMatrix_apply _ hlast, heq]
  exact halfFlat_curvature_matrix_bound _
    (unitWeyl_upper_posSemidef _ (actual_weyl_symmetric (o.frame x)).1
      (actual_unit_weyl_polynomial hRic hnorm e (o.frame_positive x))) a ha

end
end PositiveEinsteinFour.Geometry
end


section

/-! The round-sphere covering map, with its polar values
and surjectivity supplied by global exponential coverage. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped BigOperators Manifold ContDiff _root_.Topology
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_polar (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) (q : Directions) :
    roundSphereMap g o e (roundPolarPoint t q) = frameExponential g o e (t • q.val) := by
  unfold roundSphereMap
  by_cases h0 : t = 0
  · subst t
    rw [roundLog_polar_zero, zero_smul]
  by_cases hπ : t = Real.pi
  · subst t
    rw [roundLog_polar_pi]
    exact frameExponential_pi_independent_direction hRic hplus hminus e he firstDirection q
  · rw [roundLog_polar_interior t ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 hπ⟩]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Endpoint distance estimates for the actual sphere map. These also
control its continuity at both polar-coordinate singularities. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Set
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_distance_south (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) (p : RoundSphere4) :
    metricEDistance g (roundAntipodalPoint g o e) (roundSphereMap g o e p) ≤
      ENNReal.ofReal (Real.pi - Real.arccos (p.val 0)) := by
  obtain ⟨t, ht, q, rfl⟩ := exists_roundPolarPoint p
  rw [roundSphereMap_polar hRic hplus hminus e he t ht q, roundPolarPoint_first,
    Real.arccos_cos ht.1 ht.2]
  have hA : roundAntipodalPoint g o e = frameExponential g o e (Real.pi • q.val) :=
    frameExponential_pi_independent_direction hRic hplus hminus e he firstDirection q
  rw [hA, frameExponential_direction_ray g o e he q Real.pi,
    frameExponential_direction_ray g o e he q t]
  have hd := frameGeodesic_distance_le g 0
    (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) Real.pi t
  simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The sphere map is continuous at both poles as well as in the ordinary
polar chart; the south-pole bound uses the proved common endpoint. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Bundle Set Filter
open scoped Manifold ContDiff _root_.Topology ENNReal
noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem roundSphereMap_continuous (hRic : RicciThree g)
    (hplus : ∀ c, plusWeyl g c (o.frame c) = 0)
    (hminus : ∀ c, minusWeyl g c (o.frame c) = 0)
    (e : FrameBundle g) (he : e ∈ o.positive) : Continuous (roundSphereMap g o e) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : roundTail p = 0
  · rcases roundTail_zero_cases p hp with rfl | rfl
    · apply (tendsto_iff_edist_tendsto_0).mpr
      have hb : Tendsto (fun q : RoundSphere4 => ENNReal.ofReal (Real.arccos (q.val 0)))
          (𝓝 roundNorth) (𝓝 0) := by
        have hc : Continuous (fun q : RoundSphere4 =>
            ENNReal.ofReal (Real.arccos (q.val 0))) :=
          ENNReal.continuous_ofReal.comp roundPolarAngle_continuous
        simpa [roundNorth] using hc.tendsto roundNorth
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun _ => bot_le) (fun q => ?_)
      rw [roundSphereMap_north, edist_comm]
      exact roundSphereMap_distance_north e q
    · apply (tendsto_iff_edist_tendsto_0).mpr
      have hb : Tendsto (fun q : RoundSphere4 =>
          ENNReal.ofReal (Real.pi - Real.arccos (q.val 0)))
          (𝓝 (antipode roundNorth)) (𝓝 0) := by
        have hc : Continuous (fun q : RoundSphere4 =>
            ENNReal.ofReal (Real.pi - Real.arccos (q.val 0))) :=
          ENNReal.continuous_ofReal.comp (continuous_const.sub roundPolarAngle_continuous)
        simpa [roundNorth, antipode] using hc.tendsto (antipode roundNorth)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun _ => bot_le) (fun q => ?_)
      rw [roundSphereMap_south, edist_comm]
      exact roundSphereMap_distance_south hRic hplus hminus e he q
  · exact (frameExponential_continuous g o e).continuousAt.comp (roundLog_continuousAt hp)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


