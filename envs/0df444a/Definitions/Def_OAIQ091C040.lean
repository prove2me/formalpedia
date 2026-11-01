-- Prove2me | Definitions.Def_OAIQ091C040
-- name    : OAIQ091C040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:06:42.131869+00:00
-- url     : https://prove2.me/theorems/0436b5bb-f77a-4dca-a7a4-e15b0ece7728
-- title:
--   Definitions bundle OAIQ091C040 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 351 declarations of OpenAI's Lean: 95 definitions and 256 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.besselJetLinear`, `OAI.PositiveEinsteinFour.Geometry.integerDensityCutoffL2`, `OAI.PositiveEinsteinFour.Geometry.jetL2`, `OAI.PositiveEinsteinFour.Geometry.jetUniformLinear`, `OAI.PositiveEinsteinFour.Geometry.l4JetBound`, `OAI.PositiveEinsteinFour.Geometry.l4JetL2`, `OAI.PositiveEinsteinFour.Geometry.l4NextJetL2`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselJetL2`, `OAI.PositiveEinsteinFour.Geometry.scalarBesselJetUniform`, `OAI.PositiveEinsteinFour.Geometry.scalarBorelLp`, `OAI.PositiveEinsteinFour.Geometry.scalarBorelLpEquiv`, `OAI.PositiveEinsteinFour.Geometry.scalarBorelLpEquivAux`, `OAI.PositiveEinsteinFour.Geometry.scalarChartCutoff`, `OAI.PositiveEinsteinFour.Geometry.scalarChartDrift`, `OAI.PositiveEinsteinFour.Geometry.scalarChartOperator`, `OAI.PositiveEinsteinFour.Geometry.scalarChartReconstructionFun`, `OAI.PositiveEinsteinFour.Geometry.scalarChartSupport`, `OAI.PositiveEinsteinFour.Geometry.scalarCoefficientBump`, `OAI.PositiveEinsteinFour.Geometry.scalarComplexL2`, `OAI.PositiveEinsteinFour.Geometry.scalarCutoffChartC1`, `OAI.PositiveEinsteinFour.Geometry.scalarCutoffDrift`, `OAI.PositiveEinsteinFour.Geometry.scalarCutoffPrincipal`, `OAI.PositiveEinsteinFour.Geometry.scalarCutoffSchwartz`, `OAI.PositiveEinsteinFour.Geometry.scalarFrozenDrift`, `OAI.PositiveEinsteinFour.Geometry.scalarGradientCoordinateL2`, `OAI.PositiveEinsteinFour.Geometry.scalarLocalL2Product`, `OAI.PositiveEinsteinFour.Geometry.scalarLocalL2ProductCLM`, `OAI.PositiveEinsteinFour.Geometry.scalarLocalL2ProductLinear`, `OAI.PositiveEinsteinFour.Geometry.scalarPartialMatrix`, `OAI.PositiveEinsteinFour.Geometry.scalarPartialVector`, `OAI.PositiveEinsteinFour.Geometry.scalarPartitionFunction`, `OAI.PositiveEinsteinFour.Geometry.scalarPrincipalContraction`, `OAI.PositiveEinsteinFour.Geometry.scalarRealSchwartzJet`, `OAI.PositiveEinsteinFour.Geometry.scalarRescaledDrift`, `OAI.PositiveEinsteinFour.Geometry.scalarRescaledOperator`, `OAI.PositiveEinsteinFour.Geometry.scalarRescaledPoint`, `OAI.PositiveEinsteinFour.Geometry.scalarRescaledPrincipal`, `OAI.PositiveEinsteinFour.Geometry.scalarRescalingLinearEquiv`, `OAI.PositiveEinsteinFour.Geometry.smoothH1ToL2`, `OAI.PositiveEinsteinFour.Geometry.smoothH1ToL2Linear` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_HodgeTheory06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory06.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C023`, `OAIQ091C024`, `OAIQ091C025`, `OAIQ091C058`, `OAIQ091C059`, `OAIQ091C060`, `OAIQ091C061`, `OAIQ091C062`, `OAIQ091C068` and `OAIQ091C069`; the statements `OAI_PositiveEinsteinFour_Bianchi_matrixRotation_energy`, `OAI_PositiveEinsteinFour_Bianchi_rawGradientGenerator_casimir`, `OAI_PositiveEinsteinFour_Geometry_ScalarCovariantData_curvature_identity`, `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy`, `OAI_PositiveEinsteinFour_HighestHessian_totalMinus_condition` and `OAI_PositiveEinsteinFour_HighestHessian_totalPlus_condition`; the proofs of `OAI_PositiveEinsteinFour_Bianchi_matrixRotation_energy`, `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy` and `OAI_PositiveEinsteinFour_HighestHessian_totalMinus_condition`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C039

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual positive local frames and smooth cutoffs for two-form regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoForm_regularity_cutoff (o : FrameOrientation g) (c : M) (z₀ : ChartTarget c) :
    ∃ (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace), IsOpen U ∧
      ∃ hUt : U ⊆ (chartAt FourSpace c).target,
        (∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive) ∧
        ∃ (χ : FourSpace → ℝ) (_hχ : ContDiff ℝ ∞ χ) (_hc : HasCompactSupport χ),
          tsupport χ ⊆ U ∧ {z | z ∈ tsupport χ ∧ χ z = 1} ∈ 𝓝 z₀.val := by
  obtain ⟨S, hS, U, hU, hzU, hUt, hp⟩ := twoForm_positive_chart_at o c z₀ z₀.property
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hzU)
  let χ : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hs : tsupport (χ : FourSpace → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    exact hdU
  refine ⟨S, hS, U, hU, hUt, hp, χ, χ.contDiff, χ.hasCompactSupport, hs, ?_⟩
  have hone : {z : FourSpace | χ z = 1} ∈ 𝓝 z₀.val := χ.eventuallyEq_one
  filter_upwards [hone] with z hz
  exact ⟨subset_tsupport (χ : FourSpace → ℝ) (by change χ z ≠ 0; rw [hz]; norm_num), hz⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Raising the momentum in the actual kinetic Hamiltonian gives the
ordinary tangent-coordinate geodesic field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem kinetic_force_transpose (g : SmoothMetric M) (c : M)
    (x : FourSpace) (p v : Fin 4 → ℝ) :
    (fun r => p ⬝ᵥ (connectionMatrix g c r x *ᵥ v)) =
      (jacobiConnection (fun r => connectionMatrix g c r x) v)ᵀ *ᵥ p := by
  funext r
  simp only [jacobiConnection, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum, connectionMatrix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [christoffel_comm g c x i r j]
  ring

theorem kinetic_inverse_metric_rate (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (v : Fin 4 → ℝ) :
    (∑ r, v r • matrixPartial (fun z => (metricInChart g c z)⁻¹) r x) =
      -(jacobiConnection (fun r => connectionMatrix g c r x) v *
        (metricInChart g c x)⁻¹) -
      (metricInChart g c x)⁻¹ *
        (jacobiConnection (fun r => connectionMatrix g c r x) v)ᵀ := by
  simp only [matrixPartial_inverseMetric g c x hx, smul_sub, smul_neg,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, jacobiConnection,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.transpose_sum, Matrix.transpose_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual six-dimensional Weitzenböck potential and its first two
matrix traces. These are local algebraic identities, not an index formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem twoFormCurvatureMatrix_apply (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) (a : TwoFormFour) :
    WithLp.toLp 2 (twoFormCurvatureMatrix R *ᵥ WithLp.ofLp a) = twoFormCurvatureAction R a := by
  ext i
  change (∑ j, -R ![(AlgebraicCurvature.pair i).1, (AlgebraicCurvature.pair i).2,
    (AlgebraicCurvature.pair j).1, (AlgebraicCurvature.pair j).2] * a j) = _
  rw [twoFormCurvatureAction_component R hR]
  simp only [neg_mul, Finset.sum_neg_distrib]

theorem twoFormPotentialMatrix_apply (R : CovariantCoordinates 4)
    (hR : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) (a : TwoFormFour) :
    WithLp.toLp 2 (twoFormPotentialMatrix R *ᵥ WithLp.ofLp a) =
      (6 : ℝ) • a - (2 : ℝ) • twoFormCurvatureAction R a := by
  have h := twoFormCurvatureMatrix_apply R hR a
  ext i
  have hi := congrArg (fun v : TwoFormFour => v i) h
  change (twoFormCurvatureMatrix R *ᵥ WithLp.ofLp a) i = twoFormCurvatureAction R a i at hi
  change (twoFormPotentialMatrix R *ᵥ WithLp.ofLp a) i = _
  rw [twoFormPotentialMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  change 6 * a i - 2 * (twoFormCurvatureMatrix R *ᵥ WithLp.ofLp a) i = _
  rw [hi]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rescaling a chart in a frozen orthonormal frame makes the actual principal
coefficients uniformly close to the identity on a fixed unit ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Metric Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarRescaledPoint (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (y : FourSpace) : FourSpace :=
  z₀.val + r • ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀) y)

def scalarRescaledPrincipal (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (y : FourSpace) : Mat4 :=
  frozenScalarPrincipal g c z₀ (scalarRescaledPoint g c z₀ r y)

theorem scalarRescaledPrincipal_zero (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (y : FourSpace) : scalarRescaledPrincipal g c z₀ 0 y = 1 := by
  simp only [scalarRescaledPrincipal, scalarRescaledPoint, zero_smul, add_zero,
    frozenScalarPrincipal_self]

theorem scalarRescaledPrincipal_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (y : FourSpace)
    (hy : scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun x => scalarRescaledPrincipal g c z₀ r x i j) y := by
  apply (frozenScalarPrincipal_contDiffAt g c z₀ _ hy i j).comp
  exact contDiffAt_const.add
    (((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)).contDiff.contDiffAt.const_smul r)

def scalarFrozenDrift (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (z : FourSpace) (j : Fin 4) : ℝ :=
  -∑ a, (chartGramMatrix g c 1 z₀)⁻¹ j a *
    ∑ i, ∑ k, (metricInChart g c z)⁻¹ i k * christoffel g c z a i k

def scalarRescaledDrift (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (y : FourSpace) (j : Fin 4) : ℝ :=
  r * scalarFrozenDrift g c z₀ (scalarRescaledPoint g c z₀ r y) j

theorem scalarFrozenDrift_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (j : Fin 4) : ContDiffAt ℝ ∞ (fun w => scalarFrozenDrift g c z₀ w j) z := by
  unfold scalarFrozenDrift
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro a _
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro k _
  exact (scalarPrincipalCoefficients_smooth g c z hz i k).mul
    (christoffel_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne' a i k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Spatial derivatives of the rescaled coefficients tend uniformly to zero
on a fixed compact set. This includes the derivatives needed by the formal
adjoint of the perturbed scalar operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem scalarParameter_partial_contDiffAt (F : ℝ → FourSpace → ℝ)
    (r : ℝ) (y : FourSpace)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (r, y)) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : ℝ × FourSpace => partialDeriv (F q.1) i q.2) (r, y) := by
  have hu : ContDiffAt ℝ ∞
      (fun p : (ℝ × FourSpace) × FourSpace => F p.1.1 p.2) ((r, y), y) :=
    ContDiffAt.comp (f := fun p : (ℝ × FourSpace) × FourSpace => (p.1.1, p.2))
      ((r, y), y) hF ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
  exact (hu.fderiv contDiffAt_snd (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    (contDiffAt_const (c := coordinateVector i))

theorem scalarParameter_second_contDiffAt (F : ℝ → FourSpace → ℝ)
    (r : ℝ) (y : FourSpace)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (r, y)) (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun q : ℝ × FourSpace =>
      partialDeriv (fun z => partialDeriv (F q.1) j z) i q.2) (r, y) := by
  exact scalarParameter_partial_contDiffAt (fun t z => partialDeriv (F t) j z)
    r y (scalarParameter_partial_contDiffAt F r y hF j) i

theorem scalarCompactParameter_small {ι : Type*} [Fintype ι]
    (F : ι → ℝ × FourSpace → ℝ) {K : Set FourSpace} (hK : IsCompact K)
    (hF : ∀ y ∈ K, ∀ i, ContinuousAt (F i) (0, y))
    (hzero : ∀ y ∈ K, ∀ i, F i (0, y) = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r, |r| < η → ∀ y ∈ K, ∀ i, |F i (r, y)| < ε := by
  let S : Set (ℝ × FourSpace) := {q | ∀ i, |F i q| < ε}
  have hnear : ∀ y ∈ K, S ∈ 𝓝 (0, y) := by
    intro y hy
    apply eventually_all.mpr
    intro i
    apply ((hF y hy i).abs).eventually_lt continuousAt_const
    simpa only [hzero y hy i, abs_zero] using hε
  have htube : S ∈ 𝓝 (0 : ℝ) ×ˢ 𝓝ˢ K := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro y hy
    rw [← nhds_prod_eq]
    exact hnear y hy
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp htube
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨η, hη, ?_⟩
  intro r hr y hy i
  apply hUV ⟨hηU ?_, subset_of_mem_nhdsSet hV hy⟩ i
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hr

theorem scalarParameter_jets_uniform (F : ℝ → FourSpace → ℝ)
    {K : Set FourSpace} (hK : IsCompact K) (k : ℝ)
    (hF : ∀ y ∈ K, ContDiffAt ℝ ∞ (Function.uncurry F) (0, y))
    (hzero : ∀ y, F 0 y = k) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r, |r| < η → ∀ y ∈ K,
      |F r y - k| < ε ∧
      (∀ i, |partialDeriv (F r) i y| < ε) ∧
      (∀ i j, |partialDeriv (fun z => partialDeriv (F r) j z) i y| < ε) := by
  have hz : F 0 = fun _ => k := funext hzero
  let J : Unit ⊕ (Fin 4 ⊕ (Fin 4 × Fin 4)) → ℝ × FourSpace → ℝ
    | Sum.inl _ => fun q => F q.1 q.2 - k
    | Sum.inr (Sum.inl i) => fun q => partialDeriv (F q.1) i q.2
    | Sum.inr (Sum.inr (i, j)) => fun q =>
        partialDeriv (fun z => partialDeriv (F q.1) j z) i q.2
  have hJ : ∀ y ∈ K, ∀ a, ContinuousAt (J a) (0, y) := by
    intro y hy a
    rcases a with _ | (i | ⟨i, j⟩)
    · exact (hF y hy).continuousAt.sub continuousAt_const
    · exact (scalarParameter_partial_contDiffAt F 0 y (hF y hy) i).continuousAt
    · exact (scalarParameter_second_contDiffAt F 0 y (hF y hy) i j).continuousAt
  have hJzero : ∀ y ∈ K, ∀ a, J a (0, y) = 0 := by
    intro y _ a
    rcases a with _ | (i | ⟨i, j⟩)
    · exact sub_eq_zero.mpr (hzero y)
    · simp only [J, hz, partialDeriv, fderiv_fun_const, Pi.zero_apply, zero_apply]
    · simp only [J, hz, partialDeriv, fderiv_fun_const, Pi.zero_apply, zero_apply]
  obtain ⟨η, hη, hb⟩ := scalarCompactParameter_small J hK hJ hJzero ε hε
  refine ⟨η, hη, ?_⟩
  intro r hr y hy
  exact ⟨hb r hr y hy (Sum.inl ()),
    fun i => hb r hr y hy (Sum.inr (Sum.inl i)),
    fun i j => hb r hr y hy (Sum.inr (Sum.inr (i, j)))⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarRescaled_function_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (f : FourSpace → ℝ) (hf : ContDiffAt ℝ ∞ f z₀.val)
    (y : FourSpace) : ContDiffAt ℝ ∞
      (fun q : ℝ × FourSpace => f (scalarRescaledPoint g c z₀ q.1 q.2)) (0, y) := by
  have hp : ContDiffAt ℝ ∞
      (fun q : ℝ × FourSpace => scalarRescaledPoint g c z₀ q.1 q.2) (0, y) :=
    contDiffAt_const.add (contDiffAt_fst.smul
      (((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
        (chartGramMatrix g c 1 z₀)).contDiff.contDiffAt.comp _ contDiffAt_snd))
  have hf' : ContDiffAt ℝ ∞ f (scalarRescaledPoint g c z₀ 0 y) := by
    simpa only [scalarRescaledPoint, zero_smul, add_zero] using hf
  exact hf'.comp (0, y) hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth lower-order coefficients of the actual two-form connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem twoFormSkewAction_antisymm (a b : TwoFormFour) :
    twoFormSkewAction a b = -twoFormSkewAction b a := by
  ext i
  fin_cases i <;> simp [twoFormSkewAction] <;> ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormConnectionAction_contDiffAt (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (a : TwoFormFour) :
    ContDiffAt ℝ ∞ (fun w =>
      twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i w)) a) z := by
  have hC : ContDiffAt ℝ ∞ (fun w => ![
      chartTwoFormConnection (g := g) c S i w 0 1,
      chartTwoFormConnection (g := g) c S i w 0 2,
      chartTwoFormConnection (g := g) c S i w 0 3,
      chartTwoFormConnection (g := g) c S i w 1 2,
      chartTwoFormConnection (g := g) c S i w 1 3,
      chartTwoFormConnection (g := g) c S i w 2 3]) z := by
    apply contDiffAt_pi.mpr
    intro r
    fin_cases r
    · exact chartTwoFormConnection_contDiffAt c S hS i z hz 0 1
    · exact chartTwoFormConnection_contDiffAt c S hS i z hz 0 2
    · exact chartTwoFormConnection_contDiffAt c S hS i z hz 0 3
    · exact chartTwoFormConnection_contDiffAt c S hS i z hz 1 2
    · exact chartTwoFormConnection_contDiffAt c S hS i z hz 1 3
    · exact chartTwoFormConnection_contDiffAt c S hS i z hz 2 3
  have hE : ContDiffAt ℝ ∞
      (fun w => twoFormExtract (chartTwoFormConnection (g := g) c S i w)) z :=
    (PiLp.contDiff_toLp (𝕜 := ℝ) (p := 2) (n := ∞)).comp_contDiffAt z hC
  have h := ((twoFormSkewActionLinear a).toContinuousLinearMap.contDiff.comp_contDiffAt z hE).neg
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => twoFormSkewAction_antisymm _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The completion in the actual two-form H1 norm and its bounded map to
L2. Injectivity of the map is not assumed; it requires the weak derivative
closure argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothH1TwoForm_norm_sq (u : SmoothH1TwoForm o) :
    ‖u‖ ^ 2 = smoothTwoFormL2Inner (u : smoothTwoForms o) u +
      smoothTwoFormCovariantEnergy (u : smoothTwoForms o) u := by
  rw [← real_inner_self_eq_norm_sq]
  rfl

def smoothH1ToL2Linear : SmoothH1TwoForm o →ₗ[ℝ] SmoothL2TwoForm o where
  toFun u := u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smoothH1ToL2Linear_norm_le (u : SmoothH1TwoForm o) :
    ‖smoothH1ToL2Linear u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hL2 : ‖smoothH1ToL2Linear u‖ ^ 2 = smoothTwoFormL2Inner (u : smoothTwoForms o) u := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  rw [hL2, smoothH1TwoForm_norm_sq]
  exact le_add_of_nonneg_right (smoothTwoFormCovariantEnergy_nonneg (u : smoothTwoForms o))

def smoothH1ToL2 : SmoothH1TwoForm o →L[ℝ] SmoothL2TwoForm o :=
  smoothH1ToL2Linear.mkContinuous 1 (fun u => by simpa using smoothH1ToL2Linear_norm_le u)

def smoothTwoFormToH1 : SmoothH1TwoForm o →ₗᵢ[ℝ] TwoFormH1 o :=
  UniformSpace.Completion.toComplₗᵢ

theorem smoothTwoFormToH1_dense : DenseRange (smoothTwoFormToH1 (o := o)) :=
  UniformSpace.Completion.denseRange_coe

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the two derivative slots, in arbitrary coordinates
and in actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFramedSecondDerivative_change (u : M → TwoFormFour) {x : M}
    (e f : OrthonormalFrame g x) :
    twoFormFramedSecondDerivative o u ⟨x, f⟩ =
      frameTensor (e.changeMatrix f) (twoFormFramedSecondDerivative o u ⟨x, e⟩) := by
  unfold twoFormFramedSecondDerivative
  rw [← frameTensor_mul, e.mul_changeMatrix f]

theorem twoFormFramedRoughTrace_change (u : M → TwoFormFour) {x : M}
    (e f : OrthonormalFrame g x) :
    twoFormFramedRoughTrace o u ⟨x, f⟩ =
      frameTensor (e.changeMatrix f) (twoFormFramedRoughTrace o u ⟨x, e⟩) := by
  unfold twoFormFramedRoughTrace
  rw [twoFormFramedSecondDerivative_change u e f]
  exact twoFormSecondTrace_orthogonal _ (mul_eq_one_comm.mp (e.changeMatrix_orthogonal f)) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality and support control for the actual two-form differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCoordinates_eq_zero (u : M → TwoFormFour) (c : M) (z : FourSpace)
    (hu : u ((chartAt FourSpace c).symm z) = 0) : twoFormCoordinates o u c z = 0 := by
  unfold twoFormCoordinates twoFormTensorAt
  rw [hu]
  change frameTensor _ (frameTensor _ (twoFormTensorLinear 0)) = 0
  rw [map_zero, frameTensor_zero_two, frameTensor_zero_two]

theorem twoFormCoordinates_congr_nhds {u v : M → TwoFormFour} (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (h : u =ᶠ[𝓝 ((chartAt FourSpace c).symm z)] v) :
    twoFormCoordinates o u c =ᶠ[𝓝 z] twoFormCoordinates o v c := by
  have he := h.comp_tendsto ((chartAt FourSpace c).continuousAt_symm hz).tendsto
  filter_upwards [he] with w hw
  dsimp only [Function.comp_def] at hw
  unfold twoFormCoordinates twoFormTensorAt
  rw [hw]

theorem twoFormCovariantCoordinates_zero (c : M) (z : FourSpace) :
    twoFormCovariantCoordinates o (fun _ => 0) c z = 0 := by
  have he : twoFormCoordinates o (fun _ => 0) c = 0 := by
    funext w
    exact twoFormCoordinates_eq_zero _ c w rfl
  unfold twoFormCovariantCoordinates
  rw [he]
  funext a
  simp [covariantDerivative, partialDeriv]

theorem twoFormFramedCovariantDerivative_zero_of_nhds (u : M → TwoFormFour)
    (e : FrameBundle g) (hu : u =ᶠ[𝓝 e.base] fun _ => 0) :
    twoFormFramedCovariantDerivative o u e = 0 := by
  let z := chartAt FourSpace e.base e.base
  have hz : z ∈ (chartAt FourSpace e.base).target := mem_chart_target FourSpace e.base
  have hu' : u =ᶠ[𝓝 ((chartAt FourSpace e.base).symm z)] fun _ => 0 := by
    simpa only [z, (chartAt FourSpace e.base).left_inv (mem_chart_source FourSpace e.base)] using hu
  have hc := covariantDerivative_congr g e.base
    (twoFormCoordinates_congr_nhds (o := o) e.base z hz hu')
  change twoFormCovariantCoordinates o u e.base z =
    twoFormCovariantCoordinates o (fun _ => 0) e.base z at hc
  rw [twoFormCovariantCoordinates_zero] at hc
  change frameTensor e.frame.matrix (twoFormCovariantCoordinates o u e.base z) = 0
  rw [hc]
  funext a
  simp [frameTensor]

theorem twoFormCovariantPairing_tsupport_right (u v : M → TwoFormFour) :
    tsupport (twoFormCovariantPairing o u v) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport v)
  intro x hx
  by_contra hn
  have hzero := twoFormFramedCovariantDerivative_zero_of_nhds (o := o) v
    ⟨x, o.frame x⟩ (notMem_tsupport_iff_eventuallyEq.mp hn)
  apply hx
  unfold twoFormCovariantPairing
  rw [hzero]
  simp [frameTensorPairing]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruction of the full covariant derivative in a local frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormLocalNabla_congr (c : M) (S : Mat4) {a b : FourSpace → TwoFormFour}
    {z : FourSpace} (h : a =ᶠ[𝓝 z] b) (i : Fin 4) :
    twoFormLocalNabla (g := g) c S a i z = twoFormLocalNabla (g := g) c S b i z := by
  unfold twoFormLocalNabla
  rw [h.fderiv_eq, h.self_of_nhds]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Realization of compactly supported local orthonormal-frame tests as
actual smooth global two-forms, including their covariant derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Function
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormGramTestTensor (g : SmoothMetric M) (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) (z : FourSpace) : CovariantCoordinates 2 :=
  frameTensor ((chartGramMatrix g c S z)ᵀ * metricInChart g c z) (twoFormTensor (a z))

theorem twoFormGramTestTensor_smooth (g : SmoothMetric M) (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target) :
    ContDiffOn ℝ ∞ (twoFormGramTestTensor g c S a) (chartAt FourSpace c).target := by
  apply contDiffOn_pi.mpr
  intro v z hz
  have hT : ContDiffAt ℝ ∞ (fun w => twoFormTensor (a w)) z :=
    twoFormTensorLinear.toContinuousLinearMap.contDiff.comp_contDiffAt z
      (ha.contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hz))
  have hG (i j : Fin 4) : ContDiffAt ℝ ∞
      (fun w => ((chartGramMatrix g c S w)ᵀ * metricInChart g c w) i j) z := by
    change ContDiffAt ℝ ∞ (fun w => ∑ k,
      chartGramMatrix g c S w k i * metricInChart g c w k j) z
    exact ContDiffAt.sum (fun k _ => (chartGramMatrix_contDiffAt g c S z hz k i).mul
      (metricInChart_contDiffAt g c z hz k j))
  apply ContDiffAt.contDiffWithinAt
  change ContDiffAt ℝ ∞ (fun w => ∑ b,
    (∏ k, ((chartGramMatrix g c S w)ᵀ * metricInChart g c w) (b k) (v k)) *
      twoFormTensor (a w) b) z
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod (fun k _ => hG (b k) (v k))).mul
    ((ContinuousLinearMap.proj b : CovariantCoordinates 2 →L[ℝ] ℝ).contDiff.comp_contDiffAt z hT)

theorem twoFormGramTestTensor_skew (g : SmoothMetric M) (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) (z : FourSpace) (i j : Fin 4) :
    twoFormGramTestTensor g c S a z ![j,i] = -twoFormGramTestTensor g c S a z ![i,j] := by
  apply twoTensor_frame_skew
  intro k l
  exact congrArg (fun A : Mat4 => A k l) (twoFormMatrix_skew (a z))

theorem twoFormGramTestTensor_support (g : SmoothMetric M) (c : M) (S : Mat4)
    (a : FourSpace → TwoFormFour) : tsupport (twoFormGramTestTensor g c S a) ⊆ tsupport a := by
  apply closure_mono
  intro z hz
  by_contra hn
  have hzero : a z = 0 := notMem_support.mp hn
  apply hz
  unfold twoFormGramTestTensor
  rw [hzero]
  change frameTensor _ (twoFormTensorLinear 0) = 0
  rw [map_zero, frameTensor_zero_two]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic first-derivative pairing in a chart. Its principal
coefficient is the actual inverse metric on each of the six components. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoForm_weighted_rows_pairing (E : Mat4) (A B : Fin 4 → TwoFormFour) :
    (∑ i, inner ℝ (∑ j, E j i • A j) (∑ k, E k i • B k)) =
      ∑ j, ∑ k, (E * Eᵀ) j k * inner ℝ (A j) (B k) := by
  conv_rhs => rw [Finset.sum_comm]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = (∑ i, E j i * E k i) * inner ℝ (A k) (B j) :=
      (Finset.sum_mul Finset.univ (fun i => E j i * E k i) (inner ℝ (A k) (B j))).symm
    _ = _ := by
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormLocalNablaRows_pairing (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a b : FourSpace → TwoFormFour) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    (∑ i, inner ℝ (twoFormLocalNablaRows (g := g) c S a z i)
      (twoFormLocalNablaRows (g := g) c S b z i)) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        inner ℝ (twoFormLocalNabla (g := g) c S a i z)
          (twoFormLocalNabla (g := g) c S b j z) := by
  unfold twoFormLocalNablaRows
  rw [twoForm_weighted_rows_pairing, chartGramMatrix_mul_transpose_orthogonal g c S hS z hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite infinitesimal matrix is the actual connection-curvature
action on the two-form coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormCurvatureRow (R : CovariantCoordinates 4) (i j : Fin 4) : TwoFormFour :=
  twoFormExtract (fun k l => R ![i,j,k,l])

theorem twoFormMatrix_curvatureRow (R : CovariantCoordinates 4)
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) (i j : Fin 4) :
    twoFormMatrix (twoFormCurvatureRow R i j) = fun k l => R ![i,j,k,l] := by
  apply twoFormMatrix_extract
  ext k l
  exact hl i j k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of an actual normal variation with the columns of
the globally chosen Jacobi solution. Uniqueness uses only the first-order
equation and its initial values. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

def jacobiColumnLinear : (Fin 3 → ℝ) →ₗ[ℝ] NormalMatrix where
  toFun := jacobiColumn
  map_add' v w := by
    ext i j
    by_cases hj : j = 0 <;> simp [jacobiColumn, hj]
  map_smul' r v := by
    ext i j
    by_cases hj : j = 0 <;> simp [jacobiColumn, hj]

theorem hasDerivAt_jacobiColumn {y : ℝ → Fin 3 → ℝ}
    {v : Fin 3 → ℝ} {t : ℝ} (hy : HasDerivAt y v t) :
    HasDerivAt (fun s => jacobiColumn (y s)) (jacobiColumn v) t :=
  jacobiColumnLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hy

/-- A normal vector solution with initial position zero and velocity `w`
is the action of the matrix solution on `w`. -/
theorem normal_jacobi_eq_mulVec {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K)
    (y z : ℝ → Fin 3 → ℝ) (w : Fin 3 → ℝ) (a b : ℝ)
    (hzero : (0 : ℝ) ∈ Ioo a b) (hy0 : y 0 = 0) (hz0 : z 0 = w)
    (hy : ∀ s ∈ Ioo a b, HasDerivAt y (z s) s)
    (hz : ∀ s ∈ Ioo a b, HasDerivAt z (-(R s *ᵥ y s)) s) :
    ∀ s ∈ Ioo a b, y s = d.J s *ᵥ w ∧ z s = d.V s *ᵥ w := by
  let B := jacobiColumn w
  let γ : ℝ → JacobiState := fun s => (jacobiColumn (y s), jacobiColumn (z s))
  let η : ℝ → JacobiState := fun s => (d.J s * B, d.V s * B)
  have hγ : LinearCurveOn (fun s => jacobiStateOperator (R s)) γ (Ioo a b) := by
    intro s hs
    have hpos := hasDerivAt_jacobiColumn (hy s hs)
    have hvel := hasDerivAt_jacobiColumn (hz s hs)
    have hneg : jacobiColumn (-(R s *ᵥ y s)) = -(R s * jacobiColumn (y s)) := by
      rw [mul_jacobiColumn]
      exact jacobiColumnLinear.map_neg _
    rw [hneg] at hvel
    exact hpos.prodMk hvel
  have hη : LinearCurveOn (fun s => jacobiStateOperator (R s)) η (Ioo a b) := by
    intro s _
    have hpos := (d.position_derivative s).mul_const B
    have hvel := (d.velocity_derivative s).mul_const B
    simpa only [η, jacobiStateOperator_apply, neg_mul, Matrix.mul_assoc] using
      hpos.prodMk hvel
  have hbound (s : ℝ) : ‖jacobiStateOperator (R s)‖ ≤ ((1 + K : ℝ≥0) : ℝ) := by
    apply (norm_jacobiStateOperator_le _).trans
    simpa only [NNReal.coe_add, NNReal.coe_one, add_comm] using add_le_add_left (hK s) 1
  have hinit : γ 0 = η 0 := by
    simp only [γ, η, hy0, hz0, d.initial_position, d.initial_velocity,
      Matrix.zero_mul, Matrix.one_mul, B]
    congr 1
    ext i j
    simp [jacobiColumn]
  have heq := linear_curve_eqOn_interval (fun s => jacobiStateOperator (R s))
    (1 + K) hbound hγ hη hzero hinit
  intro s hs
  have h := heq hs
  have hp : jacobiColumn (y s) = jacobiColumn (d.J s *ᵥ w) := by
    simpa only [γ, η, B, mul_jacobiColumn] using congrArg Prod.fst h
  have hv : jacobiColumn (z s) = jacobiColumn (d.V s *ᵥ w) := by
    simpa only [γ, η, B, mul_jacobiColumn] using congrArg Prod.snd h
  constructor
  · funext i
    simpa only [jacobiColumn, ite_true, if_true] using congrArg (fun A : NormalMatrix => A i 0) hp
  · funext i
    simpa only [jacobiColumn, ite_true, if_true] using congrArg (fun A : NormalMatrix => A i 0) hv

end
end PositiveEinsteinFour.Jacobi

end


section

/-! The full four-dimensional Jacobi system splits into its linear radial
part and the three-dimensional normal matrix solution. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix Set _root_.OAI.PositiveEinsteinFour.Geometry
open scoped _root_.Topology NNReal Matrix.Norms.L2Operator

noncomputable section

/-- The radial and normal initial-value equations determine the full frame variation. -/
theorem full_jacobi_eq_mulVec {R : ℝ → NormalMatrix}
    (d : MatrixJacobiSolution R) (K : ℝ≥0) (hK : ∀ s, ‖R s‖ ≤ K)
    (y z : ℝ → Fin 4 → ℝ) (w : Fin 4 → ℝ) (a b : ℝ)
    (hzero : (0 : ℝ) ∈ Ioo a b) (hy0 : y 0 = 0) (hz0 : z 0 = w)
    (hy : ∀ s ∈ Ioo a b, HasDerivAt y (z s) s)
    (hz : ∀ s ∈ Ioo a b,
      HasDerivAt z (-(Fin.cons 0 (R s *ᵥ fun i => y s i.succ))) s) :
    ∀ s ∈ Ioo a b,
      y s = jacobiBlockMatrix s (d.J s) *ᵥ w ∧
      z s = jacobiBlockMatrix 1 (d.V s) *ᵥ w := by
  have hyHead (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r => y r 0) (z s 0) s := hasDerivAt_pi.mp (hy s hs) 0
  have hzHead (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r => z r 0) 0 s := by
    simpa only [Pi.neg_apply, Fin.cons_zero, neg_zero] using hasDerivAt_pi.mp (hz s hs) 0
  have hyTail (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r (i : Fin 3) => y r i.succ) (fun i => z s i.succ) s := by
    apply hasDerivAt_pi.mpr
    intro i
    exact hasDerivAt_pi.mp (hy s hs) i.succ
  have hzTail (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r (i : Fin 3) => z r i.succ)
        (-(R s *ᵥ fun i => y s i.succ)) s := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [Pi.neg_apply, Fin.cons_succ] using hasDerivAt_pi.mp (hz s hs) i.succ
  have hy0Head : y 0 0 = 0 := congrFun hy0 0
  have hz0Head : z 0 0 = w 0 := congrFun hz0 0
  have hy0Tail : (fun i : Fin 3 => y 0 i.succ) = 0 := by
    funext i
    exact congrFun hy0 i.succ
  have hz0Tail : (fun i : Fin 3 => z 0 i.succ) = (fun i => w i.succ) := by
    funext i
    exact congrFun hz0 i.succ
  have hhead := radial_jacobi_pair_eq (fun s => y s 0) (fun s => z s 0)
    (w 0) a b hzero hy0Head hz0Head hyHead hzHead
  have htail := normal_jacobi_eq_mulVec d K hK
    (fun s i => y s i.succ) (fun s i => z s i.succ) (fun i => w i.succ)
    a b hzero hy0Tail hz0Tail hyTail hzTail
  intro s hs
  constructor
  · rw [jacobiBlockMatrix_mulVec]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using (hhead s hs).1
    · simpa only [Fin.cons_succ] using congrFun (htail s hs).1 j
  · rw [jacobiBlockMatrix_mulVec]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero, one_mul] using (hhead s hs).2
    · simpa only [Fin.cons_succ] using congrFun (htail s hs).2 j

end
end PositiveEinsteinFour.Jacobi
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Frame-bundle integral realizations of the intrinsic two-form pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_inner (u v : M → TwoFormFour) (e : FrameBundle g) :
    inner ℝ (twoFormFrameValue o u e) (twoFormFrameValue o v e) =
      inner ℝ (u e.base) (v e.base) :=
  (twoFormFrameIsometry _ ((o.frame e.base).changeMatrix_orthogonal e.frame)).inner_map_map _ _

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

theorem smoothTwoFormL2Inner_eq_frame (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner u v = ∫ e,
      inner ℝ (twoFormFrameValue o u.val e) (twoFormFrameValue o v.val e)
        ∂canonicalFrameMeasure g o := by
  unfold smoothTwoFormL2Inner
  rw [← canonicalFrameMeasure_integral_base g o _ (smoothTwoForm_pairing_integrable u v)]
  apply integral_congr_ae
  filter_upwards [] with e
  exact (twoFormFrameValue_inner u.val v.val e).symm

theorem smoothTwoFormCovariantEnergy_eq_frame (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v = (1 / 2 : ℝ) * ∫ e,
      ∑ i, ∑ j, ∑ k, twoFormFramedCovariantDerivative o u.val e ![i,j,k] *
        twoFormFramedCovariantDerivative o v.val e ![i,j,k] ∂canonicalFrameMeasure g o := by
  unfold smoothTwoFormCovariantEnergy
  rw [← canonicalFrameMeasure_integral_base g o _ (smoothTwoFormCovariantPairing_integrable u v)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with e
  rw [twoFormCovariantPairing_eq_frame, frameTensorPairing_three]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form rough Green identity from the actual invariant parallel
flows. No integration-by-parts input is added to the geometry. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormGreen_compactFrame : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rough Green pairing is bounded by the L2 value norm.
This is the estimate needed to close the covariant derivative graph. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormBound_compactFrame_rfb4d6b_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
def smoothTwoFormEuclideanTrace (u : smoothTwoForms o) : C(FrameBundle g, TwoTensorEuclidean) :=
  ⟨fun e => WithLp.toLp 2 (twoFormFramedRoughTrace o u.val e),
    (PiLp.continuous_toLp 2 _).comp u.property.continuous_framedRoughTrace⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite tensor estimates for the chart localization of two-forms.
The bounds involve the actual value and covariant energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartTransport (g : SmoothMetric M) (c : M) (z : FourSpace) : Mat4 :=
  (chartGramMatrix g c 1 z)ᵀ * metricInChart g c z

theorem twoFormChartTransport_continuousOn (g : SmoothMetric M) (c : M) :
    ContinuousOn (twoFormChartTransport g c) (chartAt FourSpace c).target := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j z hz
  change ContinuousWithinAt (fun w => ∑ k,
    chartGramMatrix g c 1 w k i * metricInChart g c w k j) _ z
  exact (ContDiffAt.sum (fun k _ =>
    (chartGramMatrix_contDiffAt g c 1 z hz k i).mul
      (metricInChart_contDiffAt g c z hz k j))).continuousAt.continuousWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual covariant derivative retains the alternating two-form slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem twoFormFramedValue_skew (u : M → TwoFormFour) (e : FrameBundle g) (j k : Fin 4) :
    twoFormFramedValue o u e ![k,j] = -twoFormFramedValue o u e ![j,k] := by
  rw [twoFormFramedValue_eq]
  exact congrArg (fun A : Mat4 => A j k) (twoFormMatrix_skew (twoFormFrameValue o u e))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The H1 pairing against a smooth two-form extends to the actual L2
completion by the rough Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormGreenLinear (v : SmoothL2TwoForm o) : SmoothL2TwoForm o →ₗ[ℝ] ℝ where
  toFun u := smoothTwoFormL2Inner (u : smoothTwoForms o) v +
    smoothTwoFormCovariantEnergy (u : smoothTwoForms o) v
  map_add' u w := by
    exact (congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_add (u : smoothTwoForms o) w v)
      (smoothTwoFormCovariantEnergy_add (u : smoothTwoForms o) w v)).trans
      (add_add_add_comm _ _ _ _)
  map_smul' r u := by
    exact (congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_smul r (u : smoothTwoForms o) v)
      (smoothTwoFormCovariantEnergy_smul r (u : smoothTwoForms o) v)).trans
      (mul_add r _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The base L² representative of an intrinsic H¹ scalar is a bounded
linear map, obtained from the closed image of base pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.h1Base_frameCompact
theorem scalarH1BaseValue_spec (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    scalarBasePullback g o (scalarH1BaseValue g o d u) = scalarH1Value d u :=
  scalarH1BaseValueFun_spec g o d u

theorem scalarH1BaseValue_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d)
    (b : Lp ℝ 2 (normalizedVolume g)) (hb : scalarBasePullback g o b = scalarH1Value d u) :
    scalarH1BaseValue g o d u = b := by
  apply (scalarBasePullback g o).injective
  exact (scalarH1BaseValue_spec g o d u).trans hb.symm

theorem scalarH1BaseValue_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    scalarH1BaseValue g o d (smoothScalarToH1 d a) = smoothScalarBaseL2 g a := by
  apply scalarH1BaseValue_eq
  exact scalarBasePullback_smooth g o a

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact chart control of ordinary derivatives by the actual two-form
H1 energy. The connection coefficients are bounded only on the chosen
compact chart set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

def tensorSlotWeight (n : ℕ) (P : Mat4) : ℝ :=
  ∑ a : Fin n → Fin 4, ∑ s : Fin n, ∑ b : Fin 4, |P b (a s)|

theorem tensorSlotWeight_nonneg (n : ℕ) (P : Mat4) : 0 ≤ tensorSlotWeight n P :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

theorem tensorSlotWeight_continuous (n : ℕ) : Continuous (tensorSlotWeight n) := by
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro s _
  apply continuous_finsetSum
  intro b _
  exact ((continuous_apply (a s)).comp (continuous_apply b)).abs

theorem tensorSlotAction_abs_le_weight {n : ℕ} (P : Mat4) (T : CovariantCoordinates n)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ a, |T a| ≤ C) (a : Fin n → Fin 4) :
    |tensorSlotAction P T a| ≤ tensorSlotWeight n P * C := by
  calc
    _ ≤ ∑ s : Fin n, |∑ b : Fin 4, P b (a s) * T (Function.update a s b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : Fin n, ∑ b : Fin 4, |P b (a s)| * C := by
      apply Finset.sum_le_sum
      intro s _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hT _) (abs_nonneg _)
    _ = (∑ s : Fin n, ∑ b : Fin 4, |P b (a s)|) * C := by
      simp only [Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      unfold tensorSlotWeight
      exact Finset.single_le_sum (f := fun a : Fin n → Fin 4 =>
        ∑ s : Fin n, ∑ b : Fin 4, |P b (a s)|)
        (fun a _ => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg (fun b _ =>
          abs_nonneg (P b (a s))))) (Finset.mem_univ a)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormChartConnectionWeight (g : SmoothMetric M) (c : M) (z : FourSpace) : ℝ :=
  ∑ i : Fin 4, tensorSlotWeight 2 (connectionMatrix g c i z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reverse chart norm control. This recovers the intrinsic two-form
value from its finitely many compact coordinate components. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

theorem twoForm_norm_le_tensor_sum (u : TwoFormFour) :
    ‖u‖ ≤ ∑ a : Fin 2 → Fin 4, |twoFormTensor u a| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun a : Fin 2 → Fin 4 => |twoFormTensor u a|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hs
  have hn := twoFormTensor_norm u
  simp only [frameTensorSquareNorm, frameTensorPairing, ← pow_two] at hn
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mp
  nlinarith [sq_nonneg ‖u‖]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior-derivative and codifferential energy of a smooth
two-form, and its integrated Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_5
def smoothTwoFormDeRhamEnergy (u : smoothTwoForms o) : ℝ :=
  ∫ e, twoFormDeRhamQuadratic (fun i j k =>
    twoFormFramedCovariantDerivative o u.val e ![i,j,k]) ∂canonicalFrameMeasure g o

theorem smoothTwoFormDeRhamEnergy_nonneg (u : smoothTwoForms o) :
    0 ≤ smoothTwoFormDeRhamEnergy u :=
  integral_nonneg (fun _ => twoFormDeRhamQuadratic_nonneg _)

theorem smoothTwoForm_derivative_product_integrable (u v : smoothTwoForms o)
    (a b : Fin 3 → Fin 4) :
    Integrable (fun e => twoFormFramedCovariantDerivative o u.val e a *
      twoFormFramedCovariantDerivative o v.val e b) (canonicalFrameMeasure g o) :=
  (((continuous_apply a).comp u.property.continuous_framedCovariantDerivative).mul
    ((continuous_apply b).comp v.property.continuous_framedCovariantDerivative)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential differential and its metric Jacobian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem jacobiBlockMatrix_rescale (t : ℝ) (ht : t ≠ 0) (J : Jacobi.NormalMatrix) :
    t⁻¹ • jacobiBlockMatrix t J = jacobiBlockMatrix 1 (t⁻¹ • J) := by
  ext i j
  change t⁻¹ * jacobiBlockMatrix t J i j = jacobiBlockMatrix 1 (t⁻¹ • J) i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [jacobiBlockMatrix, ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The traced second covariant derivative is an actual smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def twoFormTraceExtract : CovariantCoordinates 4 →L[ℝ] TwoFormFour :=
  ((twoFormExtractLinear.comp twoTensorMatrixLinear).comp twoFormTraceLinear).toContinuousLinearMap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormRoughTraceField (o : FrameOrientation g) (u : M → TwoFormFour) : M → TwoFormFour :=
  fun x => twoFormExtract (twoTensorMatrixLinear (twoFormFramedRoughTrace o u ⟨x, o.frame x⟩))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed exponential is a C1 manifold map and satisfies the
radial Gauss identity, as a consequence of its actual differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalized_frame_pairing (E G : Mat4) (hE : Eᵀ * G * E = 1)
    (u v : Fin 4 → ℝ) : (E *ᵥ u) ⬝ᵥ (G *ᵥ (E *ᵥ v)) = u ⬝ᵥ v := by
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec E u (G *ᵥ (E *ᵥ v))]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Base L² scalars are locally Euclidean L² in every metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem scalarChart_density_lower_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, δ ≤ chartVolumeDensity g c z :=
  hK.exists_forall_le'
    (fun z hz => (chartVolumeDensity_contDiffAt g c z (hKt hz)).continuousAt.continuousWithinAt)
    (fun z hz => chartVolumeDensity_pos g c z (hKt hz))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate test equation for the actual second-order elliptic operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarChartOperator (g : SmoothMetric M) (c : M) (ψ : FourSpace → ℝ)
    (z : FourSpace) : ℝ :=
  ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
    (partialDeriv (fun w => partialDeriv ψ j w) i z -
      ∑ k, christoffel g c z k i j * partialDeriv ψ k z)

theorem scalarChartOperator_congr_nhds (g : SmoothMetric M) (c : M)
    {ψ χ : FourSpace → ℝ} {z : FourSpace} (h : ψ =ᶠ[𝓝 z] χ) :
    scalarChartOperator g c ψ z = scalarChartOperator g c χ z := by
  have h₁ (i : Fin 4) :
      (fun w => partialDeriv ψ i w) =ᶠ[𝓝 z] (fun w => partialDeriv χ i w) :=
    (h.fderiv (𝕜 := ℝ)).mono (fun _ hw =>
      congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hw)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  · exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      ((h₁ j).fderiv_eq (𝕜 := ℝ))
  · apply Finset.sum_congr rfl
    intro k _
    rw [(h₁ k).eq_of_nhds]

end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second coordinate derivatives under a fixed affine change of
four-dimensional coordinates, used for rescaling the actual scalar operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff BigOperators

noncomputable section

theorem scalarAffineMap_partial_second (C : Mat4) (q z : FourSpace)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (i j : Fin 4) :
    partialDeriv (fun w => partialDeriv (fun v => ψ (scalarAffineMap C q v)) j w) i z =
      ∑ a, ∑ b, C a j * (C b i *
        partialDeriv (fun v => partialDeriv ψ a v) b (scalarAffineMap C q z)) := by
  have hp (a : Fin 4) : ContDiff ℝ ∞ (fun w => partialDeriv ψ a w) :=
    (hψ.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
      (contDiff_const (c := coordinateVector a))
  have hfirst : (fun w => partialDeriv (fun v => ψ (scalarAffineMap C q v)) j w) =
      (fun w => ∑ a, C a j * partialDeriv ψ a (scalarAffineMap C q w)) := by
    funext w
    exact scalarAffineMap_partial C q w ψ (hψ.differentiable (by simp) _) j
  rw [hfirst]
  have hd (a : Fin 4) : DifferentiableAt ℝ
      (fun w => C a j * partialDeriv ψ a (scalarAffineMap C q w)) z :=
    ((hp a).differentiable (by simp) _).comp z
      (scalarAffineMap_hasFDerivAt C q z).differentiableAt |>.const_mul (C a j)
  change (fderiv ℝ (fun w => ∑ a, C a j * partialDeriv ψ a (scalarAffineMap C q w)) z)
    (coordinateVector i) = _
  rw [fderiv_fun_sum (fun a (_ : a ∈ Finset.univ) => hd a), _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  change partialDeriv (fun w => C a j * partialDeriv ψ a (scalarAffineMap C q w)) i z = _
  have hmul : partialDeriv (fun w => C a j * partialDeriv ψ a (scalarAffineMap C q w)) i z =
      C a j * partialDeriv (fun w => partialDeriv ψ a (scalarAffineMap C q w)) i z := by
    change (fderiv ℝ ((C a j) • fun w => partialDeriv ψ a (scalarAffineMap C q w)) z)
      (coordinateVector i) = _
    rw [fderiv_const_smul_field]
    rfl
  rw [hmul, scalarAffineMap_partial C q z _ ((hp a).differentiable (by simp) _) i,
    Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual metric coefficients put the chart Laplacian in divergence
form.  This supplies the coefficient identity for local energy estimates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_metric_trace_cancellation (H : Mat4)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hΓ : ∀ a i k, Γ a i k = Γ a k i) (j : Fin 4) :
    (∑ i, (∑ k, Γ k i k) * H i j) =
      ∑ i, ∑ k, Γ i i k * H k j := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [hΓ k i k]

theorem scalar_metric_divergence_algebra (ρ : ℝ) (H : Mat4)
    (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hΓ : ∀ a i k, Γ a i k = Γ a k i) (j : Fin 4) :
    (∑ i, ((∑ k, Γ k i k) * ρ * H i j +
      ρ * (-(∑ k, Γ i i k * H k j) - ∑ k, H i k * Γ j i k))) =
      -ρ * ∑ i, ∑ k, H i k * Γ j i k := by
  calc
    _ = ∑ i, (ρ * ((∑ k, Γ k i k) * H i j) -
        ρ * (∑ k, Γ i i k * H k j) - ρ * (∑ k, H i k * Γ j i k)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ρ * ((∑ i, (∑ k, Γ k i k) * H i j) -
        (∑ i, ∑ k, Γ i i k * H k j) - (∑ i, ∑ k, H i k * Γ j i k)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ = _ := by rw [scalar_metric_trace_cancellation H Γ hΓ j]; ring

theorem scalar_metric_coefficient_divergence (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (j : Fin 4) :
    (∑ i, partialDeriv
      (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z) =
      -chartVolumeDensity g c z *
        ∑ i, ∑ k, (metricInChart g c z)⁻¹ i k * christoffel g c z j i k := by
  have hterm (i : Fin 4) :
      partialDeriv (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z =
        (∑ k, christoffel g c z k i k) * chartVolumeDensity g c z *
          (metricInChart g c z)⁻¹ i j + chartVolumeDensity g c z *
            (-(∑ k, christoffel g c z i i k * (metricInChart g c z)⁻¹ k j) -
              ∑ k, (metricInChart g c z)⁻¹ i k * christoffel g c z j i k) := by
    have hρ := (chartVolumeDensity_contDiffAt g c z hz).differentiableAt (by first | simp | exact_mod_cast le_top)
    have hH := (scalarPrincipalCoefficients_smooth g c z hz i j).differentiableAt (by first | simp | exact_mod_cast le_top)
    have hprod : partialDeriv
        (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z =
        partialDeriv (chartVolumeDensity g c) i z * (metricInChart g c z)⁻¹ i j +
          chartVolumeDensity g c z * partialDeriv (fun w => (metricInChart g c w)⁻¹ i j) i z := by
      simp only [partialDeriv, fderiv_fun_mul hρ hH, _root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      ring
    rw [hprod, partialDeriv_chartVolumeDensity g c z hz i]
    have hInv := congrFun (congrFun (matrixPartial_inverseMetric g c z hz i) i) j
    change partialDeriv (fun w => (metricInChart g c w)⁻¹ i j) i z = _ at hInv
    rw [hInv]
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
      Matrix.transpose_apply, connectionMatrix]
  simp_rw [hterm]
  exact scalar_metric_divergence_algebra _ _ _ (christoffel_comm g c z) j

theorem scalar_partial_mul {f h : FourSpace → ℝ} {z : FourSpace}
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (i : Fin 4) :
    partialDeriv (fun w => f w * h w) i z =
      partialDeriv f i z * h z + f z * partialDeriv h i z := by
  simp only [partialDeriv, fderiv_fun_mul hf hh, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem scalarChartOperator_divergence (g : SmoothMetric M) (c : M)
    (ψ : FourSpace → ℝ) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (hψ : ContDiffAt ℝ ∞ ψ z) :
    (∑ i, partialDeriv (fun w => ∑ j,
      chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z) =
      chartVolumeDensity g c z * scalarChartOperator g c ψ z := by
  have hP (j : Fin 4) : DifferentiableAt ℝ (fun w => partialDeriv ψ j w) z :=
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiffAt_const (c := coordinateVector j))).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hA (i j : Fin 4) : DifferentiableAt ℝ
      (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) z :=
    ((chartVolumeDensity_contDiffAt g c z hz).mul
      (scalarPrincipalCoefficients_smooth g c z hz i j)).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hterm (i : Fin 4) :
      partialDeriv (fun w => ∑ j,
        chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z =
      ∑ j, (partialDeriv
        (fun w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j) i z *
          partialDeriv ψ j z + chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j *
            partialDeriv (fun w => partialDeriv ψ j w) i z) := by
    have hs := fderiv_fun_sum (u := Finset.univ)
      (A := fun j w => chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j *
        partialDeriv ψ j w) (fun j _ => (hA i j).mul (hP j))
    change (fderiv ℝ _ z) (coordinateVector i) = _
    rw [hs, _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact scalar_partial_mul (hA i j) (hP j) i
  simp_rw [hterm]
  exact scalar_divergence_expansion _ _ _ _ _ _
    (scalar_metric_coefficient_divergence g c z hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate Laplacian under an affine change of variables. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

def scalarPartialVector (ψ : FourSpace → ℝ) (z : FourSpace) : Fin 4 → ℝ :=
  fun i => partialDeriv ψ i z

def scalarPartialMatrix (ψ : FourSpace → ℝ) (z : FourSpace) : Mat4 :=
  fun i j => partialDeriv (fun w => partialDeriv ψ j w) i z

def scalarPrincipalContraction (H Q : Mat4) : ℝ := ∑ i, ∑ j, H i j * Q i j

theorem scalarPrincipalContraction_eq_trace (H Q : Mat4) :
    scalarPrincipalContraction H Q = (H * Qᵀ).trace := by
  simp only [scalarPrincipalContraction, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.transpose_apply]

theorem scalarAffineMap_partialVector (C : Mat4) (q z : FourSpace)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    scalarPartialVector (fun w => ψ (scalarAffineMap C q w)) z =
      Cᵀ *ᵥ scalarPartialVector ψ (scalarAffineMap C q z) := by
  funext i
  exact scalarAffineMap_partial C q z ψ (hψ.differentiable (by simp) _) i

theorem scalarAffineMap_partialMatrix (C : Mat4) (q z : FourSpace)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    scalarPartialMatrix (fun w => ψ (scalarAffineMap C q w)) z =
      Cᵀ * scalarPartialMatrix ψ (scalarAffineMap C q z) * C := by
  ext i j
  rw [scalarPartialMatrix, scalarAffineMap_partial_second C q z ψ hψ i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp [scalarPartialMatrix]
  ring

theorem scalarPrincipalContraction_affine (H C Q : Mat4) :
    scalarPrincipalContraction H (Cᵀ * Q * C) =
      scalarPrincipalContraction (C * H * Cᵀ) Q := by
  rw [scalarPrincipalContraction_eq_trace, scalarPrincipalContraction_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (H * (Cᵀ * (Qᵀ * C))).trace = (H * Cᵀ * Qᵀ * C).trace := by
      congr 1
      noncomm_ring
    _ = (C * (H * Cᵀ * Qᵀ)).trace := Matrix.trace_mul_comm _ _
    _ = (C * H * Cᵀ * Qᵀ).trace := by congr 1; noncomm_ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarChartDrift (g : SmoothMetric M) (c : M) (z : FourSpace) : Fin 4 → ℝ :=
  fun a => ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j * christoffel g c z a i j

theorem scalarChartOperator_eq_contraction (g : SmoothMetric M) (c : M)
    (ψ : FourSpace → ℝ) (z : FourSpace) :
    scalarChartOperator g c ψ z =
      scalarPrincipalContraction (metricInChart g c z)⁻¹ (scalarPartialMatrix ψ z) -
        scalarChartDrift g c z ⬝ᵥ scalarPartialVector ψ z := by
  have hs : (∑ a, (∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
      christoffel g c z a i j) * partialDeriv ψ a z) =
      ∑ i, ∑ j, (metricInChart g c z)⁻¹ i j *
        (∑ a, christoffel g c z a i j * partialDeriv ψ a z) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  simp only [scalarChartOperator, scalarPrincipalContraction, scalarPartialMatrix,
    scalarChartDrift, scalarPartialVector, dotProduct, mul_sub, Finset.sum_sub_distrib]
  rw [hs]

theorem scalarChartOperator_affine (g : SmoothMetric M) (c : M)
    (C : Mat4) (q z : FourSpace) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    scalarChartOperator g c (fun w => ψ (scalarAffineMap C q w)) z =
      scalarPrincipalContraction (C * (metricInChart g c z)⁻¹ * Cᵀ)
        (scalarPartialMatrix ψ (scalarAffineMap C q z)) -
      (C *ᵥ scalarChartDrift g c z) ⬝ᵥ scalarPartialVector ψ (scalarAffineMap C q z) := by
  rw [scalarChartOperator_eq_contraction, scalarAffineMap_partialMatrix C q z ψ hψ,
    scalarPrincipalContraction_affine, scalarAffineMap_partialVector C q z ψ hψ,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual invertible affine map used to rescale a metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarRescalingLinearEquiv (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (hr : r ≠ 0) : FourSpace ≃L[ℝ] FourSpace :=
  ContinuousLinearEquiv.equivOfInverse
    (r • (frozenFrameLinearEquiv g c z₀).toContinuousLinearMap)
    (r⁻¹ • (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap)
    (by intro x; simp [smul_smul, hr])
    (by intro x; simp [smul_smul, hr])

theorem scalarRescalingLinearEquiv_apply (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (y : FourSpace) :
    scalarRescalingLinearEquiv g c z₀ r hr y + z₀ = scalarRescaledPoint g c z₀ r y := by
  change r • (frozenFrameLinearEquiv g c z₀ y) + z₀ = _
  rw [scalarRescaledPoint, add_comm]
  rfl

theorem scalarRescalingLinearEquiv_symm_apply (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (z : FourSpace) :
    (scalarRescalingLinearEquiv g c z₀ r hr).symm z =
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
        (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) z := by
  change r⁻¹ • (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap z = _
  rw [frozenFrameLinearEquiv_symm_matrix, map_smul]
  rfl

theorem scalarRescaling_inverse_affine (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (z : FourSpace) :
    (scalarRescalingLinearEquiv g c z₀ r hr).symm (z - z₀) =
      scalarAffineMap (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹)
        (-((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
          (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) z₀)) z := by
  rw [scalarRescalingLinearEquiv_symm_apply, map_sub]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact transformation of the geometric chart Laplacian under the
constructed frozen-frame rescaling. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarRescaledOperator (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (ψ : FourSpace → ℝ) (y : FourSpace) : ℝ :=
  scalarPrincipalContraction (scalarRescaledPrincipal g c z₀ r y)
    (scalarPartialMatrix ψ y) +
    scalarRescaledDrift g c z₀ r y ⬝ᵥ scalarPartialVector ψ y

theorem scalarRescaledOperator_eq_zero_off_tsupport (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (ψ : FourSpace → ℝ) {y : FourSpace}
    (hy : y ∉ tsupport ψ) : scalarRescaledOperator g c z₀ r ψ y = 0 := by
  have hfirst (i : Fin 4) : partialDeriv ψ i y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy
      (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h))
  have hsecond (i j : Fin 4) : partialDeriv (fun z => partialDeriv ψ j z) i y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy
      (tsupport_fderiv_apply_subset ℝ (coordinateVector j)
        (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h)))
  simp only [scalarRescaledOperator, scalarPrincipalContraction, scalarPartialMatrix,
    scalarPartialVector, dotProduct, hfirst, hsecond, mul_zero, Finset.sum_const_zero, add_zero]

theorem scalarContraction_smul (s : ℝ) (H Q : Mat4) :
    scalarPrincipalContraction (s • H) Q = s * scalarPrincipalContraction H Q := by
  simp only [scalarPrincipalContraction, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem scalarRescaling_principal (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (z : FourSpace) :
    r ^ 2 • ((r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) *
      (metricInChart g c z)⁻¹ * (r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹)ᵀ) =
      frozenScalarPrincipal g c z₀ z := by
  rw [frozenScalarPrincipal_eq_conjugate]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h : r ^ 2 * (r⁻¹ * r⁻¹) = 1 := by field_simp [hr]
  rw [h, one_smul]

theorem scalarRescaling_drift (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (y : FourSpace) :
    r ^ 2 • ((r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹) *ᵥ
      scalarChartDrift g c (scalarRescaledPoint g c z₀ r y)) =
        -scalarRescaledDrift g c z₀ r y := by
  funext j
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.smul_apply, Pi.neg_apply, scalarRescaledDrift, scalarFrozenDrift,
    scalarChartDrift, mul_assoc]
  rw [← Finset.mul_sum]
  have h : r ^ 2 * r⁻¹ = r := by field_simp [hr]
  simp only [← mul_assoc, h, mul_neg, neg_neg]

theorem scalarRescaledOperator_eq_chart (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (y : FourSpace) :
    r ^ 2 * scalarChartOperator g c
      (fun z => ψ ((scalarRescalingLinearEquiv g c z₀ r hr).symm (z - z₀)))
      (scalarRescaledPoint g c z₀ r y) = scalarRescaledOperator g c z₀ r ψ y := by
  let C : Mat4 := r⁻¹ • (chartGramMatrix g c 1 z₀)⁻¹
  let q := -((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C z₀)
  have he : (fun z => ψ ((scalarRescalingLinearEquiv g c z₀ r hr).symm (z - z₀))) =
      fun z => ψ (scalarAffineMap C q z) := by
    funext z
    rw [scalarRescaling_inverse_affine]
  have hy : scalarAffineMap C q (scalarRescaledPoint g c z₀ r y) = y := by
    rw [← scalarRescaling_inverse_affine g c z₀ r hr,
      ← scalarRescalingLinearEquiv_apply g c z₀ r hr y, add_sub_cancel_right]
    exact ContinuousLinearEquiv.symm_apply_apply _ y
  rw [he, scalarChartOperator_affine g c C q _ ψ hψ, hy, mul_sub,
    ← scalarContraction_smul, scalarRescaling_principal g c z₀ r hr]
  have hd := congrArg (fun v : Fin 4 → ℝ => v ⬝ᵥ scalarPartialVector ψ y)
    (scalarRescaling_drift g c z₀ r hr y)
  rw [smul_dotProduct, neg_dotProduct] at hd
  simp only [smul_eq_mul] at hd
  change scalarPrincipalContraction (scalarRescaledPrincipal g c z₀ r y)
    (scalarPartialMatrix ψ y) - _ = _
  rw [hd]
  exact sub_neg_eq_add _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Multiplying a local L² representative by a compact cutoff gives a
genuine global L² function, independent of its values off the local set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

theorem scalarLocalL2_product_memLp {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) :
    MemLp (fun z => χ z * f z) 2 volume := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  have hp : MemLp (fun z => χ z * f z) 2 (volume.restrict K) := by
    apply (Lp.memLp f).of_le_mul (c := C)
      (hχ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    filter_upwards with z
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC (χ z) (mem_range_self z)) (norm_nonneg _)
  have heq : K.indicator (fun z => χ z * f z) = (fun z => χ z * f z) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hs ((subset_tsupport χ) (left_ne_zero_of_mul hz))
  rw [← heq]
  exact (memLp_indicator_iff_restrict hK).mpr hp

def scalarLocalL2Product {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) : Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarLocalL2_product_memLp hK χ hχ hc hs f).toLp _

theorem scalarLocalL2Product_coe {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) :
    scalarLocalL2Product hK χ hχ hc hs f =ᵐ[volume] (fun z => χ z * f z) :=
  MemLp.coeFn_toLp (scalarLocalL2_product_memLp hK χ hχ hc hs f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical L4 estimate for the first derivatives of an H2 distribution.
The compactly supported Gagliardo--Nirenberg estimate is extended by cutoffs;
Schwartz approximation is then taken through the actual L2 Bessel inverse. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter Set FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

theorem h2_compact_critical (f : V → ℂ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    eLpNorm f 4 volume ≤ (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
      eLpNorm (fderiv ℝ f) 2 volume := by
  simpa [ScalarEuclideanSobolev.constant] using
    (eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure V) hf hc
      (p := 2) (p' := 4) (by norm_num) (by simp) (by norm_num))

theorem h2_cutoff_L4_bound (f : 𝓢(V, ℂ)) (n : ℕ) :
    eLpNorm (fun x => h2Cutoff n x • f x) 4 volume ≤
      (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
        (ENNReal.ofReal h2BumpDerivativeBound * eLpNorm f 2 volume +
          ∑ i : Fin 4, eLpNorm ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f : 𝓢(V, ℂ)) : V → ℂ) 2 volume) := by
  have hg : ContDiff ℝ 1 (fun x => h2Cutoff n x • f x) :=
    ((h2Cutoff_smooth n).of_le (by first | simp | exact_mod_cast le_top)).smul (f.smooth 1)
  exact (h2_compact_critical _ hg (h2Cutoff_compact n).smul_right).trans
    (mul_le_mul_of_nonneg_left (h2_cutoff_L2_derivative f n) (by positivity))

/-- A fixed inhomogeneous critical estimate for Schwartz functions. -/
theorem scalar_schwartz_L4_bound (f : 𝓢(V, ℂ)) :
    eLpNorm f 4 volume ≤
      (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
        (ENNReal.ofReal h2BumpDerivativeBound * eLpNorm f 2 volume +
          ∑ i : Fin 4, eLpNorm ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f : 𝓢(V, ℂ)) : V → ℂ) 2 volume) := by
  apply Lp.eLpNorm_le_of_ae_tendsto (f := fun n x => h2Cutoff n x • f x)
    (Filter.Eventually.of_forall (h2_cutoff_L4_bound f))
    (fun n => ((h2Cutoff_smooth n).continuous.smul f.continuous).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by
      simpa only [one_smul] using (h2Cutoff_tendsto x).smul_const (f x)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport between the measurable structure on FourSpace and its equal
Borel structure, preserving functions and Lebesgue measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ENNReal

noncomputable section

abbrev scalarBorelLp (F : Type*) [NormedAddCommGroup F] (p : ℝ≥0∞) : Type _ := by
  letI : MeasurableSpace FourSpace := borel FourSpace
  letI : BorelSpace FourSpace := ⟨rfl⟩
  letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
  exact ↥(Lp F p (volume : Measure FourSpace))

def scalarBorelLpEquivAux (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : MeasurableSpace FourSpace)
    (hm : m = borel FourSpace) :
    (letI : MeasurableSpace FourSpace := m
     letI : BorelSpace FourSpace := ⟨hm⟩
     letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
     Lp F p (volume : Measure FourSpace)) ≃ₗᵢ[ℝ] scalarBorelLp F p := by
  subst m
  exact LinearIsometryEquiv.refl ℝ _

def scalarBorelLpEquiv (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp F p (volume : Measure FourSpace) ≃ₗᵢ[ℝ] scalarBorelLp F p :=
  scalarBorelLpEquivAux F p inferInstance BorelSpace.measurable_eq

theorem scalarBorelLpEquivAux_ae (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p : ℝ≥0∞) [Fact (1 ≤ p)] (m : MeasurableSpace FourSpace)
    (hm : m = borel FourSpace)
    (u : (letI : MeasurableSpace FourSpace := m
          letI : BorelSpace FourSpace := ⟨hm⟩
          letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
          Lp F p (volume : Measure FourSpace))) (f : FourSpace → F)
    (hu : letI : MeasurableSpace FourSpace := m
          letI : BorelSpace FourSpace := ⟨hm⟩
          letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
          (u : FourSpace → F) =ᵐ[volume] f) :
    letI : MeasurableSpace FourSpace := borel FourSpace
    letI : BorelSpace FourSpace := ⟨rfl⟩
    letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
    (scalarBorelLpEquivAux F p m hm u : FourSpace → F) =ᵐ[volume] f := by
  subst m
  exact hu

/-- Almost-everywhere representatives are unchanged by the transport. -/
theorem scalarBorelLpEquiv_ae (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Lp F p (volume : Measure FourSpace))
    (f : FourSpace → F) (hu : (u : FourSpace → F) =ᵐ[volume] f) :
    letI : MeasurableSpace FourSpace := borel FourSpace
    letI : BorelSpace FourSpace := ⟨rfl⟩
    letI : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace
    (scalarBorelLpEquiv F p u : FourSpace → F) =ᵐ[volume] f :=
  scalarBorelLpEquivAux_ae F p inferInstance BorelSpace.measurable_eq u f hu

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
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

omit [T3Space M] in
theorem twoFormLocalNabla_zero_off (c : M) (S : Mat4) (a : FourSpace → TwoFormFour)
    (z : FourSpace) (hz : z ∉ tsupport a) (i : Fin 4) :
    twoFormLocalNabla (g := g) c S a i z = 0 := by
  have he : a =ᶠ[𝓝 z] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  unfold twoFormLocalNabla
  rw [he.fderiv_eq, he.self_of_nhds]
  simp only [fderiv_const_apply, _root_.zero_apply, zero_add]
  change (twoFormSkewActionLinear (twoFormExtract (chartTwoFormConnection (g := g) c S i z))) 0 = 0
  exact map_zero _

end
end PositiveEinsteinFour.Geometry
end


section

/-! An intrinsic continuous scalar controls the local first jet of a
smooth two-form. Its L2 norm is bounded by twice the actual H1 norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormControl_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def twoFormValueNorm (u : smoothTwoForms o) : C(M, ℝ) :=
  ⟨fun x => ‖u.val x‖, smoothTwoForm_norm_continuous u⟩

def twoFormEnergyRoot (u : smoothTwoForms o) : C(M, ℝ) :=
  ⟨fun x => Real.sqrt (twoFormCovariantPairing o u.val u.val x),
    Real.continuous_sqrt.comp (u.property.covariantPairing_continuous u.property)⟩

def twoFormControl (u : smoothTwoForms o) : C(M, ℝ) := twoFormValueNorm u + twoFormEnergyRoot u

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem twoFormControl_nonneg (u : smoothTwoForms o) (x : M) : 0 ≤ twoFormControl u x := by
  change 0 ≤ ‖u.val x‖ + Real.sqrt (twoFormCovariantPairing o u.val u.val x)
  positivity

def twoFormValueNormL2 (u : smoothTwoForms o) : Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormValueNorm u)

def twoFormEnergyRootL2 (u : smoothTwoForms o) : Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormEnergyRoot u)

def twoFormControlL2 (u : smoothTwoForms o) : Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormControl u)

theorem twoFormValueNormL2_coe (u : smoothTwoForms o) :
    twoFormValueNormL2 u =ᵐ[normalizedVolume g] fun x => ‖u.val x‖ :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) (twoFormValueNorm u)

theorem twoFormValueNormL2_norm_sq (u : smoothTwoForms o) :
    ‖twoFormValueNormL2 u‖ ^ 2 = smoothTwoFormL2Inner u u := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormValueNorm u))
    (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormValueNorm u)) = _
  rw [ContinuousMap.inner_toLp, smoothTwoFormL2Inner_self]
  apply integral_congr_ae
  filter_upwards [] with x
  change ‖u.val x‖ * ‖u.val x‖ = ‖u.val x‖ ^ 2
  ring

theorem twoFormEnergyRootL2_norm_sq (u : smoothTwoForms o) :
    ‖twoFormEnergyRootL2 u‖ ^ 2 = smoothTwoFormCovariantEnergy u u := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormEnergyRoot u))
    (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (twoFormEnergyRoot u)) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with x
  change Real.sqrt (twoFormCovariantPairing o u.val u.val x) *
    Real.sqrt (twoFormCovariantPairing o u.val u.val x) = _
  rw [← pow_two, Real.sq_sqrt (twoFormCovariantPairing_self_nonneg o u.val x)]

theorem twoFormControlL2_norm_le (u : SmoothH1TwoForm o) :
    ‖twoFormControlL2 (u : smoothTwoForms o)‖ ≤ 2 * ‖u‖ := by
  have hv : ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h₁ := twoFormValueNormL2_norm_sq (u : smoothTwoForms o)
    have h₂ := smoothH1TwoForm_norm_sq u
    have h₃ := smoothTwoFormCovariantEnergy_nonneg (u : smoothTwoForms o)
    linarith only [h₁, h₂, h₃]
  have he : ‖twoFormEnergyRootL2 (u : smoothTwoForms o)‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have h₁ := twoFormEnergyRootL2_norm_sq (u : smoothTwoForms o)
    have h₂ := smoothH1TwoForm_norm_sq u
    have h₃ := smoothTwoFormL2Inner_nonneg (u : smoothTwoForms o)
    linarith only [h₁, h₂, h₃]
  have hid : twoFormControlL2 (u : smoothTwoForms o) =
      twoFormValueNormL2 (u : smoothTwoForms o) + twoFormEnergyRootL2 (u : smoothTwoForms o) :=
    map_add (ContinuousMap.toLp 2 (normalizedVolume g) ℝ) _ _
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hv he).trans_eq (by ring))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded extension of the metric's actual curvature action to L2
two-forms. No bound on curvature is an additional input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormValueNormL2_eq_L2norm (u : SmoothL2TwoForm o) :
    ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := twoFormValueNormL2_norm_sq (u : smoothTwoForms o)
  have hi : ‖u‖ ^ 2 = smoothTwoFormL2Inner (u : smoothTwoForms o) u := by
    rw [← real_inner_self_eq_norm_sq]
    rfl
  exact h.trans hi.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer of the intrinsic two-form H1 control to supported scalar
functions on a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormLocalization_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Real coordinate L² functions and their weak derivatives embed into
the complex tempered distributions used by the elliptic inverse. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Manifold ContDiff

noncomputable section

def scalarComplexL2 (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    Lp ℂ 2 (volume : Measure FourSpace) := Complex.ofRealCLM.compLp f

theorem scalarComplexL2_coe (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarComplexL2 f =ᵐ[volume] (fun x => (f x : ℂ)) :=
  Complex.ofRealCLM.coeFn_compLp f

theorem scalarComplexL2_pairing_re (f : Lp ℝ 2 (volume : Measure FourSpace))
    (φ : 𝓢(FourSpace, ℂ)) :
    ((scalarComplexL2 f : 𝓢'(FourSpace, ℂ)) φ).re = ∫ x, f x * (φ x).re := by
  have hi := (φ.memLp 2 (volume : Measure FourSpace)).integrable_mul
    (Lp.memLp (scalarComplexL2 f))
  rw [Lp.toTemperedDistribution_apply]
  change (∫ x, φ x * scalarComplexL2 f x).re = _
  have he : (∫ x, φ x * scalarComplexL2 f x).re =
      ∫ x, (φ x * scalarComplexL2 f x).re := (integral_re hi).symm
  rw [he]
  apply integral_congr_ae
  filter_upwards [scalarComplexL2_coe f] with x hx
  rw [hx]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem scalarComplexL2_pairing_im (f : Lp ℝ 2 (volume : Measure FourSpace))
    (φ : 𝓢(FourSpace, ℂ)) :
    ((scalarComplexL2 f : 𝓢'(FourSpace, ℂ)) φ).im = ∫ x, f x * (φ x).im := by
  have hi := (φ.memLp 2 (volume : Measure FourSpace)).integrable_mul
    (Lp.memLp (scalarComplexL2 f))
  rw [Lp.toTemperedDistribution_apply]
  change (∫ x, φ x * scalarComplexL2 f x).im = _
  have he : (∫ x, φ x * scalarComplexL2 f x).im =
      ∫ x, (φ x * scalarComplexL2 f x).im := (integral_im hi).symm
  rw [he]
  apply integral_congr_ae
  filter_upwards [scalarComplexL2_coe f] with x hx
  rw [hx]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem scalarSchwartz_real_partial (L : ℂ →L[ℝ] ℝ) (φ : 𝓢(FourSpace, ℂ))
    (i : Fin 4) (x : FourSpace) :
    partialDeriv (fun y => L (φ y)) i x =
      L ((scalarSchwartzCoordinateDerivative i φ) x) := by
  change (fderiv ℝ (L ∘ φ) x) (coordinateVector i) =
    L ((fderiv ℝ φ x) (EuclideanSpace.basisFun (Fin 4) ℝ i))
  rw [_root_.fderiv_comp (f := (φ : FourSpace → ℂ)) (g := (L : ℂ → ℝ))
    x L.differentiableAt φ.differentiableAt, L.fderiv]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply, coordinateVector]

theorem scalarComplexL2_weak_derivative
    (f g : Lp ℝ 2 (volume : Measure FourSpace)) (i : Fin 4)
    (hw : ∀ q : 𝓢(FourSpace, ℝ),
      (∫ x, f x * partialDeriv q i x) = -(∫ x, g x * q x)) :
    scalarCoordinateDerivative i (scalarComplexL2 f : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 g : 𝓢'(FourSpace, ℂ)) := by
  ext φ
  change (scalarComplexL2 f : 𝓢'(FourSpace, ℂ))
    (-scalarSchwartzCoordinateDerivative i φ) = _
  rw [map_neg]
  apply Complex.ext
  · rw [Complex.neg_re, scalarComplexL2_pairing_re, scalarComplexL2_pairing_re]
    have h := hw (φ.postcompCLM Complex.reCLM)
    have he (x : FourSpace) : partialDeriv (fun y => (φ y).re) i x =
        ((scalarSchwartzCoordinateDerivative i φ) x).re :=
      scalarSchwartz_real_partial Complex.reCLM φ i x
    change (∫ x, f x * partialDeriv (fun y => (φ y).re) i x) =
      -(∫ x, g x * (φ x).re) at h
    simp_rw [he] at h
    linarith

  · rw [Complex.neg_im, scalarComplexL2_pairing_im, scalarComplexL2_pairing_im]
    have h := hw (φ.postcompCLM Complex.imCLM)
    have he (x : FourSpace) : partialDeriv (fun y => (φ y).im) i x =
        ((scalarSchwartzCoordinateDerivative i φ) x).im :=
      scalarSchwartz_real_partial Complex.imCLM φ i x
    change (∫ x, f x * partialDeriv (fun y => (φ y).im) i x) =
      -(∫ x, g x * (φ x).im) at h
    simp_rw [he] at h
    linarith


end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact smooth extensions of the actual rescaled metric coefficients.
Their values and first two derivatives become uniformly small as the chart
scale tends to zero, including outside the cutoff support. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology SchwartzMap

noncomputable section

theorem scalarCutoff_contDiff (χ f : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ (fun y => χ y * f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf y hy)
  · have hz : (fun z => χ z * f z) =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp only [hz, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hz

def scalarCutoffSchwartz (χ f : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ f y) :
    𝓢(FourSpace, ℂ) :=
  (hc.mul_right.comp_left (show Complex.ofReal 0 = 0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (scalarCutoff_contDiff χ f hχ hf))

theorem scalarCutoffSchwartz_apply (χ f : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ f y)
    (y : FourSpace) : scalarCutoffSchwartz χ f hχ hc hf y = (χ y * f y : ℝ) := rfl

theorem scalarCutoffParameter_jets_uniform (F : ℝ → FourSpace → ℝ)
    {K : Set FourSpace} (hK : IsCompact K)
    (hF : ∀ y ∈ K, ContDiffAt ℝ ∞ (Function.uncurry F) (0, y))
    (hzero : ∀ y, F 0 y = 0) (hs : ∀ r, tsupport (F r) ⊆ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r, |r| < η → ∀ y,
      |F r y| < ε ∧ (∀ i, |partialDeriv (F r) i y| < ε) ∧
      (∀ i j, |partialDeriv (fun z => partialDeriv (F r) j z) i y| < ε) := by
  obtain ⟨η, hη, hb⟩ := scalarParameter_jets_uniform F hK 0 hF hzero ε hε
  refine ⟨η, hη, ?_⟩
  intro r hr y
  by_cases hy : y ∈ K
  · simpa only [sub_zero] using hb r hr y hy
  · have hval : F r y = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hy (hs r ht))
    have hder (i : Fin 4) : partialDeriv (F r) i y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hy
        (hs r ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) ht)))
    have hsecond (i j : Fin 4) :
        partialDeriv (fun z => partialDeriv (F r) j z) i y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hy
        (hs r ((tsupport_fderiv_apply_subset ℝ (coordinateVector j))
          ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) ht))))
    simp only [hval, hder, hsecond, abs_zero]
    exact ⟨hε, fun _ => hε, fun _ _ => hε⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarCutoffPrincipal (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (χ : FourSpace → ℝ) (r : ℝ) (i j : Fin 4) (y : FourSpace) : ℝ :=
  χ y * (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j)

def scalarCutoffDrift (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (χ : FourSpace → ℝ) (r : ℝ) (i : Fin 4) (y : FourSpace) : ℝ :=
  χ y * scalarRescaledDrift g c z₀ r y i

theorem scalarCutoffPrincipal_jets_uniform (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (i j : Fin 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r, |r| < η → ∀ y,
      |scalarCutoffPrincipal g c z₀ χ r i j y| < ε ∧
      (∀ k, |partialDeriv (scalarCutoffPrincipal g c z₀ χ r i j) k y| < ε) ∧
      (∀ k l, |partialDeriv
        (fun z => partialDeriv (scalarCutoffPrincipal g c z₀ χ r i j) l z) k y| < ε) := by
  apply scalarCutoffParameter_jets_uniform _ hc _ _ _ ε hε
  · intro y _
    apply (hχ.contDiffAt.comp (0, y) contDiffAt_snd).mul
    exact (scalarRescaled_function_contDiffAt g c z₀ _
      (frozenScalarPrincipal_contDiffAt g c z₀ z₀ z₀.property i j) y).sub contDiffAt_const
  · intro y
    simp only [scalarCutoffPrincipal, scalarRescaledPrincipal_zero, sub_self, mul_zero]
  · intro r
    exact tsupport_mul_subset_left

theorem scalarCutoffDrift_jets_uniform (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (i : Fin 4) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ r, |r| < η → ∀ y,
      |scalarCutoffDrift g c z₀ χ r i y| < ε ∧
      (∀ k, |partialDeriv (scalarCutoffDrift g c z₀ χ r i) k y| < ε) ∧
      (∀ k l, |partialDeriv
        (fun z => partialDeriv (scalarCutoffDrift g c z₀ χ r i) l z) k y| < ε) := by
  apply scalarCutoffParameter_jets_uniform _ hc _ _ _ ε hε
  · intro y _
    apply (hχ.contDiffAt.comp (0, y) contDiffAt_snd).mul
    exact contDiffAt_fst.mul (scalarRescaled_function_contDiffAt g c z₀ _
      (scalarFrozenDrift_contDiffAt g c z₀ z₀ z₀.property i) y)
  · intro y
    simp only [scalarCutoffDrift, scalarRescaledDrift, zero_mul, mul_zero]
  · intro r
    exact tsupport_mul_subset_left

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded cutoff multiplication from a chart L² space into Euclidean L².
These maps keep the actual local representatives used by the weak equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem scalarLocalL2Product_bound {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ 2 (volume.restrict K),
      ‖scalarLocalL2Product hK χ hχ hc hs f‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun f => ?_⟩
  have heq : K.indicator (fun z => χ z * f z) = (fun z => χ z * f z) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hs ((subset_tsupport χ) (left_ne_zero_of_mul hz))
  have hb : eLpNorm (fun z => χ z * f z) 2 volume ≤
      ENNReal.ofReal (max C 0) * eLpNorm f 2 (volume.restrict K) := by
    rw [← heq, eLpNorm_indicator_eq_eLpNorm_restrict hK]
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards with z
    first | rw [Pi.mul_apply, norm_mul] | rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((hC (χ z) (mem_range_self z)).trans (le_max_left _ _)) (norm_nonneg _)
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) hb
  change ‖(scalarLocalL2_product_memLp hK χ hχ hc hs f).toLp _‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_max_right C 0)] using hr

theorem scalarLocalL2Product_ae_congr {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hs : tsupport χ ⊆ K) {f h : FourSpace → ℝ}
    (he : f =ᵐ[volume.restrict K] h) :
    (fun z => χ z * f z) =ᵐ[volume] (fun z => χ z * h z) := by
  have hl : (fun z => χ z * f z) =ᵐ[volume.restrict K] (fun z => χ z * h z) :=
    he.mono (fun z hz => congrArg (χ z * ·) hz)
  have hi := (ae_eq_restrict_iff_indicator_ae_eq hK).mp hl
  have hzero (q : FourSpace → ℝ) :
      K.indicator (fun z => χ z * q z) = (fun z => χ z * q z) := by
    apply indicator_eq_self.mpr
    intro z hz
    exact hs ((subset_tsupport χ) (left_ne_zero_of_mul hz))
  simpa only [hzero] using hi

def scalarLocalL2ProductLinear {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    Lp ℝ 2 (volume.restrict K) →ₗ[ℝ] Lp ℝ 2 (volume : Measure FourSpace) where
  toFun := scalarLocalL2Product hK χ hχ hc hs
  map_add' f h := by
    apply Lp.ext
    have he := scalarLocalL2Product_ae_congr hK χ hs (Lp.coeFn_add f h)
    filter_upwards [scalarLocalL2Product_coe hK χ hχ hc hs (f + h),
      scalarLocalL2Product_coe hK χ hχ hc hs f,
      scalarLocalL2Product_coe hK χ hχ hc hs h,
      Lp.coeFn_add (scalarLocalL2Product hK χ hχ hc hs f)
        (scalarLocalL2Product hK χ hχ hc hs h), he] with z hsum hf hh hLp hz
    rw [hsum, hLp, Pi.add_apply, hf, hh]
    simpa only [Pi.add_apply, mul_add] using hz
  map_smul' r f := by
    apply Lp.ext
    have he := scalarLocalL2Product_ae_congr hK χ hs (Lp.coeFn_smul r f)
    filter_upwards [scalarLocalL2Product_coe hK χ hχ hc hs (r • f),
      scalarLocalL2Product_coe hK χ hχ hc hs f,
      Lp.coeFn_smul r (scalarLocalL2Product hK χ hχ hc hs f), he] with z hrf hf hLp hz
    simp only [RingHom.id_apply]
    rw [hrf, hLp, Pi.smul_apply, hf]
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm] using hz

def scalarLocalL2ProductCLM {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    Lp ℝ 2 (volume.restrict K) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarLocalL2ProductLinear hK χ hχ hc hs).mkContinuousOfExistsBound (by
    obtain ⟨C, _, hC⟩ := scalarLocalL2Product_bound hK χ hχ hc hs
    exact ⟨C, hC⟩)

theorem scalarLocalL2ProductCLM_coe {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) :
    scalarLocalL2ProductCLM hK χ hχ hc hs f =ᵐ[volume] (fun z => χ z * f z) :=
  scalarLocalL2Product_coe hK χ hχ hc hs f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Extracting the real compact-test identity from an equality of complex
L2 distributional derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

noncomputable section

theorem scalarComplexL2_compact_weak_derivative
    (f D : Lp ℝ 2 (volume : Measure FourSpace)) (i : Fin 4)
    (hD : scalarCoordinateDerivative i (scalarComplexL2 f : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, f z * partialDeriv ψ i z) = -(∫ z, D z * ψ z) := by
  let φ : 𝓢(FourSpace, ℂ) := (hcψ.toSchwartzMap hψ).postcompCLM Complex.ofRealCLM
  have he := congrArg (fun T : 𝓢'(FourSpace, ℂ) => (T φ).re) hD
  change ((scalarComplexL2 f : 𝓢'(FourSpace, ℂ))
    (-scalarSchwartzCoordinateDerivative i φ)).re =
    ((scalarComplexL2 D : 𝓢'(FourSpace, ℂ)) φ).re at he
  rw [map_neg, Complex.neg_re, scalarComplexL2_pairing_re, scalarComplexL2_pairing_re] at he
  have hp (z : FourSpace) : ((scalarSchwartzCoordinateDerivative i φ) z).re =
      partialDeriv ψ i z := by
    exact (scalarSchwartz_real_partial Complex.reCLM φ i z).symm
  simp_rw [hp] at he
  change -(∫ z, f z * partialDeriv ψ i z) = ∫ z, D z * ψ z at he
  linarith only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real components of the actual complex distributional test pairing.
Only the compactly localized source must be smooth and integrable. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)

theorem scalarComplexL2_pairing_component (w : Lp ℝ 2 (volume : Measure V))
    (L : ℂ →L[ℝ] ℝ) (φ : S) :
    L ((scalarComplexL2 w : 𝓢'(V, ℂ)) φ) = ∫ x, w x * L (φ x) := by
  have hi := (φ.memLp 2 (volume : Measure V)).integrable_mul
    (Lp.memLp (scalarComplexL2 w))
  change Integrable (fun x => φ x * scalarComplexL2 w x) volume at hi
  rw [Lp.toTemperedDistribution_apply]
  change L (∫ x, φ x * scalarComplexL2 w x) = _
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [scalarComplexL2_coe w] with x hx
  rw [hx, mul_comm (φ x), ← Complex.real_smul, L.map_smul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real small-jet bounds for compact metric coefficients are exactly
the complex Schwartz derivative bounds used by the elliptic estimates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff SchwartzMap

noncomputable section

theorem scalarComplex_partial (f : FourSpace → ℝ) (x : FourSpace)
    (hf : DifferentiableAt ℝ f x) (i : Fin 4) :
    (fderiv ℝ (fun y => (f y : ℂ)) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) =
      (partialDeriv f i x : ℂ) := by
  change (fderiv ℝ (Complex.ofRealCLM ∘ f) x)
    (EuclideanSpace.basisFun (Fin 4) ℝ i) = _
  rw [_root_.fderiv_comp (f := f) (g := (Complex.ofRealCLM : ℝ → ℂ))
    x Complex.ofRealCLM.differentiableAt hf, Complex.ofRealCLM.fderiv]
  simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.basisFun_apply, partialDeriv, coordinateVector, Complex.ofRealCLM_apply]

theorem scalarCutoffSchwartz_first (χ f : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ f y)
    (i : Fin 4) (x : FourSpace) :
    scalarSchwartzCoordinateDerivative i (scalarCutoffSchwartz χ f hχ hc hf) x =
      (partialDeriv (fun y => χ y * f y) i x : ℂ) := by
  change (fderiv ℝ (fun y => ((χ y * f y : ℝ) : ℂ)) x)
    (EuclideanSpace.basisFun (Fin 4) ℝ i) = _
  exact scalarComplex_partial _ x
    ((scalarCutoff_contDiff χ f hχ hf).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) i

theorem scalarCutoffSchwartz_second (χ f : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ f y)
    (i j : Fin 4) (x : FourSpace) :
    scalarSchwartzCoordinateDerivative i
      (scalarSchwartzCoordinateDerivative j (scalarCutoffSchwartz χ f hχ hc hf)) x =
      (partialDeriv (fun y => partialDeriv (fun z => χ z * f z) j y) i x : ℂ) := by
  have he : (fun y => scalarSchwartzCoordinateDerivative j
      (scalarCutoffSchwartz χ f hχ hc hf) y) =
        fun y => (partialDeriv (fun z => χ z * f z) j y : ℂ) :=
    funext (scalarCutoffSchwartz_first χ f hχ hc hf j)
  change (fderiv ℝ (fun y => scalarSchwartzCoordinateDerivative j
    (scalarCutoffSchwartz χ f hχ hc hf) y) x)
      (EuclideanSpace.basisFun (Fin 4) ℝ i) = _
  rw [he]
  apply scalarComplex_partial
  exact (((scalarCutoff_contDiff χ f hχ hf).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    (contDiff_const (c := coordinateVector j))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x

theorem scalarCutoffSchwartz_jet_bounds (χ f : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hf : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ f y)
    (δ : ℝ)
    (h₀ : ∀ x, |χ x * f x| ≤ δ)
    (h₁ : ∀ i x, |partialDeriv (fun y => χ y * f y) i x| ≤ δ)
    (h₂ : ∀ i j x, |partialDeriv
      (fun y => partialDeriv (fun z => χ z * f z) j y) i x| ≤ δ) :
    (∀ x, ‖scalarCutoffSchwartz χ f hχ hc hf x‖ ≤ δ) ∧
      (∀ i x, ‖scalarSchwartzCoordinateDerivative i
        (scalarCutoffSchwartz χ f hχ hc hf) x‖ ≤ δ) ∧
      (∀ i j x, ‖scalarSchwartzCoordinateDerivative i
        (scalarSchwartzCoordinateDerivative j (scalarCutoffSchwartz χ f hχ hc hf)) x‖ ≤ δ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa only [scalarCutoffSchwartz_apply, Complex.norm_real, Real.norm_eq_abs] using h₀ x
  · intro i x
    rw [scalarCutoffSchwartz_first, Complex.norm_real, Real.norm_eq_abs]
    exact h₁ i x
  · intro i j x
    rw [scalarCutoffSchwartz_second, Complex.norm_real, Real.norm_eq_abs]
    exact h₂ i j x

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded localization of the intrinsic scalar H¹ space into Euclidean
L⁴. The construction uses the actual chart representative and its four
weak derivatives, with a compact smooth cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instFactLeENNRealOfNat_solutions_3_rfb4d6b_1 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localSobolev_frameCompact
def scalarCutoffChartC1 (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    SmoothScalar (M := M) →ₗ[ℝ] ↥(Euclidean.C1c (E := FourSpace)) where
  toFun a := ⟨fun z => χ z * a.val ((chartAt FourSpace c).symm z),
    (scalarCutoff_contDiff χ _ hχ (fun z hz =>
      scalarCoordinates_contDiffAt a.property c z (hKt (hs hz))
        (fun j => Fin.elim0 j))).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hc.mul_right⟩
  map_add' a b := by
    ext z
    change χ z * (a.val _ + b.val _) = χ z * a.val _ + χ z * b.val _
    ring
  map_smul' r a := by
    ext z
    change χ z * (r * a.val _) = r * (χ z * a.val _)
    ring

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem scalarCutoffChart_partial (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : SmoothScalar (M := M)) (i : Fin 4) (z : FourSpace) :
    partialDeriv (scalarCutoffChartC1 c hKt χ hχ hc hs a).val i z =
      χ z * partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z +
        partialDeriv χ i z * a.val ((chartAt FourSpace c).symm z) := by
  by_cases hz : z ∈ K
  · have ha := (scalarCoordinates_contDiffAt a.property c z (hKt hz)
      (fun j => Fin.elim0 j)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change DifferentiableAt ℝ (fun w => a.val ((chartAt FourSpace c).symm w)) z at ha
    change partialDeriv (fun w => χ w * a.val ((chartAt FourSpace c).symm w)) i z = _
    rw [scalar_partial_product χ _ z (hχ.differentiable (by simp) z) ha]
    ring
  · have ht : z ∉ tsupport χ := fun hz' => hz (hs hz')
    have hzero : χ z = 0 := image_eq_zero_of_notMem_tsupport ht
    have hder : partialDeriv χ i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz' => ht
        ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) hz'))
    have hproduct : partialDeriv (scalarCutoffChartC1 c hKt χ hχ hc hs a).val i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hz' => ht
        (tsupport_mul_subset_left ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) hz')))
    rw [hproduct, hzero, hder, zero_mul, zero_mul, zero_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Affine pullback of the actual L2 function preserves first-order Sobolev
regularity.  The derivative identity is proved by changing variables in
Schwartz test integrals. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem scalarComplexAffinePullbackL2_memSobolev_one (A : V ≃L[ℝ] V) (q : V)
    (u : L2) (hu : MemSobolev 1 2 (u : T)) :
    MemSobolev 1 2 (scalarComplexAffinePullbackL2 A q u : T) := by
  rw [← scalarAffineDistribution_L2]
  exact scalarAffineDistribution_memSobolev_one A q u hu

theorem scalarComplexAffinePullbackL2_ofReal (A : V ≃L[ℝ] V) (q : V)
    (u : Lp ℝ 2 (volume : Measure V)) :
    scalarComplexAffinePullbackL2 A q (scalarComplexL2 u) =
      scalarComplexL2 (scalarAffinePullbackL2 A q u) := by
  have hq : Measure.QuasiMeasurePreserving (fun x => A x + q)
      (volume : Measure V) volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  apply Lp.ext
  filter_upwards [scalarComplexAffinePullbackL2_coe A q (scalarComplexL2 u),
    scalarComplexL2_coe (scalarAffinePullbackL2 A q u),
    scalarAffinePullbackL2_coe A q u, hq.ae_eq_comp (scalarComplexL2_coe u)]
      with x h₁ h₂ h₃ h₄
  change scalarComplexL2 u (A x + q) = (u (A x + q) : ℂ) at h₄
  rw [h₁, h₄, h₂, h₃]

/-- The real L2 affine pullback has the same H1 regularity after the
canonical complexification used by the distributional elliptic theory. -/
theorem scalarAffinePullbackL2_memSobolev_one (A : V ≃L[ℝ] V) (q : V)
    (u : Lp ℝ 2 (volume : Measure V))
    (hu : MemSobolev 1 2 (scalarComplexL2 u : T)) :
    MemSobolev 1 2 (scalarComplexL2 (scalarAffinePullbackL2 A q u) : T) := by
  rw [← scalarComplexAffinePullbackL2_ofReal]
  exact scalarComplexAffinePullbackL2_memSobolev_one A q _ hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Schwartz test operator is exactly the normalized scalar coordinate
operator, including its real and imaginary parts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian BigOperators

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

theorem scalar_direct_finite_algebra (κ : ℂ) (P : Mat4) (B : Fin 4 → ℝ)
    (Q : Fin 4 → Fin 4 → ℂ) (z : Fin 4 → ℂ) :
    -κ * (∑ i, Q i i) +
      (∑ i, ∑ j, (-κ * ((P i j : ℂ) - ((1 : Mat4) i j : ℂ))) * Q i j) +
      (∑ i, (-κ * (B i : ℂ)) * z i) =
    -κ * ((∑ i, ∑ j, (P i j : ℂ) * Q i j) + ∑ i, (B i : ℂ) * z i) := by
  have hid : (∑ i, ∑ j, ((1 : Mat4) i j : ℂ) * Q i j) = ∑ i, Q i i := by
    simp [Matrix.one_apply, apply_ite]
  have hsum : (∑ i, ∑ j, ((P i j : ℂ) - ((1 : Mat4) i j : ℂ)) * Q i j) =
      (∑ i, ∑ j, (P i j : ℂ) * Q i j) - ∑ i, Q i i := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [hid]
  have hsecond : (∑ i, ∑ j, (-κ * ((P i j : ℂ) - ((1 : Mat4) i j : ℂ))) * Q i j) =
      -κ * (∑ i, ∑ j, ((P i j : ℂ) - ((1 : Mat4) i j : ℂ)) * Q i j) := by
    simp only [Finset.mul_sum, mul_assoc]
  have hfirst : (∑ i, (-κ * (B i : ℂ)) * z i) = -κ * ∑ i, (B i : ℂ) * z i := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hsecond, hfirst, hsum]
  ring

/-- The normalization and identity-matrix correction recombine to the
actual principal matrix and drift at the point x. -/
theorem scalarSchwartzDirectOperator_coordinate (P : Mat4) (B : Fin 4 → ℝ)
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (φ : S) (x : V)
    (ha : ∀ i j, a i j x =
      ((-((2 * Real.pi) ^ 2)⁻¹ * (P i j - (1 : Mat4) i j) : ℝ) : ℂ))
    (hb : ∀ i, b i x = ((-((2 * Real.pi) ^ 2)⁻¹ * B i : ℝ) : ℂ)) :
    scalarSchwartzDirectOperator a b φ x - φ x =
      (-Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) *
        ((∑ i, ∑ j, (P i j : ℂ) * D i (D j φ) x) + ∑ i, (B i : ℂ) * D i φ x) := by
  have hΔ : (Δ φ) x = ∑ i : Fin 4, D i (D i φ) x := by
    have h := congrArg (fun ψ : S => ψ x)
      (SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ) φ)
    simpa only [sum_apply, scalarSchwartzCoordinateDerivative] using h
  simp only [scalarSchwartzDirectOperator, scalarSchwartzHelmholtz,
    add_apply, sub_apply, sum_apply, smul_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply (a _ _).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (b _).hasTemperateGrowth, hΔ,
    ha, hb, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_sub]
  have h := scalar_direct_finite_algebra
    (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) P B
    (fun i j => D i (D j φ) x) (fun i => D i φ x)
  linear_combination h

/-- Every term of the test operator is supported in the original test
support, regardless of the coefficient values outside it. -/
theorem scalarSchwartzDirectOperator_zero_off_tsupport
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (φ : S) (x : V)
    (hx : x ∉ tsupport (φ : V → ℂ)) :
    scalarSchwartzDirectOperator a b φ x - φ x = 0 := by
  have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hD (i : Fin 4) : D i φ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ((SchwartzMap.tsupport_lineDerivOp_subset
      (EuclideanSpace.basisFun (Fin 4) ℝ i) φ) h)
  have hD2 (i j : Fin 4) : D i (D j φ) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx ((SchwartzMap.tsupport_lineDerivOp_subset
      (EuclideanSpace.basisFun (Fin 4) ℝ j) φ)
      ((SchwartzMap.tsupport_lineDerivOp_subset
        (EuclideanSpace.basisFun (Fin 4) ℝ i) (D j φ)) h))
  have hΔ : (Δ φ) x = 0 := by
    rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 4) ℝ)]
    change (∑ i : Fin 4, D i (D i φ)) x = 0
    simp only [sum_apply, hD2, Finset.sum_const_zero]
  simp only [scalarSchwartzDirectOperator, scalarSchwartzHelmholtz,
    add_apply, sub_apply, sum_apply, smul_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply (a _ _).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (b _).hasTemperateGrowth,
    hφ, hD, hD2, hΔ, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

theorem scalarSchwartz_real_second_partial (L : ℂ →L[ℝ] ℝ) (φ : S)
    (i j : Fin 4) (x : V) :
    scalarPartialMatrix (L ∘ φ) x i j = L (D i (D j φ) x) := by
  have hfirst : (fun y => partialDeriv (L ∘ φ) j y) = fun y => L (D j φ y) := by
    funext y
    exact scalarSchwartz_real_partial L φ j y
  change partialDeriv (fun y => partialDeriv (L ∘ φ) j y) i x = _
  rw [hfirst]
  exact scalarSchwartz_real_partial L (D j φ) i x

/-- Any real-linear component, in particular real or imaginary part,
recovers the ordinary real scalar principal/drift expression. -/
theorem scalarSchwartzDirectOperator_real_coordinate (L : ℂ →L[ℝ] ℝ)
    (P : Mat4) (B : Fin 4 → ℝ) (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (φ : S) (x : V)
    (ha : ∀ i j, a i j x =
      ((-((2 * Real.pi) ^ 2)⁻¹ * (P i j - (1 : Mat4) i j) : ℝ) : ℂ))
    (hb : ∀ i, b i x = ((-((2 * Real.pi) ^ 2)⁻¹ * B i : ℝ) : ℂ)) :
    L (scalarSchwartzDirectOperator a b φ x - φ x) =
      -((2 * Real.pi) ^ 2)⁻¹ *
        (scalarPrincipalContraction P (scalarPartialMatrix (L ∘ φ) x) +
          dotProduct B (scalarPartialVector (L ∘ φ) x)) := by
  rw [scalarSchwartzDirectOperator_coordinate P B a b φ x ha hb]
  rw [← Complex.ofReal_neg]
  rw [scalar_real_map_mul]
  congr 1
  simp only [map_add, map_sum, scalar_real_map_mul, scalarPrincipalContraction,
    scalarPartialMatrix, scalarPartialVector, dotProduct]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← scalarSchwartz_real_second_partial L φ i j x]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [← scalarSchwartz_real_partial L φ i x]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real smooth approximation preserving the L2 second derivatives and
L4 first derivatives of the same real H2 function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_4
theorem scalarSchwartz_re_derivative (f : 𝓢(V, ℂ)) (i : Fin 4) :
    D i (f.postcompCLM Complex.reCLM) =
      (scalarSchwartzCoordinateDerivative i f).postcompCLM Complex.reCLM := by
  ext x
  change (fderiv ℝ (Complex.reCLM ∘ f) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) =
    Complex.reCLM ((fderiv ℝ f x) (EuclideanSpace.basisFun (Fin 4) ℝ i))
  rw [fderiv_comp x Complex.reCLM.differentiableAt f.differentiableAt, Complex.reCLM.fderiv]
  rfl

theorem scalarSchwartz_re_toLp (f : 𝓢(V, ℂ)) (p : ℝ≥0∞) :
    (f.postcompCLM Complex.reCLM).toLp p volume = Complex.reCLM.compLp (f.toLp p volume) := by
  apply Lp.ext
  filter_upwards [(f.postcompCLM Complex.reCLM).coeFn_toLp p volume,
    Complex.reCLM.coeFn_compLp (f.toLp p volume), f.coeFn_toLp p volume] with x hf hr hc
  rw [hf, hr, hc]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integer Sobolev regularity under the actual affine chart map.
All orders are needed for the smooth harmonic representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

theorem scalarComplexAffinePullbackL2_memSobolev_integer (n : ℕ)
    (A : V ≃L[ℝ] V) (q : V) (u : Lp ℂ 2 (volume : Measure V))
    (hu : MemSobolev (n : ℝ) 2 (u : T)) :
    MemSobolev (n : ℝ) 2 (scalarComplexAffinePullbackL2 A q u : T) := by
  rw [← scalarAffineDistribution_L2]
  exact scalarAffineDistribution_memSobolev_integer n A q u hu

theorem scalarAffinePullbackL2_memSobolev_integer (n : ℕ)
    (A : V ≃L[ℝ] V) (q : V) (u : Lp ℝ 2 (volume : Measure V))
    (hu : MemSobolev (n : ℝ) 2 (scalarComplexL2 u : T)) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (scalarAffinePullbackL2 A q u) : T) := by
  rw [← scalarComplexAffinePullbackL2_ofReal]
  exact scalarComplexAffinePullbackL2_memSobolev_integer n A q _ hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth chart cutoffs obtained from a finite smooth partition
of unity. Their compact supports lie in the coordinate chart targets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def scalarChartSupport (c : M) (ρ : SmoothScalar (M := M)) : Set FourSpace :=
  (chartAt FourSpace c) '' tsupport ρ.val

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem scalarChartSupport_compact (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    IsCompact (scalarChartSupport c ρ) :=
  (isClosed_tsupport ρ.val).isCompact.image_of_continuousOn ((chartAt FourSpace c).continuousOn.mono hs)

omit [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] in
theorem scalarChartSupport_subset (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    scalarChartSupport c ρ ⊆ (chartAt FourSpace c).target := by
  rintro _ ⟨x, hx, rfl⟩
  exact (chartAt FourSpace c).map_source (hs hx)

def scalarChartCutoff (c : M) (ρ : SmoothScalar (M := M)) : FourSpace → ℝ :=
  (chartAt FourSpace c).target.indicator (fun z => ρ.val ((chartAt FourSpace c).symm z))

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem scalarChartCutoff_support (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    tsupport (scalarChartCutoff c ρ) ⊆ scalarChartSupport c ρ := by
  apply closure_minimal _ (scalarChartSupport_compact c ρ hs).isClosed
  intro z hz
  have hzT : z ∈ (chartAt FourSpace c).target := by
    by_contra hn
    exact hz (by simp [scalarChartCutoff, indicator_of_notMem hn])
  have hρ : ρ.val ((chartAt FourSpace c).symm z) ≠ 0 := by
    change scalarChartCutoff c ρ z ≠ 0 at hz
    simpa only [scalarChartCutoff, indicator_of_mem hzT] using hz
  exact ⟨(chartAt FourSpace c).symm z, subset_tsupport _ hρ,
    (chartAt FourSpace c).right_inv hzT⟩

omit [T3Space M] in
theorem scalarChartCutoff_smooth (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    ContDiff ℝ ∞ (scalarChartCutoff c ρ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · have he : scalarChartCutoff c ρ =ᶠ[𝓝 z]
        (fun w => ρ.val ((chartAt FourSpace c).symm w)) := by
      filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
      exact indicator_of_mem hw _
    exact (scalarCoordinates_contDiffAt ρ.property c z hz (fun j => Fin.elim0 j)).congr_of_eventuallyEq he
  · have ht : z ∉ tsupport (scalarChartCutoff c ρ) :=
      fun h => hz (scalarChartSupport_subset c ρ hs (scalarChartCutoff_support c ρ hs h))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp ht)

omit [IsManifold I4 ∞ M] [T3Space M] in
theorem scalarChartCutoff_compact (c : M) (ρ : SmoothScalar (M := M))
    (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    HasCompactSupport (scalarChartCutoff c ρ) :=
  (scalarChartSupport_compact c ρ hs).of_isClosed_subset (isClosed_tsupport _)
    (scalarChartCutoff_support c ρ hs)

omit [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] in
theorem scalarChartCutoff_apply (c : M) (ρ : SmoothScalar (M := M))
    {x : M} (hx : x ∈ (chartAt FourSpace c).source) :
    scalarChartCutoff c ρ (chartAt FourSpace c x) = ρ.val x := by
  rw [scalarChartCutoff, indicator_of_mem ((chartAt FourSpace c).map_source hx),
    (chartAt FourSpace c).left_inv hx]

theorem scalarPartition_exists : Nonempty (ScalarPartition M) := by
  have hcover : (univ : Set M) ⊆ ⋃ x : M, (chartAt FourSpace x).source := by
    intro x _
    exact mem_iUnion_of_mem x (mem_chart_source FourSpace x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt FourSpace x).source) (fun x => (chartAt FourSpace x).open_source) hcover
  have hfinite : (univ : Set M) ⊆ ⋃ x : {x : M // x ∈ s}, (chartAt FourSpace x.val).source := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨c, hc⟩ hxc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := I4) (s := (univ : Set M)) isClosed_univ
    (fun x : {x : M // x ∈ s} => (chartAt FourSpace x.val).source)
    (fun x => (chartAt FourSpace x.val).open_source) hfinite
  exact ⟨⟨s, ρ, hρ⟩⟩

def scalarPartitionFunction (P : ScalarPartition M) (i : P.ι) : SmoothScalar (M := M) :=
  ⟨P.ρ i, (P.ρ i).contMDiff⟩

omit [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] in
theorem scalarPartitionFunction_support (P : ScalarPartition M) (i : P.ι) :
    tsupport (scalarPartitionFunction P i).val ⊆ (chartAt FourSpace (P.center i)).source :=
  P.subordinate i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closure of the real H2 jet, using actual derivatives of real Schwartz
approximants and the complex distributional Sobolev space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (φ : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ

theorem scalarSchwartz_ofReal_derivative (f : S) (i : Fin 4) :
    scalarSchwartzCoordinateDerivative i (f.postcompCLM Complex.ofRealCLM) =
      (D i f).postcompCLM Complex.ofRealCLM := by
  ext x
  change (fderiv ℝ (Complex.ofRealCLM ∘ f) x) (EuclideanSpace.basisFun (Fin 4) ℝ i) =
    Complex.ofRealCLM ((fderiv ℝ f x) (EuclideanSpace.basisFun (Fin 4) ℝ i))
  rw [fderiv_comp x Complex.ofRealCLM.differentiableAt f.differentiableAt, Complex.ofRealCLM.fderiv]
  rfl

theorem scalarSchwartz_ofReal_toLp (f : S) :
    (f.postcompCLM Complex.ofRealCLM).toLp 2 volume = scalarComplexL2 (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(f.postcompCLM Complex.ofRealCLM).coeFn_toLp 2 volume,
    scalarComplexL2_coe (f.toLp 2 volume), f.coeFn_toLp 2 volume] with x hf hr hc
  rw [hf, hr, hc]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! At sufficiently small chart scales, the actual compact extensions of
the metric coefficients satisfy all Schwartz jet bounds required by the
elliptic estimate. The coefficients are constructed, not postulated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarRescaledDrift_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (y : FourSpace)
    (hy : scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun z => scalarRescaledDrift g c z₀ r z i) y := by
  change ContDiffAt ℝ ∞ (fun z => r * scalarFrozenDrift g c z₀
    (scalarRescaledPoint g c z₀ r z) i) y
  apply contDiffAt_const.mul
  apply (scalarFrozenDrift_contDiffAt g c z₀ _ hy i).comp
  exact contDiffAt_const.add
    (((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
      (chartGramMatrix g c 1 z₀)).contDiff.contDiffAt.const_smul r)

theorem scalarRescaledPoint_compact_eventually (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) {K : Set FourSpace} (hK : IsCompact K)
    (S : Set FourSpace) (hS : S ∈ 𝓝 z₀.val) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ y ∈ K,
      scalarRescaledPoint g c z₀ r y ∈ S := by
  let T : Set (ℝ × FourSpace) := {q | scalarRescaledPoint g c z₀ q.1 q.2 ∈ S}
  have hcont : Continuous (fun q : ℝ × FourSpace => scalarRescaledPoint g c z₀ q.1 q.2) :=
    continuous_const.add (continuous_fst.smul
      (((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
        (chartGramMatrix g c 1 z₀)).continuous.comp continuous_snd))
  have htube : T ∈ 𝓝 (0 : ℝ) ×ˢ 𝓝ˢ K := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro y _
    rw [← nhds_prod_eq]
    apply hcont.continuousAt
    simpa only [scalarRescaledPoint, zero_smul, add_zero] using hS
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp htube
  filter_upwards [hU] with r hr y hy
  have hyV : y ∈ V := subset_of_mem_nhdsSet hV hy
  exact hUV (show (r, y) ∈ U ×ˢ V from ⟨hr, hyV⟩)

theorem scalarRescaledPoint_compact_target (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) {K : Set FourSpace} (hK : IsCompact K) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∀ y ∈ K,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
  scalarRescaledPoint_compact_eventually g c z₀ hK _
    ((chartAt FourSpace c).open_target.mem_nhds z₀.property)

theorem scalarRescaledSchwartz_small_compact (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, |r| < η →
      ∃ (a : Fin 4 → Fin 4 → 𝓢(FourSpace, ℂ)) (b : Fin 4 → 𝓢(FourSpace, ℂ)),
        (∀ i j y, a i j y = (scalarCutoffPrincipal g c z₀ χ r i j y : ℂ)) ∧
        (∀ i y, b i y = (scalarCutoffDrift g c z₀ χ r i y : ℂ)) ∧
        (∀ i j y, ‖a i j y‖ ≤ δ) ∧
        (∀ i j k y, ‖scalarSchwartzCoordinateDerivative k (a i j) y‖ ≤ δ) ∧
        (∀ i j k l y, ‖scalarSchwartzCoordinateDerivative k
          (scalarSchwartzCoordinateDerivative l (a i j)) y‖ ≤ δ) ∧
        (∀ i y, ‖b i y‖ ≤ δ) ∧
        (∀ i k y, ‖scalarSchwartzCoordinateDerivative k (b i) y‖ ≤ δ) := by
  have hP : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i j y,
      |scalarCutoffPrincipal g c z₀ χ r i j y| < δ ∧
      (∀ k, |partialDeriv (scalarCutoffPrincipal g c z₀ χ r i j) k y| < δ) ∧
      (∀ k l, |partialDeriv
        (fun z => partialDeriv (scalarCutoffPrincipal g c z₀ χ r i j) l z) k y| < δ) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    obtain ⟨η, hη, hb⟩ := scalarCutoffPrincipal_jets_uniform g c z₀ χ hχ hc i j δ hδ
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hη] with r hr
    apply hb r
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hr
  have hB : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i y,
      |scalarCutoffDrift g c z₀ χ r i y| < δ ∧
      (∀ k, |partialDeriv (scalarCutoffDrift g c z₀ χ r i) k y| < δ) ∧
      (∀ k l, |partialDeriv
        (fun z => partialDeriv (scalarCutoffDrift g c z₀ χ r i) l z) k y| < δ) := by
    apply eventually_all.mpr
    intro i
    obtain ⟨η, hη, hb⟩ := scalarCutoffDrift_jets_uniform g c z₀ χ hχ hc i δ hδ
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hη] with r hr
    apply hb r
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hr
  have hT := scalarRescaledPoint_compact_target g c z₀ hc
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp (hP.and (hB.and hT))
  refine ⟨η, hη, ?_⟩
  intro r hr
  obtain ⟨hPr, hBr, hTr⟩ := hball
    (show r ∈ ball (0 : ℝ) η by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hr)
  let a : Fin 4 → Fin 4 → 𝓢(FourSpace, ℂ) := fun i j =>
    scalarCutoffSchwartz χ (fun y => scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j)
      hχ hc (fun y hy => (scalarRescaledPrincipal_contDiffAt g c z₀ r y (hTr y hy) i j).sub
        contDiffAt_const)
  let b : Fin 4 → 𝓢(FourSpace, ℂ) := fun i =>
    scalarCutoffSchwartz χ (fun y => scalarRescaledDrift g c z₀ r y i)
      hχ hc (fun y hy => scalarRescaledDrift_contDiffAt g c z₀ r y (hTr y hy) i)
  have ha (i j : Fin 4) := scalarCutoffSchwartz_jet_bounds χ
    (fun y => scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) hχ hc
    (fun y hy => (scalarRescaledPrincipal_contDiffAt g c z₀ r y (hTr y hy) i j).sub
      contDiffAt_const) δ
    (fun y => (hPr i j y).1.le)
    (fun k y => ((hPr i j y).2.1 k).le)
    (fun k l y => ((hPr i j y).2.2 k l).le)
  have hb (i : Fin 4) := scalarCutoffSchwartz_jet_bounds χ
    (fun y => scalarRescaledDrift g c z₀ r y i) hχ hc
    (fun y hy => scalarRescaledDrift_contDiffAt g c z₀ r y (hTr y hy) i) δ
    (fun y => (hBr i y).1.le)
    (fun k y => ((hBr i y).2.1 k).le)
    (fun k l y => ((hBr i y).2.2 k l).le)
  exact ⟨a, b, fun _ _ _ => rfl, fun _ _ => rfl, fun i j => (ha i j).1,
    fun i j => (ha i j).2.1, fun i j => (ha i j).2.2,
    fun i => (hb i).1, fun i => (hb i).2.1⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Poisson equation tested against compact coordinate
functions, with the volume density absorbed into the same H1 solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarChartOperator_eq_zero_off_tsupport (g : SmoothMetric M) (c : M)
    (ψ : FourSpace → ℝ) {z : FourSpace} (hz : z ∉ tsupport ψ) :
    scalarChartOperator g c ψ z = 0 := by
  rw [scalarChartOperator_congr_nhds g c (notMem_tsupport_iff_eventuallyEq.mp hz)]
  simp [scalarChartOperator, partialDeriv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual compactly supported scalar coordinate components of a smooth
two-form, including their ordinary product-rule derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormCutoffC1 (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) :
    SmoothH1TwoForm o →ₗ[ℝ] ↥(Euclidean.C1c (E := FourSpace)) where
  toFun u := ⟨fun z => χ z * twoFormCoordinates o (u : smoothTwoForms o).val c z a,
    (scalarCutoff_contDiff χ _ hχ (fun z hz =>
      (u : smoothTwoForms o).property.coordinates_contDiffAt c z (hKt (hs hz)) a)).of_le
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top), hc.mul_right⟩
  map_add' u v := by
    ext z
    change χ z * twoFormCoordinates o
      ((u : smoothTwoForms o).val + (v : smoothTwoForms o).val) c z a = _
    rw [twoFormCoordinates_add]
    change χ z * (_ + _) = χ z * _ + χ z * _
    ring
  map_smul' r u := by
    ext z
    change χ z * twoFormCoordinates o (r • (u : smoothTwoForms o).val) c z a = _
    rw [twoFormCoordinates_smul]
    change χ z * (r * _) = r * (χ z * _)
    ring

theorem twoFormCutoffC1_partial (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) (u : SmoothH1TwoForm o)
    (i : Fin 4) (z : FourSpace) :
    partialDeriv (twoFormCutoffC1 c hKt χ hχ hc hs a u).val i z =
      χ z * partialDeriv (fun w => twoFormCoordinates o (u : smoothTwoForms o).val c w a) i z +
        partialDeriv χ i z * twoFormCoordinates o (u : smoothTwoForms o).val c z a := by
  by_cases hz : z ∈ K
  · have hu := ((u : smoothTwoForms o).property.coordinates_contDiffAt c z (hKt hz) a).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    change partialDeriv (fun w => χ w * twoFormCoordinates o (u : smoothTwoForms o).val c w a) i z = _
    rw [scalar_partial_product χ _ z (hχ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z) hu]
    ring
  · have ht : z ∉ tsupport χ := fun h => hz (hs h)
    have hzero : χ z = 0 := image_eq_zero_of_notMem_tsupport ht
    have hder : partialDeriv χ i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ht ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h))
    have hp : partialDeriv (twoFormCutoffC1 c hKt χ hχ hc hs a u).val i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ht
        (tsupport_mul_subset_left ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h)))
    rw [hp, hzero, hder, zero_mul, zero_mul, zero_add]

theorem twoFormCutoffC1_support (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) (u : SmoothH1TwoForm o) :
    tsupport (twoFormCutoffC1 c hKt χ hχ hc hs a u).val ⊆ K :=
  tsupport_mul_subset_left.trans hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong L2 control of the finite coordinate jets of the Bessel inverse.
All derivatives are the actual distributional derivatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)

def besselJetLinear (n : ℕ) (is : List (Fin 4)) (hle : is.length ≤ n) : L2 →ₗ[ℂ] L2 where
  toFun f := (besselJet_exists n is hle f).choose
  map_add' f g := by
    apply scalarL2_distribution_injective
    change (((besselJet_exists n is hle (f + g)).choose) : T) = _
    rw [← (besselJet_exists n is hle (f + g)).choose_spec]
    simpa only [← Lp.toTemperedDistributionCLM_apply, map_add] using
      congrArg₂ (fun a b : T => a + b) (besselJet_exists n is hle f).choose_spec
        (besselJet_exists n is hle g).choose_spec
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply scalarL2_distribution_injective
    change (((besselJet_exists n is hle (c • f)).choose) : T) = _
    rw [← (besselJet_exists n is hle (c • f)).choose_spec]
    simpa only [← Lp.toTemperedDistributionCLM_apply, map_smul] using
      congrArg (fun a : T => c • a) (besselJet_exists n is hle f).choose_spec

theorem besselJetLinear_distribution (n : ℕ) (is : List (Fin 4))
    (hle : is.length ≤ n) (f : L2) :
    (besselJetLinear n is hle f : T) =
      scalarCoordinateJet is (scalarIntegerBesselInverse n f : T) :=
  (besselJet_exists n is hle f).choose_spec.symm

/-- Every derivative of order at most n of the inverse n-th Bessel operator is
continuous from L2 to L2. -/
def scalarBesselJetL2 (n : ℕ) (is : List (Fin 4)) (hle : is.length ≤ n) : L2 →L[ℂ] L2 where
  toLinearMap := besselJetLinear n is hle
  cont := (besselJetLinear n is hle).continuous_of_seq_closed_graph (by
    intro f x y hfx hfy
    have hl := (scalarCoordinateJet is).continuous.continuousAt.tendsto.comp
      ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp
        ((scalarIntegerBesselInverse n).continuous.continuousAt.tendsto.comp hfx))
    have hr := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp hfy
    have heq : (y : T) = scalarCoordinateJet is (scalarIntegerBesselInverse n x : T) := by
      have hr' : Tendsto (fun k => (besselJetLinear n is hle (f k) : T)) atTop
          (𝓝 (y : T)) := by
        simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply] using hr
      have hl' : Tendsto (fun k => (besselJetLinear n is hle (f k) : T)) atTop
          (𝓝 (scalarCoordinateJet is (scalarIntegerBesselInverse n x : T))) := by
        simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply,
          besselJetLinear_distribution] using hl
      exact tendsto_nhds_unique hr' hl'
    apply scalarL2_distribution_injective
    exact heq.trans (besselJetLinear_distribution n is hle x).symm)

theorem scalarBesselJetL2_distribution (n : ℕ) (is : List (Fin 4))
    (hle : is.length ≤ n) (f : L2) :
    (scalarBesselJetL2 n is hle f : T) =
      scalarCoordinateJet is (scalarIntegerBesselInverse n f : T) :=
  besselJetLinear_distribution n is hle f

theorem scalarBesselJetL2_memSobolev (n : ℕ) (is : List (Fin 4))
    (hle : is.length ≤ n) (f : L2) :
    MemSobolev ((n : ℝ) - is.length) 2 (scalarBesselJetL2 n is hle f : T) := by
  rw [scalarBesselJetL2_distribution]
  exact scalarCoordinateJet_memSobolev is (scalarIntegerBesselInverse_memSobolev n f)

theorem scalarSchwartzBesselJet_toLp (n : ℕ) (is : List (Fin 4)) (hle : is.length ≤ n) (φ : S) :
    (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).toLp 2 volume =
      scalarBesselJetL2 n is hle (φ.toLp 2 volume) := by
  apply scalarL2_distribution_injective
  change ((scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).toLp 2 volume : T) =
    (scalarBesselJetL2 n is hle (φ.toLp 2 volume) : T)
  rw [Lp.toTemperedDistribution_toLp_eq, scalarSchwartzCoordinateJet_distribution,
    scalarBesselJetL2_distribution, ← scalarSchwartzIntegerBesselInverse_toLp,
    Lp.toTemperedDistribution_toLp_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The distributional derivative of an actual compact C1 first jet in
four-dimensional Euclidean space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped SchwartzMap ENNReal

noncomputable section

theorem scalarC1_weak_derivative (f : ↥(Euclidean.C1c (E := FourSpace)))
    (q : 𝓢(FourSpace, ℝ)) (i : Fin 4) :
    (∫ x, f.val x * partialDeriv q i x) = -(∫ x, partialDeriv f.val i x * q x) := by
  have hd := ScalarEuclideanSobolev.continuous_partial f.property.1 i
  have hq := ScalarEuclideanSobolev.continuous_partial (q.smooth 1) i
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hd.mul q.continuous).integrable_of_hasCompactSupport
      ((f.property.2.fderiv_apply ℝ (coordinateVector i)).mul_right))
    ((f.property.1.continuous.mul hq).integrable_of_hasCompactSupport f.property.2.mul_right)
    ((f.property.1.continuous.mul q.continuous).integrable_of_hasCompactSupport f.property.2.mul_right)
    (fun x _ => f.property.1.differentiable one_ne_zero x)
    (fun x _ => q.differentiableAt)

theorem scalarC1_complex_derivative (f : ↥(Euclidean.C1c (E := FourSpace))) (i : Fin 4) :
    scalarCoordinateDerivative i
      (scalarComplexL2 (ScalarEuclideanSobolev.valueL2 f) : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (ScalarEuclideanSobolev.partialL2 f i) : 𝓢'(FourSpace, ℂ)) := by
  apply scalarComplexL2_weak_derivative
  intro q
  have hleft : (∫ x, ScalarEuclideanSobolev.valueL2 f x * partialDeriv q i x) =
      ∫ x, f.val x * partialDeriv q i x := by
    apply integral_congr_ae
    filter_upwards [ScalarEuclideanSobolev.valueL2_coe f] with x hx
    rw [hx]
  have hright : (∫ x, ScalarEuclideanSobolev.partialL2 f i x * q x) =
      ∫ x, partialDeriv f.val i x * q x := by
    apply integral_congr_ae
    filter_upwards [ScalarEuclideanSobolev.partialL2_coe f i] with x hx
    rw [hx]
  rw [hleft, hright]
  exact scalarC1_weak_derivative f q i

def scalarGradientCoordinateL2 (i : Fin 4) :
    Lp FourSpace 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (PiLp.proj 2 (fun _ : Fin 4 => ℝ) i).compLpL 2 volume

theorem scalarGradientCoordinateL2_smooth (f : ↥(Euclidean.C1c (E := FourSpace))) (i : Fin 4) :
    scalarGradientCoordinateL2 i (ScalarEuclideanSobolev.gradientL2 f) =
      ScalarEuclideanSobolev.partialL2 f i := by
  have hc := (PiLp.proj 2 (fun _ : Fin 4 => ℝ) i : FourSpace →L[ℝ] ℝ).coeFn_compLpL
    (p := 2) (μ := (volume : Measure FourSpace)) (ScalarEuclideanSobolev.gradientL2 f)
  have hg : ScalarEuclideanSobolev.gradientL2 f =ᵐ[volume] Euclidean.grad f.val :=
    MemLp.coeFn_toLp _
  apply Lp.ext
  filter_upwards [hc, hg, ScalarEuclideanSobolev.partialL2_coe f i] with x hcx hgx hpx
  unfold scalarGradientCoordinateL2
  rw [hcx, hgx, hpx, ScalarEuclideanSobolev.grad_eq_sum_partial]
  simp [PiLp.proj_apply, EuclideanSpace.basisFun_apply, smul_eq_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary continuous H¹-to-L⁴ embedding for the actual compact
four-manifold, assembled from compact chart cutoffs. No sharp constant is
asserted here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_6
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance manifoldSobolev_frameCompact_rfb4d6b_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_probability
def smoothScalarContinuous : SmoothScalar (M := M) →ₗ[ℝ] C(M, ℝ) where
  toFun a := ⟨a.val, a.property.continuous⟩
  map_add' a b := by ext; rfl
  map_smul' r a := by ext; rfl

def smoothScalarProduct (ρ a : SmoothScalar (M := M)) : SmoothScalar (M := M) :=
  ⟨fun x => ρ.val x * a.val x, ρ.property.mul a.property⟩

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] in
theorem smoothScalar_partition (P : ScalarPartition M) (a : SmoothScalar (M := M)) :
    (∑ i : P.ι, smoothScalarProduct (scalarPartitionFunction P i) a) = a := by
  apply Subtype.ext
  funext x
  have he : (∑ i : P.ι, (P.ρ i) x) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using P.ρ.sum_eq_one (mem_univ x)
  simp only [Submodule.coe_sum, Finset.sum_apply, smoothScalarProduct,
    scalarPartitionFunction, ← Finset.sum_mul, he, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rescaled metric coefficients satisfy the quantitative
hypotheses of the local elliptic inverse, including the adjoint drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff SchwartzMap LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

theorem scalarScaledSchwartz_derivative (κ : ℝ) (φ : S) (i : Fin 4) :
    D i ((-κ) • φ) = (-κ) • D i φ := by
  exact LineDeriv.lineDerivOp_smul _ _ _

theorem scalarScaledSchwartz_bound (κ ε : ℝ) (φ : S) (y : V)
    (hφ : ‖φ y‖ ≤ ε) : ‖((-κ) • φ) y‖ ≤ |κ| * ε := by
  change ‖(-κ) • φ y‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  exact mul_le_mul_of_nonneg_left hφ (abs_nonneg κ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- At every sufficiently small scale, the actual normalized principal
coefficients and their actual adjoint drift obey one fixed inverse budget.
The unexpanded drift b is retained for the exact adjoint test identity. -/
theorem scalarRescaledAdjointSchwartz_small (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, |r| < η →
      ∃ (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S),
        (∀ i j y, a i j y =
          (-(((2 * Real.pi) ^ 2)⁻¹) : ℝ) •
            (scalarCutoffPrincipal g c z₀ χ r i j y : ℂ)) ∧
        (∀ i y, b i y =
          (-(((2 * Real.pi) ^ 2)⁻¹) : ℝ) •
            (scalarCutoffDrift g c z₀ χ r i y : ℂ)) ∧
        (∀ i j y, ‖a i j y‖ ≤ scalarEllipticSmallSize) ∧
        (∀ i j k y, ‖D k (a i j) y‖ ≤ scalarEllipticSmallSize) ∧
        (∀ i j k l y, ‖D k (D l (a i j)) y‖ ≤ scalarEllipticSmallSize) ∧
        (∀ j y, ‖scalarAdjointDrift a b j y‖ ≤ scalarEllipticSmallSize) ∧
        (∀ j k y, ‖D k (scalarAdjointDrift a b j) y‖ ≤ scalarEllipticSmallSize) := by
  let κ : ℝ := ((2 * Real.pi) ^ 2)⁻¹
  let δ : ℝ := scalarEllipticSmallSize
  let ε : ℝ := δ / (9 * (|κ| + 1))
  have hδ : 0 < δ := scalarEllipticSmallSize_pos
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hbudget : |κ| * ε ≤ δ / 9 := scalar_rescaling_budget κ δ hδ.le
  have hnine : δ / 9 ≤ δ := by linarith
  obtain ⟨η, hη, hsmall⟩ := scalarRescaledSchwartz_small_compact g c z₀ χ hχ hc ε hε
  refine ⟨η, hη, ?_⟩
  intro r hr
  obtain ⟨a₀, b₀, ha₀, hb₀, ha, ha1, ha2, hb, hb1⟩ := hsmall r hr
  let a : Fin 4 → Fin 4 → S := fun i j => (-κ) • a₀ i j
  let b : Fin 4 → S := fun i => (-κ) • b₀ i
  have hA (i j : Fin 4) (y : V) : ‖a i j y‖ ≤ δ / 9 :=
    (scalarScaledSchwartz_bound κ ε (a₀ i j) y (ha i j y)).trans hbudget
  have hA1 (i j k : Fin 4) (y : V) : ‖D k (a i j) y‖ ≤ δ / 9 := by
    change ‖D k ((-κ) • a₀ i j) y‖ ≤ _
    rw [scalarScaledSchwartz_derivative]
    exact (scalarScaledSchwartz_bound κ ε (D k (a₀ i j)) y (ha1 i j k y)).trans hbudget
  have hA2 (i j k l : Fin 4) (y : V) : ‖D k (D l (a i j)) y‖ ≤ δ / 9 := by
    change ‖D k (D l ((-κ) • a₀ i j)) y‖ ≤ _
    rw [scalarScaledSchwartz_derivative, scalarScaledSchwartz_derivative]
    exact (scalarScaledSchwartz_bound κ ε (D k (D l (a₀ i j))) y
      (ha2 i j k l y)).trans hbudget
  have hB (i : Fin 4) (y : V) : ‖b i y‖ ≤ δ / 9 :=
    (scalarScaledSchwartz_bound κ ε (b₀ i) y (hb i y)).trans hbudget
  have hB1 (i k : Fin 4) (y : V) : ‖D k (b i) y‖ ≤ δ / 9 := by
    change ‖D k ((-κ) • b₀ i) y‖ ≤ _
    rw [scalarScaledSchwartz_derivative]
    exact (scalarScaledSchwartz_bound κ ε (D k (b₀ i)) y (hb1 i k y)).trans hbudget
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j y
    change (-κ) • a₀ i j y = _
    rw [ha₀]
  · intro i y
    change (-κ) • b₀ i y = _
    rw [hb₀]
  · intro i j y
    exact (hA i j y).trans hnine
  · intro i j k y
    exact (hA1 i j k y).trans hnine
  · intro i j k l y
    exact (hA2 i j k l y).trans hnine
  · intro j y
    simpa only [mul_div_cancel₀ _ (by norm_num : (9 : ℝ) ≠ 0)] using
      scalarAdjointDrift_bound a b (δ / 9) hA1 hB j y
  · intro j k y
    simpa only [mul_div_cancel₀ _ (by norm_num : (9 : ℝ) ≠ 0)] using
      scalarAdjointDrift_derivative_bound a b (δ / 9) hA2 hB1 j k y

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness of each compact chart localization of the intrinsic scalar
H¹ space. The actual first jet lies in the closed Euclidean graph, with
support in the fixed compact set, so Euclidean Rellich applies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFourSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFourSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasureSpaceFourSpace
theorem scalarBorel_valueL2 (f : ↥(Euclidean.C1c (E := FourSpace))) :
    scalarBorelLpEquiv ℝ 2 (ScalarEuclideanSobolev.valueL2 f) =
      Euclidean.toL2 (μ := (volume : Measure FourSpace)) f := by
  apply Lp.ext
  exact (scalarBorelLpEquiv_ae ℝ 2 _ _ (ScalarEuclideanSobolev.valueL2_coe f)).trans
    (MemLp.coeFn_toLp _).symm

theorem scalarBorel_gradientL2 (f : ↥(Euclidean.C1c (E := FourSpace))) :
    scalarBorelLpEquiv FourSpace 2 (ScalarEuclideanSobolev.gradientL2 f) =
      Euclidean.toL2Grad (μ := (volume : Measure FourSpace)) f := by
  apply Lp.ext
  exact (scalarBorelLpEquiv_ae FourSpace 2 _ _ (MemLp.coeFn_toLp _)).trans
    (MemLp.coeFn_toLp _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second coordinate product rule needs only local C2 regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped ContDiff _root_.Topology

noncomputable section

theorem scalar_partial_second_product_at (f u : FourSpace → ℝ) (x : FourSpace)
    (hf : ContDiffAt ℝ 2 f x) (hu : ContDiffAt ℝ 2 u x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => f y * u y) i) j x =
      partialDeriv (partialDeriv f i) j x * u x +
      partialDeriv f i x * partialDeriv u j x +
      partialDeriv f j x * partialDeriv u i x +
      f x * partialDeriv (partialDeriv u i) j x := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hud : DifferentiableAt ℝ u x := hu.differentiableAt (by norm_num)
  have hfpi : DifferentiableAt ℝ (partialDeriv f i) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero
  have hupi : DifferentiableAt ℝ (partialDeriv u i) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero
  have heq : partialDeriv (fun y => f y * u y) i =ᶠ[𝓝 x]
      (fun y => partialDeriv f i y * u y + f y * partialDeriv u i y) := by
    filter_upwards [hf.eventually (by norm_num), hu.eventually (by norm_num)] with y hfy huy
    exact scalar_partial_product f u y
      (hfy.differentiableAt (by norm_num)) (huy.differentiableAt (by norm_num)) i
  change fderiv ℝ (partialDeriv (fun y => f y * u y) i) x (coordinateVector j) = _
  have hadd := fderiv_fun_add (hfpi.mul hud) (hfd.mul hupi)
  change fderiv ℝ (fun y => partialDeriv f i y * u y + f y * partialDeriv u i y) x =
    fderiv ℝ (partialDeriv f i * u) x + fderiv ℝ (f * partialDeriv u i) x at hadd
  rw [heq.fderiv_eq, hadd, fderiv_mul hfpi hud, fderiv_mul hfd hupi]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, partialDeriv]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undoing the affine normalization at the finite orders needed for
smooth harmonic representatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem scalar_integer_unscale (n : ℕ) (A : V ≃L[ℝ] V) (q : V) (b χ : V → ℝ)
    (v : L2) (hv2 : MemSobolev (n : ℝ) 2 (v : T))
    (hv : (v : V → ℂ) =ᵐ[volume] fun y => (χ y * b (A y + q) : ℝ)) :
    ∃ w : L2, MemSobolev (n : ℝ) 2 (w : T) ∧
      (w : V → ℂ) =ᵐ[volume] fun z => (χ (A.symm (z - q)) * b z : ℝ) := by
  let w := scalarComplexAffinePullbackL2 A.symm (-A.symm q) v
  refine ⟨w, scalarComplexAffinePullbackL2_memSobolev_integer n _ _ v hv2, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving (fun z : V => A.symm z + (-A.symm q))
      volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  filter_upwards [scalarComplexAffinePullbackL2_coe A.symm (-A.symm q) v,
    hmp.ae_eq_comp hv] with z hz he
  dsimp only [Function.comp_apply] at he
  rw [hz]
  change v (A.symm z + (-A.symm q)) = _ at he
  rw [he]
  simp only [map_add, ContinuousLinearEquiv.apply_symm_apply, map_neg,
    neg_add_cancel_right]
  rw [map_sub]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform convergence of the lower coordinate jets in a common smooth approximation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "Linf" => Lp ℂ ∞ (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)



variable (n : ℕ) (is : List (Fin 4)) (h3 : is.length + 3 ≤ n)

def jetL2 : L2 →L[ℂ] L2 := scalarBesselJetL2 n is (by omega)

theorem jetL2_memLp_top (f : L2) :
    MemLp (jetL2 n is h3 f : V → ℂ) ∞ volume := by
  have hreg : MemSobolev 3 2 (jetL2 n is h3 f : T) := by
    apply (scalarBesselJetL2_memSobolev n is (by omega) f).mono
    have hc : (is.length : ℝ) + 3 ≤ n := by exact_mod_cast h3
    linarith
  obtain ⟨v, hv⟩ := scalar_L2_H3_boundedContinuous_representative _ hreg
  exact (memLp_congr_ae hv).mpr v.memLp_top

def jetUniformLinear : L2 →ₗ[ℂ] Linf where
  toFun f := (jetL2_memLp_top n is h3 f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(jetL2_memLp_top n is h3 (f + g)).coeFn_toLp,
      (jetL2_memLp_top n is h3 f).coeFn_toLp,
      (jetL2_memLp_top n is h3 g).coeFn_toLp,
      Lp.coeFn_add (jetL2 n is h3 f) (jetL2 n is h3 g),
      Lp.coeFn_add ((jetL2_memLp_top n is h3 f).toLp _)
        ((jetL2_memLp_top n is h3 g).toLp _)] with x hfg hf hg h2 h4
    rw [hfg, h4, Pi.add_apply, hf, hg, map_add]
    exact h2
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(jetL2_memLp_top n is h3 (c • f)).coeFn_toLp,
      (jetL2_memLp_top n is h3 f).coeFn_toLp,
      Lp.coeFn_smul c (jetL2 n is h3 f),
      Lp.coeFn_smul c ((jetL2_memLp_top n is h3 f).toLp _)] with x hcf hf h2 h4
    rw [hcf, h4, Pi.smul_apply, hf, map_smul]
    exact h2

theorem jetUniformLinear_coe (f : L2) :
    (jetUniformLinear n is h3 f : V → ℂ) =ᵐ[volume] jetL2 n is h3 f :=
  (jetL2_memLp_top n is h3 f).coeFn_toLp

/-- Jets leaving at least three Sobolev derivatives are continuous in L∞. -/
def scalarBesselJetUniform : L2 →L[ℂ] Linf where
  toLinearMap := jetUniformLinear n is h3
  cont := (jetUniformLinear n is h3).continuous_of_seq_closed_graph (by
    intro f x y hfx hfy
    have hlow := tendstoInMeasure_of_tendsto_Lp
      ((jetL2 n is h3).continuous.continuousAt.tendsto.comp hfx)
    have hhigh := tendstoInMeasure_of_tendsto_Lp hfy
    have hlow' : TendstoInMeasure volume
        (fun k => (jetUniformLinear n is h3 (f k) : V → ℂ)) atTop
        (jetL2 n is h3 x : V → ℂ) :=
      hlow.congr (fun k => (jetUniformLinear_coe n is h3 (f k)).symm) Filter.EventuallyEq.rfl
    apply Lp.ext
    exact (tendstoInMeasure_ae_unique hhigh hlow').trans
      (jetUniformLinear_coe n is h3 x).symm)

theorem scalarBesselJetUniform_coe (f : L2) :
    (scalarBesselJetUniform n is h3 f : V → ℂ) =ᵐ[volume] jetL2 n is h3 f :=
  jetUniformLinear_coe n is h3 f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded reconstruction of a compactly supported Euclidean chart
function into the actual base L² space. Null sets are respected by the
proved reverse chart norm comparison. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.reconstruction_baseProbability
def scalarChartReconstructionFun (c : M) (K : Set FourSpace) (f : FourSpace → ℝ) : M → ℝ :=
  ((chartAt FourSpace c).symm '' K).indicator (fun x => f (chartAt FourSpace c x))

omit [IsManifold I4 ∞ M] [CompactSpace M] [Nonempty M] in
theorem reconstruction_set_measurable (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    MeasurableSet ((chartAt FourSpace c).symm '' K) :=
  (hK.image_of_continuousOn ((chartAt FourSpace c).symm.continuousOn.mono hKt)).isClosed.measurableSet

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] in
theorem scalarChartReconstructionFun_chart (c : M) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target) (f : FourSpace → ℝ)
    {z : FourSpace} (hz : z ∈ K) :
    scalarChartReconstructionFun c K f ((chartAt FourSpace c).symm z) = f z := by
  have hzS : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace c).symm '' K := ⟨z, hz, rfl⟩
  rw [scalarChartReconstructionFun, indicator_of_mem hzS,
    (chartAt FourSpace c).right_inv (hKt hz)]

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] in
theorem scalarChartReconstructionFun_add (c : M) (K : Set FourSpace)
    (f h : FourSpace → ℝ) :
    scalarChartReconstructionFun c K (fun z => f z + h z) =
      fun x => scalarChartReconstructionFun c K f x + scalarChartReconstructionFun c K h x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt FourSpace c).symm '' K <;>
    simp [scalarChartReconstructionFun, hx]

omit [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] in
theorem scalarChartReconstructionFun_smul (c : M) (K : Set FourSpace)
    (r : ℝ) (f : FourSpace → ℝ) :
    scalarChartReconstructionFun c K (fun z => r • f z) =
      fun x => r • scalarChartReconstructionFun c K f x := by
  classical
  funext x
  by_cases hx : x ∈ (chartAt FourSpace c).symm '' K <;>
    simp [scalarChartReconstructionFun, hx]

omit [IsManifold I4 ∞ M] [CompactSpace M] [Nonempty M] in
theorem scalarChartReconstructionFun_stronglyMeasurable (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    {f : FourSpace → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (scalarChartReconstructionFun c K f) := by
  classical
  let C : M → FourSpace := (chartAt FourSpace c).source.piecewise
    (chartAt FourSpace c) (fun _ => 0)
  have hC : Measurable C := (chartAt FourSpace c).continuousOn.measurable_piecewise
    continuousOn_const (chartAt FourSpace c).open_source.measurableSet
  have he : scalarChartReconstructionFun c K f =
      ((chartAt FourSpace c).symm '' K).indicator (fun x => f (C x)) := by
    funext x
    by_cases hx : x ∈ (chartAt FourSpace c).symm '' K
    · obtain ⟨z, hz, rfl⟩ := hx
      have hzS : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace c).symm '' K := ⟨z, hz, rfl⟩
      rw [scalarChartReconstructionFun, indicator_of_mem hzS, indicator_of_mem hzS]
      rw [show C ((chartAt FourSpace c).symm z) =
          chartAt FourSpace c ((chartAt FourSpace c).symm z) from
        piecewise_eq_of_mem _ _ _ ((chartAt FourSpace c).map_target (hKt hz))]
    · simp only [scalarChartReconstructionFun, indicator_of_notMem hx]
  rw [he]
  exact (hf.comp_measurable hC).indicator (reconstruction_set_measurable c hK hKt)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Freezing an actual Euclidean L2 chart equation, with its source
transformed by the same affine map as the unknown. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local notation "L2" => Lp ℝ 2 (volume : Measure FourSpace)

theorem scalarEuclidean_rescaled_equation (g : SmoothMetric M) (c : M)
    (w F : L2) (V : Set FourSpace)
    (hw : ∀ (φ : FourSpace → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ z, w z * scalarChartOperator g c φ z) = ∫ z, F z * φ z)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ht : ∀ y ∈ tsupport ψ, scalarRescaledPoint g c z₀ r y ∈ V) :
    (∫ y, scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀ w y *
      scalarRescaledOperator g c z₀ r ψ y) =
    ∫ y, (r ^ 2 • scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀ F) y * ψ y := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr
  let φ : FourSpace → ℝ := fun z => ψ (A.symm (z - z₀))
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (A.symm.contDiff.comp (contDiff_id.sub contDiff_const))
  have hcφ : HasCompactSupport φ := by
    have h := hcψ.comp_homeomorph ((Homeomorph.addRight (-z₀.val)).trans A.symm.toHomeomorph)
    change HasCompactSupport (fun z => ψ (A.symm (z + -z₀.val))) at h
    simpa only [φ, sub_eq_add_neg] using h
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr]
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hsφ : tsupport φ ⊆ V := by
    intro z hz
    have hy := tsupport_comp_subset_preimage (f := fun z => A.symm (z - z₀)) ψ (by fun_prop) hz
    have h := ht _ hy
    rwa [hinv] at h
  have hop (z : FourSpace) : scalarRescaledOperator g c z₀ r ψ (A.symm (z - z₀)) =
      r ^ 2 * scalarChartOperator g c φ z := by
    have h := scalarRescaledOperator_eq_chart g c z₀ r hr ψ hψ (A.symm (z - z₀))
    rw [hinv] at h
    exact h.symm
  have hsource : (∫ y, (r ^ 2 • scalarAffinePullbackL2 A z₀ F) y * ψ y) =
      r ^ 2 * (scalarAffineJacobian A * ∫ z, F z * φ z) := by
    calc
      _ = ∫ y, r ^ 2 * (scalarAffinePullbackL2 A z₀ F y * ψ y) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul (r ^ 2) (scalarAffinePullbackL2 A z₀ F)] with y hy
        rw [hy]
        change (r ^ 2 * scalarAffinePullbackL2 A z₀ F y) * ψ y = _
        ring
      _ = r ^ 2 * ∫ y, scalarAffinePullbackL2 A z₀ F y * ψ y := integral_const_mul _ _
      _ = _ := by rw [scalarAffineL2_integral]
  rw [hsource, scalarAffineL2_integral]
  change scalarAffineJacobian A * (∫ z, w z * scalarRescaledOperator g c z₀ r ψ
    (A.symm (z - z₀))) = _
  simp_rw [hop]
  have hm : (∫ z, w z * (r ^ 2 * scalarChartOperator g c φ z)) =
      r ^ 2 * ∫ z, w z * scalarChartOperator g c φ z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [hm, hw φ hφ hcφ hsφ]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Concrete chart and coefficient cutoffs for the local regularity
application. The chart cutoff is one on the whole rescaled unit ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology SchwartzMap

noncomputable section

def scalarCoefficientBump : ContDiffBump (0 : FourSpace) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := by norm_num

theorem scalarCoefficientBump_one {y : FourSpace} (hy : y ∈ closedBall 0 1) :
    scalarCoefficientBump y = 1 := scalarCoefficientBump.one_of_mem_closedBall hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar multiplication and the finite partition identity for
actual smooth two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothTwoFormProduct (ρ : SmoothScalar (M := M)) (u : smoothTwoForms o) : smoothTwoForms o :=
  ⟨fun x => ρ.val x • u.val x, u.property.mul ρ.property⟩

variable [T3Space M] [CompactSpace M]

omit [T3Space M] [CompactSpace M] in
theorem smoothTwoForm_partition (P : ScalarPartition M) (u : smoothTwoForms o) :
    (∑ i : P.ι, smoothTwoFormProduct (scalarPartitionFunction P i) u) = u := by
  have hp (x : M) : (∑ i : P.ι, (scalarPartitionFunction P i).val x) = 1 := by
    simpa only [scalarPartitionFunction, finsum_eq_sum_of_fintype] using P.ρ.sum_eq_one (Set.mem_univ x)
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, smoothTwoFormProduct]
  rw [← Finset.sum_smul, hp, one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Critical L4 control of the finite Bessel jets retaining one derivative. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter LineDeriv Set
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)
local notation "S" => 𝓢(V, ℂ)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_8
theorem schwartz_L4_coefficient : ∃ C : ℝ, ∀ φ : S,
    eLpNorm φ 4 volume ≤ (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
      (ENNReal.ofReal C * eLpNorm φ 2 volume +
        ∑ i : Fin 4, eLpNorm
          ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ : S) : V → ℂ) 2 volume) := by
  refine ⟨?C, ?_⟩
  swap
  · intro φ
    exact scalar_schwartz_L4_bound φ

variable (n : ℕ) (is : List (Fin 4)) (h1 : is.length + 1 ≤ n)

def l4JetL2 : L2 →L[ℂ] L2 := scalarBesselJetL2 n is (by omega)

def l4NextJetL2 (j : Fin 4) : L2 →L[ℂ] L2 :=
  scalarBesselJetL2 n (j :: is) (by simp; omega)

def l4JetBound (C B : ℝ) : ℝ≥0∞ :=
  (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
    (ENNReal.ofReal C * ENNReal.ofReal (‖l4JetL2 n is h1‖ * B) +
      ∑ j : Fin 4, ENNReal.ofReal (‖l4NextJetL2 n is h1 j‖ * B))

theorem l4JetBound_lt_top (C B : ℝ) : l4JetBound n is h1 C B < ∞ := by
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

theorem schwartz_jet_L4_bound (C B : ℝ)
    (hC : ∀ φ : S, eLpNorm φ 4 volume ≤ (ScalarEuclideanSobolev.constant : ℝ≥0∞) *
      (ENNReal.ofReal C * eLpNorm φ 2 volume +
        ∑ i : Fin 4, eLpNorm
          ((∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} φ : S) : V → ℂ) 2 volume))
    (φ : S) (hB : ‖φ.toLp 2 volume‖ ≤ B) :
    eLpNorm (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)) 4 volume ≤
      l4JetBound n is h1 C B := by
  apply (hC _).trans
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [schwartz_eLpNorm_two, scalarSchwartzBesselJet_toLp n is (by omega)]
    exact ENNReal.ofReal_le_ofReal (((l4JetL2 n is h1).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hB (norm_nonneg _)))
  · apply Finset.sum_le_sum
    intro j _
    have hd : (∂_{EuclideanSpace.basisFun (Fin 4) ℝ j}
        (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)) : S) =
        scalarSchwartzCoordinateJet (j :: is) (scalarSchwartzIntegerBesselInverse n φ) := rfl
    rw [hd, schwartz_eLpNorm_two, scalarSchwartzBesselJet_toLp n (j :: is) (by simp; omega)]
    exact ENNReal.ofReal_le_ofReal (((l4NextJetL2 n is h1 j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hB (norm_nonneg _)))

/-- The critical four-dimensional estimate applies to each actual derivative
with at least one derivative remaining. -/
theorem scalarBesselJetL2_memLp_four (f : L2) :
    MemLp (scalarBesselJetL2 n is (by omega) f : V → ℂ) 4 volume := by
  obtain ⟨C, hC⟩ := schwartz_L4_coefficient
  obtain ⟨vs, hvs, ht⟩ := mem_closure_iff_seq_limit.mp
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ)
      (μ := (volume : Measure V)) (p := 2) (by norm_num) f)
  choose φ hφ using hvs
  have hconv : Tendsto (fun k => (φ k).toLp 2 volume) atTop (𝓝 f) := by
    have he : (fun k => (φ k).toLp 2 volume) = vs := funext (fun k => hφ k)
    rwa [he]
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hconv).exists_norm_le
  have hB' (k : ℕ) : ‖(φ k).toLp 2 volume‖ ≤ B := hB _ (mem_range_self k)
  have hco (k : ℕ) : (l4JetL2 n is h1 ((φ k).toLp 2 volume) : V → ℂ) =ᵐ[volume]
      scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n (φ k)) := by
    rw [show l4JetL2 n is h1 ((φ k).toLp 2 volume) =
      (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n (φ k))).toLp 2 volume
      from (scalarSchwartzBesselJet_toLp n is (by omega) (φ k)).symm]
    exact SchwartzMap.coeFn_toLp _ _ _
  have hb : ∀ᶠ k in atTop,
      eLpNorm (l4JetL2 n is h1 ((φ k).toLp 2 volume) : V → ℂ) 4 volume ≤
        l4JetBound n is h1 C B := by
    apply Eventually.of_forall
    intro k
    rw [eLpNorm_congr_ae (hco k)]
    exact schwartz_jet_L4_bound n is h1 C B hC (φ k) (hB' k)
  have ht := (l4JetL2 n is h1).continuous.continuousAt.tendsto.comp hconv
  exact ⟨Lp.aestronglyMeasurable _, (eLpNorm_le_of_tendstoInMeasure hb (tendstoInMeasure_of_tendsto_Lp ht)
    (fun _ => (Lp.memLp _).aestronglyMeasurable)).trans_lt (l4JetBound_lt_top n is h1 C B)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual real rescaled equation with the complex
formal-adjoint equation used by the local regularity theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_real_L2_test_integrable (f : Lp ℝ 2 (volume : Measure V))
    (φ : S) (κ : ℝ) :
    Integrable (fun x => φ x * ((κ * f x : ℝ) : ℂ)) :=
  (φ.memLp 2 (volume : Measure V)).integrable_mul ((Lp.memLp f).const_mul κ).ofReal

theorem scalar_normalized_adjoint_test_equation_of_integrable (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (f : V → ℝ)
    (w : Lp ℝ 2 (volume : Measure V)) (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (U : Set V)
    (ha : ∀ x ∈ U, ∀ i j, a i j x =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r x i j - (1 : Mat4) i j) : ℝ) : ℂ))
    (hb : ∀ x ∈ U, ∀ i, b i x =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r x i : ℝ) : ℂ))
    (hw : ∀ ψ : V → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ x, w x * scalarRescaledOperator g c z₀ r ψ x) =
        ∫ x, f x * ψ x)
    (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ U)
    (hi : Integrable (fun x => φ x * ((-((2 * Real.pi) ^ 2)⁻¹ * f x : ℝ) : ℂ))) :
    (scalarFormalAdjointOperator a b (scalarComplexL2 w : T) - (scalarComplexL2 w : T)) φ =
      ∫ x, φ x * ((-((2 * Real.pi) ^ 2)⁻¹ * f x : ℝ) : ℂ) := by
  have hsupport (L : ℂ →L[ℝ] ℝ) : tsupport (L ∘ φ) ⊆ tsupport (φ : V → ℂ) :=
    tsupport_comp_subset L.map_zero φ
  have hcoordinate (L : ℂ →L[ℝ] ℝ) (x : V) :
      L (scalarSchwartzDirectOperator a b φ x - φ x) =
        -((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledOperator g c z₀ r (L ∘ φ) x := by
    by_cases hx : x ∈ tsupport (φ : V → ℂ)
    · exact scalarSchwartzDirectOperator_real_coordinate L
        (scalarRescaledPrincipal g c z₀ r x) (scalarRescaledDrift g c z₀ r x)
        a b φ x (ha x (hs hx)) (hb x (hs hx))
    · rw [scalarSchwartzDirectOperator_zero_off_tsupport a b φ x hx, L.map_zero,
        scalarRescaledOperator_eq_zero_off_tsupport g c z₀ r (L ∘ φ)
          (fun h => hx (hsupport L h)), mul_zero]
  have hcomponent (L : ℂ →L[ℝ] ℝ) :
      L ((scalarFormalAdjointOperator a b (scalarComplexL2 w : T) -
        (scalarComplexL2 w : T)) φ) =
        -((2 * Real.pi) ^ 2)⁻¹ * ∫ x, f x * L (φ x) := by
    rw [sub_apply, scalarFormalAdjointOperator_pairing, ← map_sub,
      scalarComplexL2_pairing_component]
    change (∫ x, w x * L (scalarSchwartzDirectOperator a b φ x - φ x)) = _
    simp_rw [hcoordinate]
    have hm : (∫ x, w x *
        (-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledOperator g c z₀ r (L ∘ φ) x)) =
        -((2 * Real.pi) ^ 2)⁻¹ *
          ∫ x, w x * scalarRescaledOperator g c z₀ r (L ∘ φ) x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hm, hw (L ∘ φ) (L.contDiff.comp (φ.smooth _))
      (hc.comp_left L.map_zero) ((hsupport L).trans hs)]
    rfl
  have hsource (L : ℂ →L[ℝ] ℝ) :
      L (∫ x, φ x * ((-((2 * Real.pi) ^ 2)⁻¹ * f x : ℝ) : ℂ)) =
        -((2 * Real.pi) ^ 2)⁻¹ * ∫ x, f x * L (φ x) := by
    rw [← L.integral_comp_comm hi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_comm (φ x), ← Complex.real_smul, L.map_smul]
    change (-((2 * Real.pi) ^ 2)⁻¹ * f x) * L (φ x) =
      -((2 * Real.pi) ^ 2)⁻¹ * (f x * L (φ x))
    ring
  apply Complex.ext
  · exact (hcomponent Complex.reCLM).trans (hsource Complex.reCLM).symm
  · exact (hcomponent Complex.imCLM).trans (hsource Complex.imCLM).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rellich compactness for the actual scalar H¹ space on the compact
manifold, assembled from the finite smooth partition of unity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rellichCompactness_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rellichCompactness_probability
def smoothScalarBaseL2Linear (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (ContinuousMap.toLp 2 (normalizedVolume g) ℝ).toLinearMap.comp smoothScalarContinuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth partitions and the self-adjoint scalar multiplication
identity in the actual two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem smoothTwoForm_partition_weights {ι : Type*} [Fintype ι]
    (ρ : ι → SmoothScalar (M := M)) (hρ : ∀ x, ∑ i : ι, (ρ i).val x = 1)
    (u : smoothTwoForms o) : (∑ i : ι, smoothTwoFormProduct (ρ i) u) = u := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, smoothTwoFormProduct]
  rw [← Finset.sum_smul, hρ, one_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Density of actual smooth scalar functions in the base L2 space,
needed for the scalar part of the Hodge heat complex. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

variable [SecondCountableTopology M]

local instance scalarBaseSmooth_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rescaled forcing is H1 whenever its intrinsic source is H1. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

theorem scalarComplexL2_real_smul (c : ℝ) (f : Lp ℝ 2 (volume : Measure V)) :
    scalarComplexL2 (c • f) = (c : ℂ) • scalarComplexL2 f := by
  apply Lp.ext
  filter_upwards [scalarComplexL2_coe (c • f), scalarComplexL2_coe f,
    Lp.coeFn_smul c f, Lp.coeFn_smul (c : ℂ) (scalarComplexL2 f)] with x hc hf hs ht
  rw [hc, ht, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hf, Complex.ofReal_mul]

theorem scalarComplexL2_real_smul_distribution (c : ℝ) (f : Lp ℝ 2 (volume : Measure V)) :
    (scalarComplexL2 (c • f) : T) = (c : ℂ) • (scalarComplexL2 f : T) := by
  rw [scalarComplexL2_real_smul]
  exact (Lp.toTemperedDistributionCLM ℂ volume 2).map_smul (c : ℂ) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single smooth approximation controls all the finite jets used in the
nonlinear bootstrap, in L2, L4 and L-infinity at their required orders. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_11
theorem scalarSchwartzBesselJet_toLp_top (n : ℕ) (is : List (Fin 4))
    (h3 : is.length + 3 ≤ n) (φ : S) :
    (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).toLp ∞ volume =
      scalarBesselJetUniform n is h3 (φ.toLp 2 volume) := by
  apply Lp.ext
  have h2 := (scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).coeFn_toLp 2 volume
  rw [scalarSchwartzBesselJet_toLp n is (by omega)] at h2
  have htop : (scalarBesselJetUniform n is h3 (φ.toLp 2 volume) : V → ℂ) =ᵐ[volume]
      scalarBesselJetL2 n is (by omega) (φ.toLp 2 volume) :=
    scalarBesselJetUniform_coe n is h3 (φ.toLp 2 volume)
  filter_upwards [(scalarSchwartzCoordinateJet is (scalarSchwartzIntegerBesselInverse n φ)).coeFn_toLp ∞ volume,
    htop, h2] with x hx htop h2
  exact hx.trans (h2.symm.trans htop.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact scalar components of an actual two-form in an orthonormal
chart frame, expressed by finitely many coordinate cutoffs. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormGramCutoffWeight (g : SmoothMetric M) (c : M) (S : Mat4)
    (χ : FourSpace → ℝ) (v b : Fin 2 → Fin 4) (z : FourSpace) : ℝ :=
  χ z * ∏ k, chartGramMatrix g c S z (b k) (v k)

theorem twoFormGramCutoffWeight_smooth (g : SmoothMetric M) (c : M) (S : Mat4)
    {K : Set FourSpace} (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ K)
    (v b : Fin 2 → Fin 4) : ContDiff ℝ ∞ (twoFormGramCutoffWeight g c S χ v b) := by
  apply scalarCutoff_contDiff χ _ hχ
  intro z hz
  exact contDiffAt_prod (fun k _ => chartGramMatrix_contDiffAt g c S z (hKt (hs hz)) (b k) (v k))

theorem twoFormGramCutoffWeight_support (g : SmoothMetric M) (c : M) (S : Mat4)
    (χ : FourSpace → ℝ) (v b : Fin 2 → Fin 4) :
    tsupport (twoFormGramCutoffWeight g c S χ v b) ⊆ tsupport χ :=
  tsupport_mul_subset_left

theorem twoFormGramCutoffWeight_compact (g : SmoothMetric M) (c : M) (S : Mat4)
    (χ : FourSpace → ℝ) (hc : HasCompactSupport χ) (v b : Fin 2 → Fin 4) :
    HasCompactSupport (twoFormGramCutoffWeight g c S χ v b) := hc.mul_right

def twoFormGramCutoffC1 (c : M) (S : Mat4) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) :
    SmoothH1TwoForm o →ₗ[ℝ] ↥(Euclidean.C1c (E := FourSpace)) :=
  ∑ b : Fin 2 → Fin 4,
    twoFormCutoffC1 c hKt (twoFormGramCutoffWeight g c S χ v b)
      (twoFormGramCutoffWeight_smooth g c S hKt χ hχ hs v b)
      (twoFormGramCutoffWeight_compact g c S χ hc v b)
      ((twoFormGramCutoffWeight_support g c S χ v b).trans hs) b

theorem twoFormGramCutoffC1_apply (c : M) (S : Mat4) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (u : SmoothH1TwoForm o) (z : FourSpace) :
    (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u).val z =
      χ z * frameTensor (chartGramMatrix g c S z) (twoFormCoordinates o (u : smoothTwoForms o).val c z) v := by
  simp only [twoFormGramCutoffC1, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  change (∑ b : Fin 2 → Fin 4, twoFormGramCutoffWeight g c S χ v b z *
    twoFormCoordinates o (u : smoothTwoForms o).val c z b) = _
  simp only [twoFormGramCutoffWeight, frameTensor, Finset.mul_sum, mul_assoc]

theorem twoFormGramCutoffC1_value (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K : Set FourSpace} (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (u : SmoothH1TwoForm o) (z : FourSpace) :
    (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u).val z =
      χ z * twoFormTensor (twoFormChartValue o (u : smoothTwoForms o).val c S hS z) v := by
  rw [twoFormGramCutoffC1_apply]
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · rw [twoFormChartValue_tensor o _ c S hS z hz]
  · have ht : z ∉ tsupport χ := fun h => hz (hKt (hs h))
    rw [image_eq_zero_of_notMem_tsupport ht, zero_mul, zero_mul]

theorem twoFormGramCutoffC1_support (c : M) (S : Mat4) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (v : Fin 2 → Fin 4) (u : SmoothH1TwoForm o) :
    tsupport (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u).val ⊆ K := by
  rw [show (twoFormGramCutoffC1 c S hKt χ hχ hc hs v u).val =
    (fun z => χ z * frameTensor (chartGramMatrix g c S z)
      (twoFormCoordinates o (u : smoothTwoForms o).val c z) v) from
        funext (twoFormGramCutoffC1_apply c S hKt χ hχ hc hs v u)]
  exact tsupport_mul_subset_left.trans hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The existing scalar elliptic estimate applied directly to a genuine
H1 chart component with actual Euclidean integer-order forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

local notation "V4" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V4)
local notation "S" => 𝓢(V4, ℂ)
local notation "T" => 𝓢'(V4, ℂ)

theorem scalarEuclidean_local_integer (n : ℕ) (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (V : Set V4) (hV : V ∈ 𝓝 z₀.val) (w F : L2)
    (hw : MemSobolev 1 2 (scalarComplexL2 w : T))
    (hF : MemSobolev (n : ℝ) 2 (scalarComplexL2 F : T))
    (heq : ∀ (ψ : V4 → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      (∫ z, w z * scalarChartOperator g c ψ z) = ∫ z, F z * ψ z) :
    ∃ (r : ℝ) (hr : 0 < r),
      (∀ y ∈ closedBall (0 : V4) 1, scalarRescaledPoint g c z₀ r y ∈ V) ∧
      ∀ φ : S, HasCompactSupport (φ : V4 → ℂ) → tsupport (φ : V4 → ℂ) ⊆ closedBall 0 (1 / 2) →
        MemSobolev ((n + 2 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2
          (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr.ne') z₀ w) : T)) := by
  obtain ⟨η₁, hη₁, hnear⟩ := Metric.mem_nhds_iff.mp
    (scalarRescaledPoint_compact_eventually g c z₀ (isCompact_closedBall 0 1) V hV)
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  have hpoint (y : V4) (hy : y ∈ closedBall (0 : V4) 1) :
      scalarRescaledPoint g c z₀ r y ∈ V :=
    hnear (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hr₁) y hy
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let w' := scalarAffinePullbackL2 A z₀ w
  let F' : L2 := r ^ 2 • scalarAffinePullbackL2 A z₀ F
  have hw' : MemSobolev 1 2 (scalarComplexL2 w' : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ w hw
  have hA (y : V4) (hy : y ∈ ball (0 : V4) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V4) (hy : y ∈ ball (0 : V4) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hreal (ψ : V4 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
      (hsψ : tsupport ψ ⊆ ball (0 : V4) 1) :
      (∫ y, w' y * scalarRescaledOperator g c z₀ r ψ y) = ∫ y, F' y * ψ y :=
    scalarEuclidean_rescaled_equation g c w F V heq z₀ r hr.ne' ψ hψ hcψ
      (fun y hy => hpoint y (ball_subset_closedBall (hsψ hy)))
  let κ : ℝ := -((2 * Real.pi) ^ 2)⁻¹
  let Ft := scalarComplexL2 (κ • F')
  have hF' : MemSobolev (n : ℝ) 2 (scalarComplexL2 F' : T) := by
    rw [show (scalarComplexL2 F' : T) = ((r ^ 2 : ℝ) : ℂ) •
      (scalarComplexL2 (scalarAffinePullbackL2 A z₀ F) : T) from
        scalarComplexL2_real_smul_distribution (r ^ 2) _]
    exact (scalarAffinePullbackL2_memSobolev_integer n A z₀ F hF).smul _
  have hFt : MemSobolev (n : ℝ) 2 (Ft : T) := by
    rw [show (Ft : T) = (κ : ℂ) • (scalarComplexL2 F' : T) from
      scalarComplexL2_real_smul_distribution κ F']
    exact hF'.smul _
  have hpair (φ : S) : (Ft : T) φ = ∫ y, φ y * ((κ * F' y : ℝ) : ℂ) := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [scalarComplexL2_coe (κ • F'), Lp.coeFn_smul κ F'] with y hc hs
    rw [hc, hs]
    rfl
  have htests (φ : S) (hcφ : HasCompactSupport (φ : V4 → ℂ))
      (hsφ : tsupport (φ : V4 → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w' : T) -
          (scalarComplexL2 w' : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w' : T)) φ = (Ft : T) φ := by
    rw [scalarFormalAdjointOperator_remainder]
    exact (scalar_normalized_adjoint_test_equation_of_integrable g c z₀ r F' w' a b
      (ball 0 1) hA hB hreal φ hcφ hsφ (scalar_real_L2_test_integrable F' φ _)).trans
        (hpair φ).symm
  refine ⟨r, hr, hpoint, ?_⟩
  intro φ hcφ hsφ
  exact scalar_ball_integer_forcing_gain a (scalarAdjointDrift a b)
    scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
    scalarEllipticSmallSize_small n (-scalarAdjointPotential a b)
    (scalarComplexL2 w' : T) (Ft : T) hFt hw' htests
    (1 / 2) (by norm_num) (by norm_num) φ hcφ hsφ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real smooth approximations carrying the same higher-order derivative
limits as their complex Fourier construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter LineDeriv
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℝ)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_14
def scalarRealSchwartzJet : List (Fin 4) → S →L[ℝ] S
  | [] => ContinuousLinearMap.id ℝ S
  | i :: is => (lineDerivOpCLM ℝ S (EuclideanSpace.basisFun (Fin 4) ℝ i)).comp
      (scalarRealSchwartzJet is)

theorem scalarRealSchwartzJet_re (is : List (Fin 4)) (f : 𝓢(V, ℂ)) :
    scalarRealSchwartzJet is (f.postcompCLM Complex.reCLM) =
      (scalarSchwartzCoordinateJet is f).postcompCLM Complex.reCLM := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
      (scalarRealSchwartzJet is (f.postcompCLM Complex.reCLM)) : S) = _
    rw [ih]
    exact scalarSchwartz_re_derivative (scalarSchwartzCoordinateJet is f) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary derivatives of local frame coefficients and their exact
relation to the actual covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormGramCutoffC1_partial (c : M) (S : Mat4) {K : Set FourSpace}
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) (u : SmoothH1TwoForm o)
    (i : Fin 4) (z : FourSpace) :
    partialDeriv (twoFormGramCutoffC1 c S hKt χ hχ hc hs a u).val i z =
      partialDeriv χ i z * frameTensor (chartGramMatrix g c S z)
        (twoFormCoordinates o (u : smoothTwoForms o).val c z) a +
      χ z * tensorPartial (fun w => frameTensor (chartGramMatrix g c S w)
        (twoFormCoordinates o (u : smoothTwoForms o).val c w)) i z a := by
  by_cases hz : z ∈ K
  · have hT := (u : smoothTwoForms o).property.gramTensor_contDiffAt c S z (hKt hz)
    have ha := (contDiffAt_pi.mp hT a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have he : (twoFormGramCutoffC1 c S hKt χ hχ hc hs a u).val = fun w =>
        χ w * frameTensor (chartGramMatrix g c S w) (twoFormCoordinates o (u : smoothTwoForms o).val c w) a :=
      funext (twoFormGramCutoffC1_apply c S hKt χ hχ hc hs a u)
    rw [he]
    exact scalar_partial_product χ _ z (hχ.differentiable (by simp) z) ha i
  · have ht : z ∉ tsupport χ := fun h => hz (hs h)
    have hzero : χ z = 0 := image_eq_zero_of_notMem_tsupport ht
    have hder : partialDeriv χ i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => ht ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h))
    have hp : partialDeriv (twoFormGramCutoffC1 c S hKt χ hχ hc hs a u).val i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz
        (twoFormGramCutoffC1_support c S hKt χ hχ hc hs a u
          ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h)))
    rw [hp, hzero, hder, zero_mul, zero_mul, zero_add]

theorem twoFormGramCutoff_covariant (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K : Set FourSpace} (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : Fin 2 → Fin 4) (u : SmoothH1TwoForm o)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    χ z * frameTensor (chartGramMatrix g c S z)
      (tensorCovariantDirection (connectionMatrix g c)
        (twoFormCoordinates o (u : smoothTwoForms o).val c) i z) a =
      partialDeriv (twoFormGramCutoffC1 c S hKt χ hχ hc hs a u).val i z -
      partialDeriv χ i z * frameTensor (chartGramMatrix g c S z)
        (twoFormCoordinates o (u : smoothTwoForms o).val c z) a -
      χ z * tensorSlotAction (chartTwoFormConnection (g := g) c S i z)
        (frameTensor (chartGramMatrix g c S z) (twoFormCoordinates o (u : smoothTwoForms o).val c z)) a := by
  have hD := twoFormGramCutoffC1_partial c S hKt χ hχ hc hs a u i z
  have hC := congrFun ((u : smoothTwoForms o).property.gramCovariantDirection c S hS z hz i) a
  simp only [Pi.sub_apply] at hC
  have hm := congrArg (fun r : ℝ => χ z * r) hC
  rw [mul_sub] at hm
  linarith only [hD, hm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closedness of all finite real weak jets in the distributional Sobolev space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)

theorem scalarRealSchwartzJet_ofReal (is : List (Fin 4)) (f : S) :
    scalarSchwartzCoordinateJet is (f.postcompCLM Complex.ofRealCLM) =
      (scalarRealSchwartzJet is f).postcompCLM Complex.ofRealCLM := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
      (scalarSchwartzCoordinateJet is (f.postcompCLM Complex.ofRealCLM)) : 𝓢(V, ℂ)) = _
    rw [ih]
    exact scalarSchwartz_ofReal_derivative (scalarRealSchwartzJet is f) i

theorem scalarRealSchwartzJet_weak (is : List (Fin 4)) (f : S) :
    scalarCoordinateJet is (scalarComplexL2 (f.toLp 2 volume) : T) =
      (scalarComplexL2 ((scalarRealSchwartzJet is f).toLp 2 volume) : T) := by
  rw [← scalarSchwartz_ofReal_toLp, Lp.toTemperedDistribution_toLp_eq,
    ← scalarSchwartzCoordinateJet_distribution, scalarRealSchwartzJet_ofReal,
    ← scalarSchwartz_ofReal_toLp, Lp.toTemperedDistribution_toLp_eq]

theorem scalar_real_jet_limit (is : List (Fin 4)) (fs : ℕ → S) (u v : L2)
    (hu : Tendsto (fun k => (fs k).toLp 2 volume) atTop (𝓝 u))
    (hv : Tendsto (fun k => (scalarRealSchwartzJet is (fs k)).toLp 2 volume)
      atTop (𝓝 v)) :
    scalarCoordinateJet is (scalarComplexL2 u : T) = (scalarComplexL2 v : T) := by
  let C := Complex.ofRealCLM.compLpL 2 (volume : Measure V)
  have hC (a : L2) : C a = scalarComplexL2 a := rfl
  have hleft := (scalarCoordinateJet is).continuous.continuousAt.tendsto.comp
    ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp
      (C.continuous.continuousAt.tendsto.comp hu))
  have hright := (Lp.toTemperedDistributionCLM ℂ volume 2).continuous.continuousAt.tendsto.comp
    (C.continuous.continuousAt.tendsto.comp hv)
  have hl : Tendsto (fun k => (scalarComplexL2
      ((scalarRealSchwartzJet is (fs k)).toLp 2 volume) : T)) atTop
      (𝓝 (scalarCoordinateJet is (scalarComplexL2 u : T))) := by
    simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply, hC,
      scalarRealSchwartzJet_weak] using hleft
  have hr : Tendsto (fun k => (scalarComplexL2
      ((scalarRealSchwartzJet is (fs k)).toLp 2 volume) : T)) atTop
      (𝓝 (scalarComplexL2 v : T)) := by
    simpa only [Function.comp_def, Lp.toTemperedDistributionCLM_apply, hC] using hright
  exact tendsto_nhds_unique hl hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local covariant derivatives of intrinsic H1 two-forms as actual
bounded maps into Euclidean L2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCutoffPartial_smooth (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (i : Fin 4) : ContDiff ℝ ∞ (fun z => partialDeriv χ i z) :=
  (hχ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

def twoFormConnectionCutoff (c : M) (S : Mat4) (χ : FourSpace → ℝ)
    (i r s : Fin 4) (z : FourSpace) : ℝ :=
  χ z * chartTwoFormConnection (g := g) c S i z r s

theorem twoFormConnectionCutoff_smooth (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K : Set FourSpace} (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ K)
    (i r s : Fin 4) : ContDiff ℝ ∞ (twoFormConnectionCutoff (g := g) c S χ i r s) :=
  scalarCutoff_contDiff χ _ hχ (fun z hz =>
    chartTwoFormConnection_contDiffAt c S hS i z (hKt (hs hz)) r s)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Division by the actual smooth positive chart density at finite Sobolev orders. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric Filter
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

def integerDensityCutoffL2 (φ : S) (w : L2) : L2 :=
  scalarL2Multiply (φ.toLp ∞ volume) w

theorem integerDensityCutoffL2_distribution (φ : S) (w : L2) :
    (integerDensityCutoffL2 φ w : T) = smulLeftCLM ℂ φ (w : T) := by
  unfold integerDensityCutoffL2
  rw [SchwartzMap.toLp]
  exact scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp ∞ volume) w

theorem integerDensityCutoffL2_coe (φ : S) (w : L2) :
    (integerDensityCutoffL2 φ w : V → ℂ) =ᵐ[volume] fun y => φ y * w y := by
  change (((φ.toLp ∞ volume) • w : L2) : V → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp ∞ volume) w,
    φ.coeFn_toLp ∞ volume] with y hy hφ
  simpa only [smul_eq_mul, Pi.mul_apply, hφ] using hy

theorem integerDensityCutoff_support (χ ρ : V → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hρ : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y) :
    tsupport ((scalarCutoffSchwartz χ (fun y => (ρ y)⁻¹) hχ hc hρ) : V → ℂ) ⊆
      tsupport χ :=
  (tsupport_comp_subset (g := Complex.ofReal) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    (fun y => χ y * (ρ y)⁻¹)).trans tsupport_mul_subset_left

theorem scalar_integer_density_division (n : ℕ) (ρ b : V → ℝ) (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => ρ y * b y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ ball (0 : V) (1 / 2))
    (hρ : ∀ y ∈ tsupport χ, ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y)
    (hρ0 : ∀ y ∈ tsupport χ, ρ y ≠ 0) :
    ∃ v : L2, MemSobolev (n : ℝ) 2 (v : T) ∧
      (v : V → ℂ) =ᵐ[volume] fun y => (χ y * b y : ℝ) := by
  let φ := scalarCutoffSchwartz χ (fun y => (ρ y)⁻¹) hχ hc hρ
  have hφχ : tsupport (φ : V → ℂ) ⊆ tsupport χ := integerDensityCutoff_support χ ρ hχ hc hρ
  have hφc : HasCompactSupport (φ : V → ℂ) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hφχ
  have hφs : tsupport (φ : V → ℂ) ⊆ ball (0 : V) (1 / 2) :=
    hφχ.trans hs
  refine ⟨integerDensityCutoffL2 φ (scalarComplexL2 w), ?_, ?_⟩
  · rw [integerDensityCutoffL2_distribution]
    exact hreg φ hφc hφs
  have hglob := (ae_restrict_iff' isOpen_ball.measurableSet).mp heq
  filter_upwards [integerDensityCutoffL2_coe φ (scalarComplexL2 w), scalarComplexL2_coe w,
    hglob] with y hv hw hy
  rw [hv, hw]
  change ((χ y * (ρ y)⁻¹ : ℝ) : ℂ) * (w y : ℂ) = _
  by_cases hz : χ y = 0
  · simp only [hz, zero_mul, Complex.ofReal_zero]
  · have ht : y ∈ tsupport χ := subset_tsupport χ hz
    have hin : y ∈ ball (0 : V) 1 := ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1) (hs ht)
    rw [← hy hin, ← Complex.ofReal_mul]
    congr 1
    calc
      χ y * (ρ y)⁻¹ * (ρ y * b y) = χ y * ((ρ y)⁻¹ * ρ y) * b y := by ring
      _ = χ y * b y := by rw [inv_mul_cancel₀ (hρ0 y ht), mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Six-component Euclidean L2 realizations of the local two-form and
its covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem twoFormTensor_component (a : TwoFormFour) (r : Fin 6) :
    twoFormTensor a (twoFormComponentIndex r) = a r := by
  fin_cases r <;> rfl

theorem twoForm_sum_components (a : TwoFormFour) :
    (∑ r : Fin 6, a r • (EuclideanSpace.basisFun (Fin 6) ℝ) r) = a := by
  ext r
  simp [EuclideanSpace.basisFun_apply, Pi.single_apply, smul_eq_mul]

def twoFormComponentL2 (r : Fin 6) :
    Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((EuclideanSpace.basisFun (Fin 6) ℝ) r)).compLpL 2 volume

theorem twoFormComponentL2_coe (r : Fin 6) (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    twoFormComponentL2 r f =ᵐ[volume]
      fun z => f z • (EuclideanSpace.basisFun (Fin 6) ℝ) r :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((EuclideanSpace.basisFun (Fin 6) ℝ) r)).coeFn_compLpL f

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormAssembleL2 (F : Fin 6 → TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace)) :
    TwoFormH1 o →L[ℝ] Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  ∑ r : Fin 6, (twoFormComponentL2 r).comp (F r)

theorem twoFormAssembleL2_coe
    (F : Fin 6 → TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace))
    (u : TwoFormH1 o) (a : FourSpace → TwoFormFour)
    (ha : ∀ r, F r u =ᵐ[volume] fun z => a z r) :
    twoFormAssembleL2 F u =ᵐ[volume] a := by
  have he : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ r : Fin 6,
      twoFormComponentL2 r (F r u) z = a z r • (EuclideanSpace.basisFun (Fin 6) ℝ) r := by
    apply Filter.eventually_all.mpr
    intro r
    filter_upwards [twoFormComponentL2_coe r (F r u), ha r] with z hc hz
    rw [hc, hz]
  have hsumA : twoFormAssembleL2 F u = ∑ r : Fin 6, twoFormComponentL2 r (F r u) := by
    simp only [twoFormAssembleL2, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rw [hsumA]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun r => twoFormComponentL2 r (F r u)), he]
    with z hsum hz
  rw [hsum]
  change (∑ r, twoFormComponentL2 r (F r u) z) = a z
  simp_rw [hz]
  exact twoForm_sum_components (a z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact chart value map extends from smooth sections to
the intrinsic L2 completion. Its bound uses only the chart volume density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothL2AsH1 : SmoothL2TwoForm o →ₗ[ℝ] SmoothH1TwoForm o where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The mass and first-order coefficients of an actual compact chart
test form are smooth, compactly supported Euclidean L2 functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormLocalNabla_contDiffAt (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (ha : ContDiffAt ℝ ∞ a z) (i : Fin 4) :
    ContDiffAt ℝ ∞ (twoFormLocalNabla (g := g) c S a i) z := by
  have hsum : ContDiffAt ℝ ∞ (fun w => ∑ r : Fin 6, a w r •
      twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i w))
        ((EuclideanSpace.basisFun (Fin 6) ℝ) r)) z := by
    apply ContDiffAt.sum
    intro r _
    exact ((PiLp.proj 2 (fun _ : Fin 6 => ℝ) r).contDiff.comp_contDiffAt z ha).smul
      (twoFormConnectionAction_contDiffAt c S hS i z hz _)
  have he (w : FourSpace) :
      twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i w)) (a w) =
        ∑ r : Fin 6, a w r •
          twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i w))
            ((EuclideanSpace.basisFun (Fin 6) ℝ) r) := by
    let L := twoFormSkewActionLinear (twoFormExtract (chartTwoFormConnection (g := g) c S i w))
    calc
      _ = L (∑ r : Fin 6, a w r • (EuclideanSpace.basisFun (Fin 6) ℝ) r) :=
        congrArg L (twoForm_sum_components (a w)).symm
      _ = _ := by rw [map_sum]; simp only [map_smul]; rfl
  exact ((ha.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const).add
    (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall he))

def twoFormMassTest (c : M) (a : FourSpace → TwoFormFour) (z : FourSpace) : TwoFormFour :=
  chartVolumeDensity g c z • a z

def twoFormEnergyTest (c : M) (S : Mat4) (a : FourSpace → TwoFormFour)
    (i : Fin 4) (z : FourSpace) : TwoFormFour :=
  chartVolumeDensity g c z • ∑ j : Fin 4,
    (metricInChart g c z)⁻¹ i j • twoFormLocalNabla (g := g) c S a j z

theorem twoFormMassTest_support (c : M) (a : FourSpace → TwoFormFour) :
    tsupport (twoFormMassTest (g := g) c a) ⊆ tsupport a :=
  tsupport_smul_subset_right _ _

theorem twoFormEnergyTest_support (c : M) (S : Mat4) (a : FourSpace → TwoFormFour)
    (i : Fin 4) : tsupport (twoFormEnergyTest (g := g) c S a i) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro z hz
  by_contra hn
  have he (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z hn j
  apply hz
  simp only [twoFormEnergyTest, he, smul_zero, Finset.sum_const_zero]

theorem twoFormMassTest_smooth (c : M) (a : FourSpace → TwoFormFour)
    (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    (hs : tsupport a ⊆ (chartAt FourSpace c).target) :
    ContDiff ℝ ∞ (twoFormMassTest (g := g) c a) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · exact (chartVolumeDensity_contDiffAt g c z hz).smul
      ((ha z hz).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hz))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hs (twoFormMassTest_support c a h))))

theorem twoFormEnergyTest_smooth (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    (hs : tsupport a ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    ContDiff ℝ ∞ (twoFormEnergyTest (g := g) c S a i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · apply (chartVolumeDensity_contDiffAt g c z hz).smul
    apply ContDiffAt.sum
    intro j _
    exact (scalarPrincipalCoefficients_smooth g c z hz i j).smul
      (twoFormLocalNabla_contDiffAt c S hS a z hz
        ((ha z hz).contDiffAt ((chartAt FourSpace c).open_target.mem_nhds hz)) j)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp
        (fun h => hz (hs (twoFormEnergyTest_support c S a i h))))

def twoFormMassTestL2 (c : M) (a : FourSpace → TwoFormFour)
    (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ (chartAt FourSpace c).target) :
    Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  ((twoFormMassTest_smooth (g := g) c a ha hs).continuous.memLp_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (twoFormMassTest_support (g := g) c a))).toLp
      (twoFormMassTest (g := g) c a)

def twoFormEnergyTestL2 (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  ((twoFormEnergyTest_smooth (g := g) c S hS a ha hs i).continuous.memLp_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (twoFormEnergyTest_support (g := g) c S a i))).toLp
      (twoFormEnergyTest (g := g) c S a i)

theorem twoFormMassTestL2_coe (c : M) (a : FourSpace → TwoFormFour)
    (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ (chartAt FourSpace c).target) :
    twoFormMassTestL2 (g := g) c a ha hc hs =ᵐ[volume] twoFormMassTest (g := g) c a :=
  MemLp.coeFn_toLp _

theorem twoFormEnergyTestL2_coe (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (a : FourSpace → TwoFormFour) (ha : ContDiffOn ℝ ∞ a (chartAt FourSpace c).target)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    twoFormEnergyTestL2 (g := g) c S hS a ha hc hs i =ᵐ[volume] twoFormEnergyTest (g := g) c S a i :=
  MemLp.coeFn_toLp _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six L2 coordinates of the actual localized two-form inherit the
first-order distributional regularity of the H1 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped Manifold ContDiff SchwartzMap

noncomputable section

def twoFormVectorComponentL2 (r : Fin 6) :
    Lp TwoFormFour 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (PiLp.proj 2 (fun _ : Fin 6 => ℝ) r).compLpL 2 volume

theorem twoFormVectorComponentL2_coe (r : Fin 6)
    (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    twoFormVectorComponentL2 r f =ᵐ[volume] fun z => f z r :=
  (PiLp.proj 2 (fun _ : Fin 6 => ℝ) r : TwoFormFour →L[ℝ] ℝ).coeFn_compLpL
    (p := 2) (μ := (volume : Measure FourSpace)) f

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormVectorComponentL2_assemble
    (F : Fin 6 → TwoFormH1 o →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace))
    (u : TwoFormH1 o) (r : Fin 6) :
    twoFormVectorComponentL2 r (twoFormAssembleL2 F u) = F r u := by
  let a : FourSpace → TwoFormFour := fun z => WithLp.toLp 2 (fun k => F k u z)
  have ha : twoFormAssembleL2 F u =ᵐ[volume] a :=
    twoFormAssembleL2_coe F u a (fun _ => Filter.Eventually.of_forall (fun _ => rfl))
  apply Lp.ext
  filter_upwards [twoFormVectorComponentL2_coe r (twoFormAssembleL2 F u), ha] with z hp hz
  exact hp.trans (congrArg (fun v : TwoFormFour => v r) hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Products with one extra Sobolev derivative, including the H2 endpoint,
for the localized positive-power bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_real_sobolev_smul (s r : ℝ) (u : L2)
    (hu : MemSobolev s 2 (scalarComplexL2 u : T)) :
    MemSobolev s 2 (scalarComplexL2 (r • u) : T) := by
  rw [scalarComplexL2_real_smul_distribution]
  exact hu.smul (r : ℂ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pairing an L2 two-form coefficient with a smooth compact vector
coefficient is a bounded map into scalar L2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set

noncomputable section

variable (b : FourSpace → TwoFormFour) (hb : Continuous b) (hc : HasCompactSupport b)

include hb hc

theorem twoFormCoefficient_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖b z‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hc.isCompact_range hb).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun z => (hC _ (mem_range_self z)).trans (le_max_left _ _)⟩

def twoFormCoefficientBound : ℝ := Classical.choose (twoFormCoefficient_bound b hb hc)

theorem twoFormCoefficientBound_le (z : FourSpace) : ‖b z‖ ≤ twoFormCoefficientBound b hb hc :=
  (Classical.choose_spec (twoFormCoefficient_bound b hb hc)).2 z

theorem twoFormCoefficientPair_memLp (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    MemLp (fun z => inner ℝ (f z) (b z)) 2 volume := by
  apply (Lp.memLp f).of_le_mul ((Lp.aestronglyMeasurable f).inner hb.aestronglyMeasurable)
  filter_upwards with z
  exact (norm_inner_le_norm (f z) (b z)).trans
    ((mul_le_mul_of_nonneg_left (twoFormCoefficientBound_le b hb hc z) (norm_nonneg _)).trans_eq
      (mul_comm _ _))

def twoFormCoefficientPair (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  (twoFormCoefficientPair_memLp b hb hc f).toLp _

theorem twoFormCoefficientPair_coe (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    twoFormCoefficientPair b hb hc f =ᵐ[volume] fun z => inner ℝ (f z) (b z) :=
  MemLp.coeFn_toLp _

def twoFormCoefficientPairLinear :
    Lp TwoFormFour 2 (volume : Measure FourSpace) →ₗ[ℝ] Lp ℝ 2 (volume : Measure FourSpace) where
  toFun := twoFormCoefficientPair b hb hc
  map_add' f h := by
    apply Lp.ext
    filter_upwards [twoFormCoefficientPair_coe b hb hc (f + h),
      twoFormCoefficientPair_coe b hb hc f, twoFormCoefficientPair_coe b hb hc h,
      Lp.coeFn_add f h, Lp.coeFn_add (twoFormCoefficientPair b hb hc f)
        (twoFormCoefficientPair b hb hc h)] with z hsum hf hh hfh hp
    rw [hsum, hfh, Pi.add_apply, inner_add_left, hp, Pi.add_apply, hf, hh]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [twoFormCoefficientPair_coe b hb hc (r • f),
      twoFormCoefficientPair_coe b hb hc f, Lp.coeFn_smul r f,
      Lp.coeFn_smul r (twoFormCoefficientPair b hb hc f)] with z hrf hf hs hp
    simp only [RingHom.id_apply]
    rw [hrf, hs, Pi.smul_apply, real_inner_smul_left, hp, Pi.smul_apply, hf]
    rfl

theorem twoFormCoefficientPair_norm (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    ‖twoFormCoefficientPair b hb hc f‖ ≤ twoFormCoefficientBound b hb hc * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [twoFormCoefficientPair_coe b hb hc f] with z hz
  rw [hz]
  exact (norm_inner_le_norm (f z) (b z)).trans
    ((mul_le_mul_of_nonneg_left (twoFormCoefficientBound_le b hb hc z) (norm_nonneg _)).trans_eq
      (mul_comm _ _))

def twoFormCoefficientPairL2 :
    Lp TwoFormFour 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (twoFormCoefficientPairLinear b hb hc).mkContinuous (twoFormCoefficientBound b hb hc)
    (twoFormCoefficientPair_norm b hb hc)

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

theorem twoFormTensor_coordinate_expansion (a : TwoFormFour) (v : Fin 2 → Fin 4) :
    twoFormTensor a v = ∑ r : Fin 6, a r * twoFormTensor (EuclideanSpace.basisFun (Fin 6) ℝ r) v := by
  have h := congrArg (fun x : TwoFormFour => twoFormTensorLinear x v) (twoForm_sum_components a)
  simp only [map_sum, map_smul] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Separating the scalar test derivative from the connection term in
the actual two-form weak equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormLocalNabla_smul_const (c : M) (S : Mat4)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (b : TwoFormFour) (i : Fin 4) (z : FourSpace) :
    twoFormLocalNabla (g := g) c S (fun w => ψ w • b) i z =
      partialDeriv ψ i z • b + ψ z •
        twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i z)) b := by
  have hd := ((hψ.differentiable (by simp) z).hasFDerivAt.smul_const b).fderiv
  unfold twoFormLocalNabla
  rw [hd]
  have hc := (twoFormSkewActionLinear
    (twoFormExtract (chartTwoFormConnection (g := g) c S i z))).map_smul (ψ z) b
  change partialDeriv ψ i z • b + _ = _
  exact congrArg (fun v => partialDeriv ψ i z • b + v) hc

def twoFormWeightedConnection (c : M) (S : Mat4) (b : TwoFormFour)
    (i : Fin 4) (z : FourSpace) : TwoFormFour :=
  chartVolumeDensity g c z • ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j •
    twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S j z)) b

theorem twoFormEnergyTest_smul_const (c : M) (S : Mat4)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (b : TwoFormFour) (i : Fin 4) (z : FourSpace) :
    twoFormEnergyTest (g := g) c S (fun w => ψ w • b) i z =
      (∑ j : Fin 4, (chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j * partialDeriv ψ j z) • b) +
      ψ z • twoFormWeightedConnection (g := g) c S b i z := by
  simp only [twoFormEnergyTest, twoFormLocalNabla_smul_const c S ψ hψ,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum, twoFormWeightedConnection, smul_smul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc]
  · apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring

theorem twoFormWeightedConnection_contDiffAt (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (b : TwoFormFour) (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (twoFormWeightedConnection (g := g) c S b i) z := by
  apply (chartVolumeDensity_contDiffAt g c z hz).smul
  exact ContDiffAt.sum (fun j _ => (scalarPrincipalCoefficients_smooth g c z hz i j).smul
    (twoFormConnectionAction_contDiffAt c S hS j z hz b))

theorem twoFormCutoffWeightedConnection_smooth (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (b : TwoFormFour) (i : Fin 4) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target) :
    ContDiff ℝ ∞ (fun z => χ z • twoFormWeightedConnection (g := g) c S b i z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport χ
  · exact hχ.contDiffAt.smul (twoFormWeightedConnection_contDiffAt c S hS b i z (hs hz))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
    rw [hw]
    exact zero_smul _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth compact coefficients for the actual Weitzenböck potential in
an orthonormal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormChartPotential (c : M) (S : Mat4) (z : FourSpace) : TwoFormFour →L[ℝ] TwoFormFour :=
  (2 : ℝ) • twoFormCurvatureOperator (frameTensor (chartGramMatrix g c S z)
    (curvatureCoordinates g c z)) - (5 : ℝ) • ContinuousLinearMap.id ℝ TwoFormFour

theorem twoFormChartPotential_contDiffAt (c : M) (S : Mat4) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (twoFormChartPotential (g := g) c S) z :=
  ((twoFormCurvatureOperator.contDiff.contDiffAt.comp z
    (chartMetricCurvature_contDiffAt c S z hz)).const_smul (2 : ℝ)).sub contDiffAt_const

def twoFormPotentialCoefficient (c : M) (S : Mat4) (η : FourSpace → ℝ) (r : Fin 6)
    (z : FourSpace) : TwoFormFour :=
  η z • WithLp.toLp 2 (fun k : Fin 6 =>
    twoFormChartPotential (g := g) c S z (EuclideanSpace.basisFun (Fin 6) ℝ k) r)

theorem twoFormPotentialCoefficient_smooth (c : M) (S : Mat4)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η)
    (hs : tsupport η ⊆ (chartAt FourSpace c).target) (r : Fin 6) :
    ContDiff ℝ ∞ (twoFormPotentialCoefficient (g := g) c S η r) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  apply scalarCutoff_contDiff η _ hη
  intro z hz
  exact (PiLp.proj 2 (fun _ : Fin 6 => ℝ) r).contDiff.contDiffAt.comp z
    ((twoFormChartPotential_contDiffAt c S z (hs hz)).clm_apply contDiffAt_const)

theorem twoFormPotentialCoefficient_compact (c : M) (S : Mat4)
    (η : FourSpace → ℝ) (hc : HasCompactSupport η) (r : Fin 6) :
    HasCompactSupport (twoFormPotentialCoefficient (g := g) c S η r) := hc.smul_right

theorem twoForm_linear_coordinate (L : TwoFormFour →L[ℝ] TwoFormFour)
    (a : TwoFormFour) (r : Fin 6) :
    L a r = ∑ k : Fin 6, a k * L (EuclideanSpace.basisFun (Fin 6) ℝ k) r := by
  have h := congrArg (fun x : TwoFormFour => L x r) (twoForm_sum_components a)
  simp only [map_sum, map_smul] at h
  exact h.symm

theorem twoFormPotentialCoefficient_pair (c : M) (S : Mat4)
    (η : FourSpace → ℝ) (r : Fin 6) (a : TwoFormFour) (z : FourSpace) :
    inner ℝ a (twoFormPotentialCoefficient (g := g) c S η r z) =
      η z * twoFormChartPotential (g := g) c S z a r := by
  rw [twoForm_linear_coordinate]
  simp only [twoFormPotentialCoefficient, inner_smul_right, PiLp.inner_apply,
    RCLike.inner_apply', conj_trivial]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth compact coefficient paired with an H1 two-form is H1.
This supplies L2 derivatives of the lower-order connection terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped BigOperators SchwartzMap ENNReal ContDiff

noncomputable section

variable (b : FourSpace → TwoFormFour) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)

def twoFormCoefficientSchwartz (r : Fin 6) : 𝓢(FourSpace, ℂ) :=
  let L : TwoFormFour →L[ℝ] ℂ := Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 6 => ℝ) r)
  (hc.comp_left (g := L) (map_zero L)).toSchwartzMap (L.contDiff.comp hb)

theorem twoFormCoefficientPair_complex (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hc f) =
      ∑ r : Fin 6, scalarL2Multiply ((twoFormCoefficientSchwartz b hb hc r).toLp (∞ : ℝ≥0∞) volume)
        (scalarComplexL2 (twoFormVectorComponentL2 r f)) := by
  let P : Fin 6 → Lp ℂ 2 (volume : Measure FourSpace) := fun r => scalarL2Multiply ((twoFormCoefficientSchwartz b hb hc r).toLp (∞ : ℝ≥0∞) volume)
    (scalarComplexL2 (twoFormVectorComponentL2 r f))
  have hp : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ r : Fin 6,
      P r z = (b z r : ℂ) * (f z r : ℂ) := by
    apply Filter.eventually_all.mpr
    intro r
    filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) ((twoFormCoefficientSchwartz b hb hc r).toLp (∞ : ℝ≥0∞) volume)
        (scalarComplexL2 (twoFormVectorComponentL2 r f)),
      (twoFormCoefficientSchwartz b hb hc r).coeFn_toLp (∞ : ℝ≥0∞) volume,
      scalarComplexL2_coe (twoFormVectorComponentL2 r f), twoFormVectorComponentL2_coe r f]
        with z hmul hcoef hreal hcomp
    change (((twoFormCoefficientSchwartz b hb hc r).toLp (∞ : ℝ≥0∞) volume) •
      scalarComplexL2 (twoFormVectorComponentL2 r f)) z = _
    rw [hmul]
    change ((twoFormCoefficientSchwartz b hb hc r).toLp (∞ : ℝ≥0∞) volume) z *
      scalarComplexL2 (twoFormVectorComponentL2 r f) z = _
    rw [hcoef, hreal, hcomp]
    rfl
  apply Lp.ext
  filter_upwards [scalarComplexL2_coe (twoFormCoefficientPairL2 b hb.continuous hc f),
    twoFormCoefficientPair_coe b hb.continuous hc f, Lp.coeFn_finsetSum Finset.univ P, hp]
    with z hreal hpair hsum hpz
  rw [hreal]
  change (twoFormCoefficientPair b hb.continuous hc f z : ℂ) = _
  rw [hpair, hsum]
  change (inner ℝ (f z) (b z) : ℂ) = ∑ r : Fin 6, P r z
  simp_rw [hpz]
  simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial]
  change Complex.ofRealHom (∑ r : Fin 6, f z r * b z r) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change (↑(f z r * b z r) : ℂ) = ↑(b z r) * ↑(f z r)
  rw [Complex.ofReal_mul, mul_comm]

theorem twoFormCoefficientPair_distribution (f : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    (scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hc f) : 𝓢'(FourSpace, ℂ)) =
      ∑ r : Fin 6, smulLeftCLM ℂ (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) := by
  rw [twoFormCoefficientPair_complex b hb hc f]
  change (Lp.toTemperedDistributionCLM ℂ volume 2) (∑ r : Fin 6,
    scalarL2Multiply ((twoFormCoefficientSchwartz b hb hc r).toLp (∞ : ℝ≥0∞) volume)
      (scalarComplexL2 (twoFormVectorComponentL2 r f))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  exact scalarL2Multiply_distribution _ (twoFormCoefficientSchwartz b hb hc r).hasTemperateGrowth
    ((twoFormCoefficientSchwartz b hb hc r).memLp (∞ : ℝ≥0∞) volume) _

theorem twoFormCoefficientPair_memSobolev_one (f : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (hf : ∀ r : Fin 6, MemSobolev 1 2
      (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev 1 2 (scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hc f) :
      𝓢'(FourSpace, ℂ)) := by
  rw [twoFormCoefficientPair_distribution]
  have hs (s : Finset (Fin 6)) : MemSobolev 1 2 (∑ r ∈ s,
      smulLeftCLM ℂ (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero FourSpace ℂ 1 2
    | @insert r s hr ih =>
      rw [Finset.sum_insert hr]
      have hfr : MemSobolev ((1 : ℕ) : ℝ) 2
          (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) := by
        simpa only [Nat.cast_one] using hf r
      have hm := scalar_memSobolev_schwartz_multiplier 1 (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) hfr
      have hm' := hm.add (by simpa only [Nat.cast_one] using ih)
      simpa only [Nat.cast_one] using hm'
  exact hs Finset.univ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Duality between scalar L2 coefficient pairing and compact vector
tests. These identities keep the actual pointwise test functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set

noncomputable section

def twoFormWeightedTestL2 (b : FourSpace → TwoFormFour) (hb : Continuous b)
    (hc : HasCompactSupport b) (ψ : FourSpace → ℝ) (hψ : Continuous ψ) :
    Lp TwoFormFour 2 (volume : Measure FourSpace) :=
  ((hψ.smul hb).memLp_of_hasCompactSupport hc.smul_left).toLp (fun z => ψ z • b z)

theorem twoFormWeightedTestL2_coe (b : FourSpace → TwoFormFour) (hb : Continuous b)
    (hc : HasCompactSupport b) (ψ : FourSpace → ℝ) (hψ : Continuous ψ) :
    twoFormWeightedTestL2 b hb hc ψ hψ =ᵐ[volume] fun z => ψ z • b z :=
  MemLp.coeFn_toLp _

theorem twoFormCoefficientPair_test (b : FourSpace → TwoFormFour) (hb : Continuous b)
    (hc : HasCompactSupport b) (f : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (ψ : FourSpace → ℝ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    inner ℝ (twoFormCoefficientPairL2 b hb hc f)
      ((hψ.memLp_of_hasCompactSupport hcψ).toLp ψ) =
      inner ℝ f (twoFormWeightedTestL2 b hb hc ψ hψ) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [twoFormCoefficientPair_coe b hb hc f,
    (hψ.memLp_of_hasCompactSupport hcψ).coeFn_toLp,
    twoFormWeightedTestL2_coe b hb hc ψ hψ] with z hbz hψz htz
  change inner ℝ (twoFormCoefficientPair b hb hc f z) _ = _
  rw [hbz, hψz, htz, real_inner_smul_right]
  simp only [RCLike.inner_apply', conj_trivial]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Concrete smooth coefficients for the scalar component divergence
equations of a two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormMassCoefficient (c : M) (χ : FourSpace → ℝ) (b : TwoFormFour) (z : FourSpace) : TwoFormFour :=
  (χ z * chartVolumeDensity g c z) • b

def twoFormFluxCoefficient (c : M) (χ : FourSpace → ℝ) (b : TwoFormFour)
    (i j : Fin 4) (z : FourSpace) : TwoFormFour :=
  (χ z * (chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j)) • b

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (χ : FourSpace → ℝ)
  (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ (chartAt FourSpace c).target) (b : TwoFormFour)

include hχ hs

theorem twoFormMassCoefficient_smooth : ContDiff ℝ ∞ (twoFormMassCoefficient (g := g) c χ b) :=
  (scalarCutoff_contDiff χ (chartVolumeDensity g c) hχ
    (fun z hz => chartVolumeDensity_contDiffAt g c z (hs hz))).smul contDiff_const

theorem twoFormFluxCoefficient_smooth (i j : Fin 4) :
    ContDiff ℝ ∞ (twoFormFluxCoefficient (g := g) c χ b i j) :=
  (scalarCutoff_contDiff χ _ hχ (fun z hz =>
    (chartVolumeDensity_contDiffAt g c z (hs hz)).mul
      (scalarPrincipalCoefficients_smooth g c z (hs hz) i j))).smul contDiff_const

def twoFormMassPair :
    Lp TwoFormFour 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormCoefficientPairL2 (twoFormMassCoefficient (g := g) c χ b)
    (twoFormMassCoefficient_smooth (g := g) c χ hχ hs b).continuous hc.mul_right.smul_right

def twoFormFluxPair (i j : Fin 4) :
    Lp TwoFormFour 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormCoefficientPairL2 (twoFormFluxCoefficient (g := g) c χ b i j)
    (twoFormFluxCoefficient_smooth (g := g) c χ hχ hs b i j).continuous hc.mul_right.smul_right

def twoFormConnectionPair (i : Fin 4) :
    Lp TwoFormFour 2 (volume : Measure FourSpace) →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormCoefficientPairL2 (fun z => χ z • twoFormWeightedConnection (g := g) c S b i z)
    (twoFormCutoffWeightedConnection_smooth c S hS b i χ hχ hs).continuous hc.smul_right

def twoFormDivergenceFlux (N : Fin 4 → Lp TwoFormFour 2 (volume : Measure FourSpace)) (j : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  ∑ i : Fin 4, twoFormFluxPair (g := g) c χ hχ hc hs b i j (N i)

def twoFormDivergenceSource (V F : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (N : Fin 4 → Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormMassPair (g := g) c χ hχ hc hs b (F - V) -
    ∑ i : Fin 4, twoFormConnectionPair (g := g) c S hS χ hχ hc hs b i (N i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite family of compact coordinate maps controls the global
two-form L2 value map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormValueNormL2_partition (P : ScalarPartition M) (u : smoothTwoForms o) :
    ‖twoFormValueNormL2 u‖ ≤ ∑ i : P.ι,
      ‖twoFormValueNormL2 (smoothTwoFormProduct (scalarPartitionFunction P i) u)‖ := by
  let R := fun i : P.ι => twoFormValueNormL2 (smoothTwoFormProduct (scalarPartitionFunction P i) u)
  have hall : ∀ᵐ x ∂normalizedVolume g, ∀ i : P.ι,
      R i x = ‖(smoothTwoFormProduct (scalarPartitionFunction P i) u).val x‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact twoFormValueNormL2_coe (smoothTwoFormProduct (scalarPartitionFunction P i) u)
  have hpoint (x : M) : ‖u.val x‖ ≤ ∑ i : P.ι,
      ‖(smoothTwoFormProduct (scalarPartitionFunction P i) u).val x‖ := by
    have he := congrArg (fun w : smoothTwoForms o => w.val x) (smoothTwoForm_partition P u)
    simp only [Submodule.coe_sum, Finset.sum_apply] at he
    rw [← he]
    exact norm_sum_le _ _
  have hdom : ‖twoFormValueNormL2 u‖ ≤ ‖∑ i : P.ι, R i‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hall, Lp.coeFn_finsetSum Finset.univ R,
      twoFormValueNormL2_coe u]
        with x hx hsum hval
    rw [hval, hsum]
    simp only [Finset.sum_apply, Real.norm_eq_abs]
    simp_rw [hx]
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact hpoint x
  exact hdom.trans (norm_sum_le _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact smooth cutoff transfers Sobolev regularity from a local
almost-everywhere representative to the actual L2 function. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal ContDiff BigOperators

noncomputable section

theorem scalar_local_sobolev_transfer (n : ℕ) (f : Lp ℝ 2 (volume : Measure FourSpace))
    (v : Lp ℂ 2 (volume : Measure FourSpace)) (hv : MemSobolev (n : ℝ) 2 (v : 𝓢'(FourSpace, ℂ)))
    (U : Set FourSpace) (hU : MeasurableSet U)
    (he : (v : FourSpace → ℂ) =ᵐ[volume.restrict U] fun z => (f z : ℂ))
    (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ U) :
    MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ (fun z => (a z : ℂ))
      (scalarComplexL2 f : 𝓢'(FourSpace, ℂ))) := by
  let φ : 𝓢(FourSpace, ℂ) := (hc.toSchwartzMap ha).postcompCLM Complex.ofRealCLM
  let A := φ.toLp (∞ : ℝ≥0∞) volume
  have hlocal := (ae_restrict_iff' hU).mp he
  have hmul : scalarL2Multiply A (scalarComplexL2 f) = scalarL2Multiply A v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) A (scalarComplexL2 f),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) A v, φ.coeFn_toLp (∞ : ℝ≥0∞) volume,
      scalarComplexL2_coe f, hlocal] with z hleft hright hA hf hz
    change (A • scalarComplexL2 f : Lp ℂ 2 volume) z = (A • v : Lp ℂ 2 volume) z
    rw [hleft, hright]
    change A z * scalarComplexL2 f z = A z * v z
    rw [hA, hf]
    change (a z : ℂ) * (f z : ℂ) = (a z : ℂ) * v z
    by_cases hza : a z = 0
    · simp only [hza, Complex.ofReal_zero, zero_mul]
    · rw [hz (hs (subset_tsupport a hza))]
  have hdist := congrArg (fun w : Lp ℂ 2 (volume : Measure FourSpace) =>
    (w : 𝓢'(FourSpace, ℂ))) hmul
  change (scalarL2Multiply (φ.toLp (∞ : ℝ≥0∞) volume) (scalarComplexL2 f) :
    𝓢'(FourSpace, ℂ)) = (scalarL2Multiply (φ.toLp (∞ : ℝ≥0∞) volume) v :
      𝓢'(FourSpace, ℂ)) at hdist
  simp only [SchwartzMap.toLp] at hdist
  rw [scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp (∞ : ℝ≥0∞) volume),
    scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp (∞ : ℝ≥0∞) volume)] at hdist
  change MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 f : 𝓢'(FourSpace, ℂ)))
  rw [hdist]
  exact scalar_memSobolev_schwartz_multiplier n φ (v : 𝓢'(FourSpace, ℂ)) hv

theorem scalarReal_memSobolev_finset (n : ℕ) {ι : Type*} (s : Finset ι)
    (F : ι → Lp ℝ 2 (volume : Measure FourSpace))
    (hF : ∀ i ∈ s, MemSobolev (n : ℝ) 2 (scalarComplexL2 (F i) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (∑ i ∈ s, F i) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  change MemSobolev (n : ℝ) 2 (C (∑ i ∈ s, F i))
  rw [map_sum]
  induction s using Finset.cons_induction_on with
  | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero FourSpace ℂ (n : ℝ) 2
  | cons i s hi ih =>
      rw [Finset.sum_cons]
      exact (hF i (Finset.mem_cons_self i s)).add
        (ih (fun j hj => hF j (Finset.mem_cons_of_mem hj)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact component test coefficients on the region where a localization
cutoff is one. The cutoff introduces no term in the tested equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (S : Mat4) (χ ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
  (hon : ∀ z ∈ tsupport ψ, χ z = 1) (b : TwoFormFour)

include hon in
theorem twoFormMassTest_separated (z : FourSpace) :
    twoFormMassTest (g := g) c (fun w => ψ w • b) z =
      ψ z • twoFormMassCoefficient (g := g) c χ b z := by
  have he : ψ z * χ z = ψ z := by
    by_cases hz : z ∈ tsupport ψ
    · rw [hon z hz, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  simp only [twoFormMassTest, twoFormMassCoefficient, smul_smul]
  congr 1
  calc
    _ = (ψ z * χ z) * chartVolumeDensity g c z := by rw [he]; ring
    _ = _ := by ring

include hon hψ in
theorem twoFormEnergyTest_separated (i : Fin 4) (z : FourSpace) :
    twoFormEnergyTest (g := g) c S (fun w => ψ w • b) i z =
      (∑ j : Fin 4, partialDeriv ψ j z • twoFormFluxCoefficient (g := g) c χ b i j z) +
        ψ z • (χ z • twoFormWeightedConnection (g := g) c S b i z) := by
  have hval : ψ z * χ z = ψ z := by
    by_cases hz : z ∈ tsupport ψ
    · rw [hon z hz, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hder (j : Fin 4) : χ z * partialDeriv ψ j z = partialDeriv ψ j z := by
    by_cases hz : z ∈ tsupport ψ
    · rw [hon z hz, one_mul]
    · have hd : partialDeriv ψ j z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz ((tsupport_fderiv_apply_subset ℝ (coordinateVector j)) h))
      rw [hd, mul_zero]
  rw [twoFormEnergyTest_smul_const c S ψ hψ b i z]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    simp only [twoFormFluxCoefficient, smul_smul]
    congr 1
    calc
      _ = (chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j) *
          (χ z * partialDeriv ψ j z) := by rw [hder j]
      _ = _ := by ring
  · rw [smul_smul, hval]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The separated scalar tests agree in L2 with the actual mass and
covariant-energy tests of a compact two-form. -/

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

include hon in
theorem twoFormMassTestL2_separated :
    twoFormMassTestL2 (g := g) c (fun z => ψ z • b) (hψ.smul contDiff_const).contDiffOn
      hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs) =
      twoFormWeightedTestL2 (twoFormMassCoefficient (g := g) c χ b)
        (twoFormMassCoefficient_smooth c χ hχ hχs b).continuous hcχ.mul_right.smul_right
        ψ hψ.continuous := by
  apply Lp.ext
  filter_upwards [twoFormMassTestL2_coe (g := g) c (fun z => ψ z • b)
    (hψ.smul contDiff_const).contDiffOn hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs),
    twoFormWeightedTestL2_coe (twoFormMassCoefficient (g := g) c χ b)
      (twoFormMassCoefficient_smooth c χ hχ hχs b).continuous hcχ.mul_right.smul_right ψ hψ.continuous]
    with z hleft hright
  rw [hleft, hright]
  exact twoFormMassTest_separated c χ ψ hon b z

include hon in
theorem twoFormEnergyTestL2_separated (i : Fin 4) :
    twoFormEnergyTestL2 (g := g) c S hS (fun z => ψ z • b) (hψ.smul contDiff_const).contDiffOn
      hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs) i =
      (∑ j : Fin 4, twoFormWeightedTestL2 (twoFormFluxCoefficient (g := g) c χ b i j)
        (twoFormFluxCoefficient_smooth c χ hχ hχs b i j).continuous hcχ.mul_right.smul_right
        (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j).continuous) +
      twoFormWeightedTestL2 (fun z => χ z • twoFormWeightedConnection (g := g) c S b i z)
        (twoFormCutoffWeightedConnection_smooth c S hS b i χ hχ hχs).continuous hcχ.smul_right
        ψ hψ.continuous := by
  let P := fun j : Fin 4 => twoFormWeightedTestL2 (twoFormFluxCoefficient (g := g) c χ b i j)
    (twoFormFluxCoefficient_smooth c χ hχ hχs b i j).continuous hcχ.mul_right.smul_right
    (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j).continuous
  let Q := twoFormWeightedTestL2 (fun z => χ z • twoFormWeightedConnection (g := g) c S b i z)
    (twoFormCutoffWeightedConnection_smooth c S hS b i χ hχ hχs).continuous hcχ.smul_right
    ψ hψ.continuous
  have hP : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ j : Fin 4,
      P j z = partialDeriv ψ j z • twoFormFluxCoefficient (g := g) c χ b i j z :=
    Filter.eventually_all.mpr (fun j => twoFormWeightedTestL2_coe _ _ _ _ _)
  have hQ := twoFormWeightedTestL2_coe (fun z => χ z • twoFormWeightedConnection (g := g) c S b i z)
    (twoFormCutoffWeightedConnection_smooth c S hS b i χ hχ hχs).continuous hcχ.smul_right
    ψ hψ.continuous
  apply Lp.ext
  filter_upwards [twoFormEnergyTestL2_coe (g := g) c S hS (fun z => ψ z • b)
    (hψ.smul contDiff_const).contDiffOn hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs) i,
    Lp.coeFn_add (∑ j, P j) Q, Lp.coeFn_finsetSum Finset.univ P, hP, hQ]
      with z hleft hsum hpsum hp hq
  rw [hsum, Pi.add_apply, hpsum, Finset.sum_apply]
  simp_rw [hp]
  rw [hq, hleft]
  exact twoFormEnergyTest_separated c S χ ψ hψ hon b i z

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual smooth Hodge Laplacian in the normalization Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormL2Inner_sub (u v w : smoothTwoForms o) :
    smoothTwoFormL2Inner (u - v) w = smoothTwoFormL2Inner u w - smoothTwoFormL2Inner v w := by
  exact @inner_sub_left ℝ (SmoothL2TwoForm o) _ _ _ (u : SmoothL2TwoForm o)
    (v : SmoothL2TwoForm o) (w : SmoothL2TwoForm o)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem mass_pairing (A : FourSpace → TwoFormFour) (z : FourSpace) :
    inner ℝ (χ z • A z) (twoFormMassTest (g := g) c a z) =
      chartVolumeDensity g c z * inner ℝ (A z) (a z) := by
  by_cases hz : z ∈ tsupport a
  · rw [hon z hz, one_smul]
    exact real_inner_smul_right _ _ _
  · have hzero := image_eq_zero_of_notMem_tsupport hz
    simp only [twoFormMassTest, hzero, smul_zero, inner_zero_right, mul_zero]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem energy_pairing (A : FourSpace → TwoFormFour) (i : Fin 4) (z : FourSpace) :
    inner ℝ (χ z • A z) (twoFormEnergyTest (g := g) c S a i z) =
      chartVolumeDensity g c z * ∑ j : Fin 4, (metricInChart g c z)⁻¹ i j *
        inner ℝ (A z) (twoFormLocalNabla (g := g) c S a j z) := by
  by_cases hz : z ∈ tsupport a
  · rw [hon z hz, one_smul]
    simp only [twoFormEnergyTest, real_inner_smul_right, inner_sum]
  · have hzero (j : Fin 4) := twoFormLocalNabla_zero_off (g := g) c S a z hz j
    simp only [twoFormEnergyTest, hzero, smul_zero, Finset.sum_const_zero,
      inner_zero_right, mul_zero]

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

def twoFormScalarTestL2 (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  (hψ.continuous.memLp_of_hasCompactSupport hcψ).toLp ψ

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (χ ψ : FourSpace → ℝ)
  (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
  (hχs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψs : tsupport ψ ⊆ (chartAt FourSpace c).target)
  (hon : ∀ z ∈ tsupport ψ, χ z = 1) (b : TwoFormFour)

include hon in
theorem twoFormMassPair_scalarTest (V : Lp TwoFormFour 2 (volume : Measure FourSpace)) :
    inner ℝ V (twoFormMassTestL2 (g := g) c (fun z => ψ z • b) (hψ.smul contDiff_const).contDiffOn
      hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs)) =
      inner ℝ (twoFormMassPair (g := g) c χ hχ hcχ hχs b V) (twoFormScalarTestL2 ψ hψ hcψ) := by
  rw [twoFormMassTestL2_separated c χ ψ hχ hcχ hχs hψ hcψ hψs hon b]
  exact (twoFormCoefficientPair_test _ _ _ V ψ hψ.continuous hcψ).symm

include hon in
theorem twoFormEnergyPair_scalarTest (N : Lp TwoFormFour 2 (volume : Measure FourSpace)) (i : Fin 4) :
    inner ℝ N (twoFormEnergyTestL2 (g := g) c S hS (fun z => ψ z • b)
      (hψ.smul contDiff_const).contDiffOn hcψ.smul_right ((tsupport_smul_subset_left _ _).trans hψs) i) =
      (∑ j : Fin 4, inner ℝ (twoFormFluxPair (g := g) c χ hχ hcχ hχs b i j N)
        (twoFormScalarTestL2 (fun z => partialDeriv ψ j z) (twoFormCutoffPartial_smooth ψ hψ j)
          (hcψ.fderiv_apply ℝ (coordinateVector j)))) +
      inner ℝ (twoFormConnectionPair (g := g) c S hS χ hχ hcχ hχs b i N)
        (twoFormScalarTestL2 ψ hψ hcψ) := by
  rw [twoFormEnergyTestL2_separated c S hS χ ψ hχ hcχ hχs hψ hcψ hψs hon b i,
    inner_add_right, inner_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact (twoFormCoefficientPair_test _ _ _ N _ (twoFormCutoffPartial_smooth ψ hψ j).continuous
      (hcψ.fderiv_apply ℝ (coordinateVector j))).symm
  · exact (twoFormCoefficientPair_test _ _ _ N ψ hψ.continuous hcψ).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Moving actual H1 lower-order fluxes into L2 forcing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped BigOperators SchwartzMap ContDiff

noncomputable section

local notation "L2" => Lp ℝ 2 (volume : Measure FourSpace)

theorem scalarComplexL2_compact_inner_derivative (f D : L2) (i : Fin 4)
    (hD : scalarCoordinateDerivative i (scalarComplexL2 f : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 D : 𝓢'(FourSpace, ℂ)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    inner ℝ f (twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
      (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i))) =
      -inner ℝ D (twoFormScalarTestL2 ψ hψ hcψ) := by
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  have hleft : (∫ z, f z * twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
      (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i)) z) =
      ∫ z, f z * partialDeriv ψ i z := by
    apply integral_congr_ae
    filter_upwards [((twoFormCutoffPartial_smooth ψ hψ i).continuous.memLp_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ (coordinateVector i))).coeFn_toLp] with z hz
    exact congrArg (fun t => f z * t) hz
  have hright : (∫ z, D z * twoFormScalarTestL2 ψ hψ hcψ z) = ∫ z, D z * ψ z := by
    apply integral_congr_ae
    filter_upwards [(hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hz
    exact congrArg (fun t => D z * t) hz
  rw [hleft, hright]
  exact scalarComplexL2_compact_weak_derivative f D i hD ψ hψ hcψ

theorem scalar_divergence_corrected_flux (F C D : Fin 4 → L2) (R : L2)
    (hD : ∀ i, scalarCoordinateDerivative i (scalarComplexL2 (C i) : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (D i) : 𝓢'(FourSpace, ℂ)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hF : (∑ i : Fin 4, inner ℝ (F i)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
        (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i)))) =
      inner ℝ R (twoFormScalarTestL2 ψ hψ hcψ)) :
    (∑ i : Fin 4, inner ℝ (F i + C i)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z)
        (twoFormCutoffPartial_smooth ψ hψ i) (hcψ.fderiv_apply ℝ (coordinateVector i)))) =
      inner ℝ (R - ∑ i : Fin 4, D i) (twoFormScalarTestL2 ψ hψ hcψ) := by
  have hC (i : Fin 4) := scalarComplexL2_compact_inner_derivative (C i) (D i) i
    (hD i) ψ hψ hcψ
  simp_rw [inner_add_left]
  rw [Finset.sum_add_distrib, hF]
  simp_rw [hC]
  rw [Finset.sum_neg_distrib, inner_sub_left, sum_inner]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary derivative of each localized coefficient, tested against
actual smooth compact scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff SchwartzMap

noncomputable section

theorem scalarC1_compact_test (f : ↥(Euclidean.C1c (E := FourSpace)))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (i : Fin 4) :
    inner ℝ (ScalarEuclideanSobolev.valueL2 f)
      (twoFormScalarTestL2 (fun z => partialDeriv ψ i z) (twoFormCutoffPartial_smooth ψ hψ i)
        (hcψ.fderiv_apply ℝ (coordinateVector i))) =
      -inner ℝ (ScalarEuclideanSobolev.partialL2 f i) (twoFormScalarTestL2 ψ hψ hcψ) := by
  have h := scalarC1_weak_derivative f (hcψ.toSchwartzMap hψ) i
  change (∫ z, f.val z * partialDeriv ψ i z) = -(∫ z, partialDeriv f.val i z * ψ z) at h
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  have hl : (∫ z, ScalarEuclideanSobolev.valueL2 f z *
      twoFormScalarTestL2 (fun z => partialDeriv ψ i z) (twoFormCutoffPartial_smooth ψ hψ i)
        (hcψ.fderiv_apply ℝ (coordinateVector i)) z) = ∫ z, f.val z * partialDeriv ψ i z := by
    apply integral_congr_ae
    filter_upwards [ScalarEuclideanSobolev.valueL2_coe f,
      (((twoFormCutoffPartial_smooth ψ hψ i).continuous).memLp_of_hasCompactSupport
        (hcψ.fderiv_apply ℝ (coordinateVector i))).coeFn_toLp] with z hf hd
    exact congrArg₂ (· * ·) hf hd
  have hr : (∫ z, ScalarEuclideanSobolev.partialL2 f i z * twoFormScalarTestL2 ψ hψ hcψ z) =
      ∫ z, partialDeriv f.val i z * ψ z := by
    apply integral_congr_ae
    filter_upwards [ScalarEuclideanSobolev.partialL2_coe f i,
      (hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp] with z hf hq
    exact congrArg₂ (· * ·) hf hq
  rw [hl, hr]
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The principal flux paired with a scalar test is the actual
metric-weighted pairing of the ordinary weak component derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormPrincipalCoefficient (c : M) (χ : FourSpace → ℝ) (i j : Fin 4) (z : FourSpace) : ℝ :=
  χ z * (chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j)

variable (c : M) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ (chartAt FourSpace c).target)

include hχ hs in
theorem twoFormPrincipalCoefficient_smooth (i j : Fin 4) :
    ContDiff ℝ ∞ (twoFormPrincipalCoefficient (g := g) c χ i j) :=
  scalarCutoff_contDiff χ _ hχ (fun z hz =>
    (chartVolumeDensity_contDiffAt g c z (hs hz)).mul
      (scalarPrincipalCoefficients_smooth g c z (hs hz) i j))

theorem twoFormFluxPair_basis_test (F : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (i j : Fin 4) (r : Fin 6) :
    inner ℝ (twoFormFluxPair (g := g) c χ hχ hc hs (EuclideanSpace.basisFun (Fin 6) ℝ r) i j F)
      (twoFormScalarTestL2 ψ hψ hcψ) =
    inner ℝ (twoFormVectorComponentL2 r F)
      (twoFormScalarTestL2 (fun z => twoFormPrincipalCoefficient (g := g) c χ i j z * ψ z)
        ((twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul hψ) hc.mul_right.mul_right) := by
  rw [L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply', conj_trivial]
  apply integral_congr_ae
  filter_upwards [twoFormCoefficientPair_coe
      (twoFormFluxCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r) i j)
      (twoFormFluxCoefficient_smooth c χ hχ hs _ i j).continuous hc.mul_right.smul_right F,
    twoFormVectorComponentL2_coe r F,
    (hψ.continuous.memLp_of_hasCompactSupport hcψ).coeFn_toLp,
    (((twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul hψ).continuous.memLp_of_hasCompactSupport
      hc.mul_right.mul_right).coeFn_toLp] with z hp hv hq ht
  have hp' : twoFormFluxPair (g := g) c χ hχ hc hs (EuclideanSpace.basisFun (Fin 6) ℝ r)
      i j F z = inner ℝ (F z)
        (twoFormFluxCoefficient (g := g) c χ (EuclideanSpace.basisFun (Fin 6) ℝ r) i j z) := hp
  have hq' : twoFormScalarTestL2 ψ hψ hcψ z = ψ z := hq
  have ht' : twoFormScalarTestL2
      (fun z => twoFormPrincipalCoefficient (g := g) c χ i j z * ψ z)
      ((twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul hψ)
      hc.mul_right.mul_right z = twoFormPrincipalCoefficient (g := g) c χ i j z * ψ z := ht
  rw [hp', hv, hq', ht']
  simp only [twoFormFluxCoefficient, inner_smul_right, EuclideanSpace.inner_basisFun_real,
    twoFormPrincipalCoefficient]
  ring

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

def twoFormPrincipalTest (i j : Fin 4) (z : FourSpace) : ℝ :=
  twoFormPrincipalCoefficient (g := g) c χ i j z * partialDeriv ψ j z

include hχ hs hψ in
theorem twoFormPrincipalTest_smooth (i j : Fin 4) :
    ContDiff ℝ ∞ (twoFormPrincipalTest (g := g) c χ ψ i j) :=
  (twoFormPrincipalCoefficient_smooth c χ hχ hs i j).mul (twoFormCutoffPartial_smooth ψ hψ j)

include hcψ in
theorem twoFormPrincipalTest_compact (i j : Fin 4) :
    HasCompactSupport (twoFormPrincipalTest (g := g) c χ ψ i j) :=
  (hcψ.fderiv_apply ℝ (coordinateVector j)).mul_left

def twoFormPrincipalDerivativeTestL2 (i j : Fin 4) : Lp ℝ 2 (volume : Measure FourSpace) :=
  twoFormScalarTestL2 (fun z => partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z)
    (twoFormCutoffPartial_smooth _ (twoFormPrincipalTest_smooth c χ ψ hχ hs hψ i j) i)
    ((twoFormPrincipalTest_compact c χ ψ hcψ i j).fderiv_apply ℝ (coordinateVector i))

def twoFormPrincipalDivergenceTestL2 : Lp ℝ 2 (volume : Measure FourSpace) :=
  ∑ i : Fin 4, ∑ j : Fin 4, twoFormPrincipalDerivativeTestL2 (g := g) c χ ψ hχ hs hψ hcψ i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact principal test is precisely the density-weighted scalar
chart Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable (c : M) (χ ψ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
  (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
  (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψt : tsupport ψ ⊆ (chartAt FourSpace c).target)
  (hon : ∀ z ∈ tsupport ψ, χ z = 1)

theorem twoFormPrincipalTest_support (i j : Fin 4) :
    tsupport (twoFormPrincipalTest (g := g) c χ ψ i j) ⊆ tsupport ψ :=
  tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ (coordinateVector j))

include hon in
theorem twoFormPrincipalTest_remove_cutoff (i j : Fin 4) :
    twoFormPrincipalTest (g := g) c χ ψ i j = fun z =>
      chartVolumeDensity g c z * (metricInChart g c z)⁻¹ i j * partialDeriv ψ j z := by
  funext z
  by_cases hz : z ∈ tsupport ψ
  · simp only [twoFormPrincipalTest, twoFormPrincipalCoefficient, hon z hz, one_mul]
  · have hd : partialDeriv ψ j z = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hz ((tsupport_fderiv_apply_subset ℝ (coordinateVector j)) h))
    simp only [twoFormPrincipalTest, hd, mul_zero]

include hon hψt hχ hs hψ in
theorem twoFormPrincipalDivergence_value (z : FourSpace) :
    (∑ i : Fin 4, ∑ j : Fin 4, partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z) =
      chartVolumeDensity g c z * scalarChartOperator g c ψ z := by
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · have hder (i : Fin 4) :
        partialDeriv (fun w => ∑ j : Fin 4, twoFormPrincipalTest (g := g) c χ ψ i j w) i z =
          ∑ j : Fin 4, partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z := by
      change (fderiv ℝ _ z) (coordinateVector i) = _
      rw [fderiv_fun_sum (fun j _ =>
        (twoFormPrincipalTest_smooth c χ ψ hχ hs hψ i j).differentiable (by simp) z)]
      simp only [_root_.sum_apply, partialDeriv]
    calc
      _ = ∑ i : Fin 4, partialDeriv (fun w => ∑ j : Fin 4,
          chartVolumeDensity g c w * (metricInChart g c w)⁻¹ i j * partialDeriv ψ j w) i z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hder i]
        simp_rw [twoFormPrincipalTest_remove_cutoff c χ ψ hon]
      _ = _ := scalarChartOperator_divergence g c ψ z hz hψ.contDiffAt
  · have hp : z ∉ tsupport ψ := fun h => hz (hψt h)
    have hzero (i j : Fin 4) : partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp
        (twoFormPrincipalTest_support c χ ψ i j
          ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)) h)))
    simp only [hzero, Finset.sum_const_zero,
      scalarChartOperator_eq_zero_off_tsupport g c ψ hp, mul_zero]

include hon hψt in
theorem twoFormPrincipalDivergenceTestL2_coe :
    twoFormPrincipalDivergenceTestL2 (g := g) c χ ψ hχ hs hψ hcψ =ᵐ[volume]
      fun z => chartVolumeDensity g c z * scalarChartOperator g c ψ z := by
  let F := fun i j : Fin 4 => twoFormPrincipalDerivativeTestL2 (g := g) c χ ψ hχ hs hψ hcψ i j
  have ht : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i j : Fin 4,
      F i j z = partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (((twoFormCutoffPartial_smooth _
      (twoFormPrincipalTest_smooth c χ ψ hχ hs hψ i j) i).continuous).memLp_of_hasCompactSupport
        ((twoFormPrincipalTest_compact c χ ψ hcψ i j).fderiv_apply ℝ (coordinateVector i))).coeFn_toLp
  have hi := Filter.eventually_all.mpr (fun i : Fin 4 => Lp.coeFn_finsetSum Finset.univ (F i))
  change ((∑ i : Fin 4, ∑ j : Fin 4, F i j : Lp ℝ 2 (volume : Measure FourSpace)) : FourSpace → ℝ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 => ∑ j : Fin 4, F i j), hi, ht]
    with z hout hin hz
  rw [hout]
  change (∑ i : Fin 4, (∑ j : Fin 4, F i j) z) = _
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
        partialDeriv (twoFormPrincipalTest (g := g) c χ ψ i j) i z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hin i]
      change (∑ j : Fin 4, F i j z) = _
      exact Finset.sum_congr rfl (fun j _ => hz i j)
    _ = _ := twoFormPrincipalDivergence_value c χ ψ hχ hs hψ hψt hon z

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth coefficient pairing at the integer orders needed by the
harmonic two-form bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped BigOperators SchwartzMap ENNReal ContDiff

noncomputable section

variable (b : FourSpace → TwoFormFour) (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)

theorem twoFormCoefficientPair_memSobolev_integer (n : ℕ) (f : Lp TwoFormFour 2 (volume : Measure FourSpace))
    (hf : ∀ r : Fin 6, MemSobolev (n : ℝ) 2
      (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormCoefficientPairL2 b hb.continuous hc f) :
      𝓢'(FourSpace, ℂ)) := by
  rw [twoFormCoefficientPair_distribution]
  have hs (s : Finset (Fin 6)) : MemSobolev (n : ℝ) 2 (∑ r ∈ s,
      smulLeftCLM ℂ (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ))) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using memSobolev_fun_zero FourSpace ℂ (n : ℝ) 2
    | @insert r s hr ih =>
      rw [Finset.sum_insert hr]
      have hfr : MemSobolev (n : ℝ) 2
          (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) := by
        exact hf r
      have hm := scalar_memSobolev_schwartz_multiplier n (twoFormCoefficientSchwartz b hb hc r)
        (scalarComplexL2 (twoFormVectorComponentL2 r f) : 𝓢'(FourSpace, ℂ)) hfr
      have hm' := hm.add (by exact ih)
      exact hm'
  exact hs Finset.univ


end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Pointwise Hodge-Poisson solvability and the kernel of the actual
smooth Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_eq_of_pairings (u v : smoothTwoForms o)
    (h : ∀ w : smoothTwoForms o, smoothTwoFormL2Inner u w = smoothTwoFormL2Inner v w) :
    u = v := by
  have he : (u : SmoothL2TwoForm o) = (v : SmoothL2TwoForm o) :=
    @ext_inner_right ℝ (SmoothL2TwoForm o) _ _ _ (u : SmoothL2TwoForm o)
      (v : SmoothL2TwoForm o) (fun w => h (w : smoothTwoForms o))
  exact he

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


