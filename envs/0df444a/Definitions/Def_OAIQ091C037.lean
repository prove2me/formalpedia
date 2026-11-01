-- Prove2me | Definitions.Def_OAIQ091C037
-- name    : OAIQ091C037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:40:55.393804+00:00
-- url     : https://prove2.me/theorems/4dd2d7ce-8a9b-4e1c-94c2-9692be947631
-- title:
--   Definitions bundle OAIQ091C037 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 12 definitions and 116 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatNormalFrameData.frame`, `OAI.PositiveEinsteinFour.Geometry.KineticLocalFlow.restrictTime`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneCovariantDerivative`, `OAI.PositiveEinsteinFour.Geometry.frameCotangentState`, `OAI.PositiveEinsteinFour.Geometry.frameGeodesic`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneFormValue`, `OAI.PositiveEinsteinFour.Geometry.heatPullbackConnection`, `OAI.PositiveEinsteinFour.Geometry.heatPullbackMetric`, `OAI.PositiveEinsteinFour.Geometry.kineticMomentumScale`, `OAI.PositiveEinsteinFour.Geometry.oneFormSecondTrace`, `OAI.PositiveEinsteinFour.Geometry.radialFrameCotangentState`, `OAI.PositiveEinsteinFour.Geometry.radialSlab`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C038` and `OAIQ091C055`; the statement `OAI_PositiveEinsteinFour_QuaternionFrame_projection_bound_of_weight_square`; the proof of `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C017

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The cotangent lift of the actual horizontal frame equation satisfies
Hamilton's equations for the metric kinetic energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem cotangentHamiltonianField_contDiffAt
    (H : CotangentCoordinates → ℝ) (z : CotangentCoordinates)
    (hH : ContDiffAt ℝ ∞ H z) :
    ContDiffAt ℝ ∞ (cotangentHamiltonianField H) z := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ H) z := hH.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply ContDiffAt.prodMk
  · apply (contDiffAt_piLp 2).mpr
    intro r
    exact hd.clm_apply contDiffAt_const
  · apply (contDiffAt_piLp 2).mpr
    intro r
    exact (hd.clm_apply contDiffAt_const).neg

theorem kineticHamiltonianField_contDiffAt (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates) (hz : z.1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (cotangentHamiltonianField (kineticHamiltonian g c)) z :=
  cotangentHamiltonianField_contDiffAt _ _ (kineticHamiltonian_contDiffAt g c z hz)

theorem kineticHamiltonian_directional (g : SmoothMetric M) (c : M)
    (x p dx dp : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    fderiv ℝ (kineticHamiltonian g c) (x, p) (dx, dp) =
      (∑ i, ∑ j,
        (dp i * ((metricInChart g c x)⁻¹ i j * p j) +
          p i * (fderiv ℝ (fun z => (metricInChart g c z)⁻¹ i j) x dx * p j +
            (metricInChart g c x)⁻¹ i j * dp j))) / 2 := by
  let γ : ℝ → CotangentCoordinates := fun s => (x + s • dx, p + s • dp)
  have hx' : HasDerivAt (fun s : ℝ => x + s • dx) dx 0 := by
    simpa only [Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const dx)
  have hp' : HasDerivAt (fun s : ℝ => p + s • dp) dp 0 := by
    simpa only [Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) p).add ((hasDerivAt_id (0 : ℝ)).smul_const dp)
  have hγ : HasDerivAt γ (dx, dp) 0 := hx'.prodMk hp'
  have hγ0 : γ 0 = (x, p) := by simp [γ]
  have hdet := (metricInChart_posDef g c x hx).det_pos.ne'
  have hP (i : Fin 4) : HasDerivAt (fun s : ℝ => (p + s • dp) i) (dp i) 0 := by
    exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 hp'
  have hG (i j : Fin 4) :
      HasDerivAt (fun s : ℝ => (metricInChart g c (x + s • dx))⁻¹ i j)
        (fderiv ℝ (fun z => (metricInChart g c z)⁻¹ i j) x dx) 0 := by
    have hd : HasFDerivAt (fun z => (metricInChart g c z)⁻¹ i j)
        (fderiv ℝ (fun z => (metricInChart g c z)⁻¹ i j) x) (x + (0 : ℝ) • dx) := by
      simpa using ((metricInChart_inv_contDiffAt g c x hx hdet i j).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
    have h := hd.comp_hasDerivAt 0 hx'
    simpa only [Function.comp_def, zero_smul, add_zero] using h
  have hsum := (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hP i).mul ((hG i j).mul (hP j))))).div_const 2
  have hc : HasDerivAt (fun s => kineticHamiltonian g c (γ s))
      ((∑ i, ∑ j,
        (dp i * ((metricInChart g c x)⁻¹ i j * p j) +
          p i * (fderiv ℝ (fun z => (metricInChart g c z)⁻¹ i j) x dx * p j +
            (metricInChart g c x)⁻¹ i j * dp j))) / 2) 0 := by
    refine (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
    · beta_reduce
      simp only [kineticHamiltonian, γ, dotProduct, Matrix.mulVec, Finset.mul_sum,
        Pi.mul_apply]
    · simp only [Pi.mul_apply, zero_smul, add_zero]
  have hD : HasFDerivAt (kineticHamiltonian g c)
      (fderiv ℝ (kineticHamiltonian g c) (x, p)) (γ 0) := by
    simpa only [hγ0] using ((kineticHamiltonian_contDiffAt g c (x, p) hx).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hd := hD.comp_hasDerivAt 0 hγ
  exact hd.unique hc

theorem inverseMetric_symm (g : SmoothMetric M) (c : M) (x : FourSpace) :
    ((metricInChart g c x)⁻¹).IsSymm := by
  apply Matrix.IsSymm.inv
  ext i j
  exact g.symm _ _ _

theorem kineticHamiltonian_momentum_partial (g : SmoothMetric M) (c : M)
    (x p : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (r : Fin 4) :
    fderiv ℝ (kineticHamiltonian g c) (x, p) (momentumDirection r) =
      ((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp p) r := by
  rw [momentumDirection, kineticHamiltonian_directional g c x p 0 (coordinateVector r) hx]
  simp only [map_zero, zero_mul, zero_add, coordinateVector,
    PiLp.single_apply]
  have hs := inverseMetric_symm g c x
  have hrow : (∑ i, p i * (metricInChart g c x)⁻¹ i r) =
      ∑ i, (metricInChart g c x)⁻¹ r i * p i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hs.apply r i, mul_comm]
  simp only [Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    one_mul, mul_one, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [hrow]
  change ((∑ i, (metricInChart g c x)⁻¹ r i * p i) +
    (∑ i, (metricInChart g c x)⁻¹ r i * p i)) / 2 = _
  simp only [Matrix.mulVec, dotProduct]
  ring

theorem kineticHamiltonian_position_partial (g : SmoothMetric M) (c : M)
    (x p : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (r : Fin 4) :
    fderiv ℝ (kineticHamiltonian g c) (x, p) (positionDirection r) =
      (∑ i, ∑ j, p i * matrixPartial
        (fun z => (metricInChart g c z)⁻¹) r x i j * p j) / 2 := by
  rw [positionDirection, kineticHamiltonian_directional g c x p (coordinateVector r) 0 hx]
  simp only [PiLp.zero_apply, zero_mul, mul_zero, zero_add, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change p i * (matrixPartial (fun z => (metricInChart g c z)⁻¹) r x i j * p j) = _
  ring

theorem kineticHamiltonian_force (g : SmoothMetric M) (c : M)
    (x p : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) (r : Fin 4) :
    -fderiv ℝ (kineticHamiltonian g c) (x, p) (positionDirection r) =
      WithLp.ofLp p ⬝ᵥ (connectionMatrix g c r x *ᵥ
        ((metricInChart g c x)⁻¹ *ᵥ WithLp.ofLp p)) := by
  rw [kineticHamiltonian_position_partial g c x p hx r]
  have hquad : (∑ i, ∑ j, p i *
      matrixPartial (fun z => (metricInChart g c z)⁻¹) r x i j * p j) =
      WithLp.ofLp p ⬝ᵥ
        (matrixPartial (fun z => (metricInChart g c z)⁻¹) r x *ᵥ WithLp.ofLp p) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [hquad, matrixPartial_inverseMetric g c x hx r]
  exact inverse_metric_force _ _ (inverseMetric_symm g c x) _

theorem hasDerivAt_frameCotangentMomentum (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (t : ℝ) (k : Fin 4)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (fun r => E t r k)) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j)
      (-(parallelFrameConnection g c k (x t, E t) * E t) i j) t) :
    HasDerivAt (fun s => frameCotangentMomentum g c (x s) (E s) k)
      (WithLp.toLp 2 ((parallelFrameConnection g c k (x t, E t))ᵀ *ᵥ
        WithLp.ofLp (frameCotangentMomentum g c (x t) (E t) k))) t := by
  let G (s : ℝ) : Mat4 := metricInChart g c (x s)
  let C : Mat4 := parallelFrameConnection g c k (x t, E t)
  let D : Mat4 := Cᵀ * G t + G t * C
  let P : Mat4 := -(C * E t)
  have hG (i j : Fin 4) : HasDerivAt (fun s => G s i j) (D i j) t := by
    have hd := hasDerivAt_coordinate_comp hx
      ((metricInChart_contDiffAt g c (x t) hz i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    have hr := congrFun (congrFun (parallelFrame_metric_rate g c (x t) hz
      (fun r => E t r k)) i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, matrixPartial] at hr
    change (∑ r, E t r k * partialDeriv (fun z => metricInChart g c z i j) r (x t)) =
      D i j at hr
    rwa [hr] at hd
  have hP (i j : Fin 4) : HasDerivAt (fun s => E s i j) (P i j) t := hE i j
  have hmatrix (i : Fin 4) : HasDerivAt (fun s => (G s * E s) i k)
      ((D * E t + G t * P) i k) t := by
    have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
      (hG i j).mul (hP j k))
    simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib,
      Pi.mul_apply] using h
  have hr : D * E t + G t * P = Cᵀ * (G t * E t) := by
    dsimp only [D, P]
    rw [parallel_momentum_algebra, Matrix.mul_assoc]
  have hc : HasDerivAt (fun s i => (G s * E s) i k)
      (fun i => (Cᵀ * (G t * E t)) i k) t := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [hr] using hmatrix i
  exact (PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t hc

theorem inverseMetric_frameMomentum (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (E : Mat4) (k : Fin 4) :
    (metricInChart g c x)⁻¹ *ᵥ
      WithLp.ofLp (frameCotangentMomentum g c x E k) = fun i => E i k := by
  change (metricInChart g c x)⁻¹ *ᵥ
    (metricInChart g c x *ᵥ fun i => E i k) = _
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c x hx).det_pos.ne'),
    Matrix.one_mulVec]

theorem frameMomentum_force (g : SmoothMetric M) (c : M)
    (x : FourSpace) (E : Mat4) (k : Fin 4) (p : Fin 4 → ℝ) (i : Fin 4) :
    ((parallelFrameConnection g c k (x, E))ᵀ *ᵥ p) i =
      p ⬝ᵥ (connectionMatrix g c i x *ᵥ fun r => E r k) := by
  simp only [parallelFrameConnection, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum, connectionMatrix]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  rw [christoffel_comm g c x j r i]
  ring

/-- The metric-lowered frame direction obeys the actual kinetic
Hamiltonian field, with no energy-shell or normalization assumption. -/
theorem cotangentHamiltonianField_frame (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (E : Mat4) (k : Fin 4) :
    cotangentHamiltonianField (kineticHamiltonian g c)
      (x, frameCotangentMomentum g c x E k) =
      (WithLp.toLp 2 (fun r => E r k),
        WithLp.toLp 2 ((parallelFrameConnection g c k (x, E))ᵀ *ᵥ
          WithLp.ofLp (frameCotangentMomentum g c x E k))) := by
  apply Prod.ext
  · ext r
    change fderiv ℝ (kineticHamiltonian g c)
      (x, frameCotangentMomentum g c x E k) (momentumDirection r) = E r k
    rw [kineticHamiltonian_momentum_partial g c x _ hx r,
      inverseMetric_frameMomentum g c x hx E k]
  · ext r
    change -fderiv ℝ (kineticHamiltonian g c)
      (x, frameCotangentMomentum g c x E k) (positionDirection r) = _
    rw [kineticHamiltonian_force g c x _ hx r,
      inverseMetric_frameMomentum g c x hx E k]
    exact (frameMomentum_force g c x E k _ r).symm

/-- A primitive parallel-frame curve has a cotangent lift satisfying
Hamilton's equations for the actual metric Hamiltonian. -/
theorem hasDerivAt_parallelFrame_cotangentLift (g : SmoothMetric M) (c : M)
    (x : ℝ → FourSpace) (E : ℝ → Mat4) (t : ℝ) (k : Fin 4)
    (hz : x t ∈ (chartAt FourSpace c).target)
    (hx : HasDerivAt x (WithLp.toLp 2 (fun r => E t r k)) t)
    (hE : ∀ i j, HasDerivAt (fun s => E s i j)
      (-(parallelFrameConnection g c k (x t, E t) * E t) i j) t) :
    HasDerivAt (fun s => (x s, frameCotangentMomentum g c (x s) (E s) k))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (x t, frameCotangentMomentum g c (x t) (E t) k)) t := by
  rw [cotangentHamiltonianField_frame g c (x t) hz (E t) k]
  exact hx.prodMk (hasDerivAt_frameCotangentMomentum g c x E t k hz hx hE)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual kinetic Hamiltonian has a local flow whose initial-value
Jacobian is one. Both the variational equation and local injectivity are
proved from the vector field, before applying change of variables. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_kineticLocalFlow (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target) :
    Nonempty (KineticLocalFlow g c p) := by
  let f := cotangentHamiltonianField (kineticHamiltonian g c)
  have hf : ContDiffAt ℝ 2 f p :=
    (kineticHamiltonianField_contDiffAt g c p hp).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨r₀, hr₀, ε₀, hε₀, α, V, hαc, hVc, hs⟩ :=
    FlowCalculus.exists_jointly_differentiable_local_flow f p hf
  have hp0 : α (p, 0) = p := (hs p (Metric.mem_ball_self hr₀)).1
  have hz : (0 : ℝ) ∈ Ioo (-ε₀) ε₀ := ⟨by linarith, hε₀⟩
  have hαat : ContinuousAt α (p, 0) :=
    hαc.continuousAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨Metric.mem_ball_self hr₀, hz⟩)
  have hnear : ∀ᶠ z in 𝓝 (p, (0 : ℝ)), (α z).1 ∈ (chartAt FourSpace c).target :=
    hαat.fst.eventually ((chartAt FourSpace c).open_target.mem_nhds
      (by simpa only [hp0] using hp))
  obtain ⟨δ, hδ, hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let r := min r₀ (δ / 2)
  let ε := min ε₀ (δ / 2)
  have hr : 0 < r := lt_min hr₀ (half_pos hδ)
  have hε : 0 < ε := lt_min hε₀ (half_pos hδ)
  have hq {q : CotangentCoordinates} (hq : q ∈ Metric.ball p r) :
      q ∈ Metric.ball p r₀ := Metric.ball_subset_ball (min_le_left _ _) hq
  have ht {t : ℝ} (ht : t ∈ Ioo (-ε) ε) : t ∈ Ioo (-ε₀) ε₀ := by
    have he : ε ≤ ε₀ := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hsub : Metric.ball p r ×ˢ Ioo (-ε) ε ⊆
      Metric.ball p r₀ ×ˢ Ioo (-ε₀) ε₀ := fun z hz => ⟨hq hz.1, ht hz.2⟩
  refine ⟨{
    radius := r
    radius_pos := hr
    time := ε
    time_pos := hε
    map := α
    variation := V
    continuous_map := hαc.mono hsub
    continuous_variation := hVc.mono hsub
    initial := fun q h => (hs q (hq h)).1
    initial_variation := fun q h => (hs q (hq h)).2.1
    inside := ?_
    time_derivative := fun q h t h' => ((hs q (hq h)).2.2 t (ht h')).1
    variation_derivative := fun q h t h' => ((hs q (hq h)).2.2 t (ht h')).2.1
    joint_derivative := fun q h t h' => ((hs q (hq h)).2.2 t (ht h')).2.2 }⟩
  intro q h t h'
  apply hδnear
  rw [Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
  exact ⟨((Metric.mem_ball.mp h).trans_le (min_le_right _ _)).trans (half_lt_self hδ),
    ((abs_lt.mpr h').trans_le (min_le_right _ _)).trans (half_lt_self hδ)⟩

namespace KineticLocalFlow

variable {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}

/-- Uniqueness against any other actual kinetic trajectory on the common
interval, including cotangent lifts of the global frame flow. -/
theorem eq_on (F : KineticLocalFlow g c p)
    (q : CotangentCoordinates) (hq : q ∈ Metric.ball p F.radius)
    (γ : ℝ → CotangentCoordinates) (hγ0 : γ 0 = q)
    (hγ : ∀ t ∈ Ioo (-F.time) F.time,
      HasDerivAt γ (cotangentHamiltonianField (kineticHamiltonian g c) (γ t)) t) :
    EqOn (fun s => F.map (q, s)) γ (Ioo (-F.time) F.time) := by
  let f := cotangentHamiltonianField (kineticHamiltonian g c)
  let I := Ioo (-F.time) F.time
  let : PreconnectedSpace I :=
    isPreconnected_iff_preconnectedSpace.mp (convex_Ioo _ _).isPreconnected
  let S : Set I := {s | F.map (q, s.val) = γ s.val}
  have hcq : Continuous (fun s : I => F.map (q, s.val)) :=
    (HasDerivAt.continuousOn (fun s hs => F.time_derivative q hq s hs)).domRestrict
  have hcγ : Continuous (fun s : I => γ s.val) :=
    (HasDerivAt.continuousOn hγ).domRestrict
  have hclosed : IsClosed S := isClosed_eq hcq hcγ
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    change F.map (q, s.val) = γ s.val at hs
    have hf : ContDiffAt ℝ 1 f (F.map (q, s.val)) :=
      (kineticHamiltonianField_contDiffAt g c _ (F.inside q hq s.val s.property)).of_le
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    obtain ⟨K, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
    have hn : ∀ᶠ t in 𝓝 s.val, t ∈ I := isOpen_Ioo.mem_nhds s.property
    have hdq := hn.mono fun t ht => F.time_derivative q hq t ht
    have hdγ := hn.mono fun t ht => hγ t ht
    have hqU := hdq.self_of_nhds.continuousAt.preimage_mem_nhds hU
    have hγU := hdγ.self_of_nhds.continuousAt.preimage_mem_nhds
      (by simpa only [← hs] using hU)
    have hu := ODE_solution_unique_of_eventually
      (Filter.Eventually.of_forall fun _ => hLip) (hdq.and hqU) (hdγ.and hγU) hs
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds hu
  have hz : (0 : ℝ) ∈ I := ⟨by linarith [F.time_pos], F.time_pos⟩
  have hfull : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨0, hz⟩, (F.initial q hq).trans hγ0.symm⟩
  intro s hs
  have h : (⟨s, hs⟩ : I) ∈ S := by rw [hfull]; trivial
  exact h

end KineticLocalFlow
end
end PositiveEinsteinFour.Geometry
end


section

/-! Homogeneity of the actual kinetic Hamiltonian. Radial scaling of
momentum corresponds to the same scaling of time along a trajectory. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def kineticMomentumScale (r : ℝ) (z : CotangentCoordinates) : CotangentCoordinates :=
  (z.1, r • z.2)

theorem kineticHamiltonianField_scale (g : SmoothMetric M) (c : M)
    (r : ℝ) (z : CotangentCoordinates)
    (hz : z.1 ∈ (chartAt FourSpace c).target) :
    cotangentHamiltonianField (kineticHamiltonian g c) (kineticMomentumScale r z) =
      (r • (cotangentHamiltonianField (kineticHamiltonian g c) z).1,
        r ^ 2 • (cotangentHamiltonianField (kineticHamiltonian g c) z).2) := by
  apply Prod.ext
  · ext i
    change fderiv ℝ (kineticHamiltonian g c) (z.1, r • z.2) (momentumDirection i) =
      r * fderiv ℝ (kineticHamiltonian g c) z (momentumDirection i)
    rw [kineticHamiltonian_momentum_partial g c z.1 (r • z.2) hz i,
      kineticHamiltonian_momentum_partial g c z.1 z.2 hz i]
    change ((metricInChart g c z.1)⁻¹ *ᵥ (r • WithLp.ofLp z.2)) i = _
    rw [Matrix.mulVec_smul]
    rfl
  · ext i
    change -fderiv ℝ (kineticHamiltonian g c) (z.1, r • z.2) (positionDirection i) =
      r ^ 2 * -fderiv ℝ (kineticHamiltonian g c) z (positionDirection i)
    rw [kineticHamiltonian_force g c z.1 (r • z.2) hz i,
      kineticHamiltonian_force g c z.1 z.2 hz i]
    change (r • WithLp.ofLp z.2) ⬝ᵥ (connectionMatrix g c i z.1 *ᵥ
      ((metricInChart g c z.1)⁻¹ *ᵥ (r • WithLp.ofLp z.2))) = _
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [smul_eq_mul]
    ring

/-- The radial extension of a unit-energy trajectory is an actual kinetic
trajectory, with the expected rescaling of its time parameter. -/
theorem hasDerivAt_kineticMomentumScale (g : SmoothMetric M) (c : M)
    (γ : ℝ → CotangentCoordinates) (r t : ℝ)
    (hz : (γ (r * t)).1 ∈ (chartAt FourSpace c).target)
    (hγ : HasDerivAt γ
      (cotangentHamiltonianField (kineticHamiltonian g c) (γ (r * t))) (r * t)) :
    HasDerivAt (fun s => kineticMomentumScale r (γ (r * s)))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (kineticMomentumScale r (γ (r * t)))) t := by
  have h : HasDerivAt (fun s => γ (r * s))
      (r • cotangentHamiltonianField (kineticHamiltonian g c) (γ (r * t))) t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hγ.scomp t ((hasDerivAt_id t).const_mul r)
  have hx : HasDerivAt (fun s => (γ (r * s)).1)
      (r • (cotangentHamiltonianField (kineticHamiltonian g c) (γ (r * t))).1) t :=
    (ContinuousLinearMap.fst ℝ FourSpace FourSpace).hasFDerivAt.comp_hasDerivAt t h
  have hp0 : HasDerivAt (fun s => (γ (r * s)).2)
      (r • (cotangentHamiltonianField (kineticHamiltonian g c) (γ (r * t))).2) t :=
    (ContinuousLinearMap.snd ℝ FourSpace FourSpace).hasFDerivAt.comp_hasDerivAt t h
  have hp : HasDerivAt (fun s => r • (γ (r * s)).2)
      (r ^ 2 • (cotangentHamiltonianField (kineticHamiltonian g c) (γ (r * t))).2) t := by
    simpa only [Pi.smul_apply, smul_smul, pow_two] using! hp0.const_smul r
  rw [kineticHamiltonianField_scale g c r (γ (r * t)) hz]
  exact hx.prodMk hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kinetic flow at zero momentum. Its stationary solution and
linearization provide the local inverse-function input for exponential
coordinates at the zero tangent vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem kineticHamiltonianField_coordinates (g : SmoothMetric M) (c : M)
    (z : CotangentCoordinates) (hz : z.1 ∈ (chartAt FourSpace c).target) :
    cotangentHamiltonianField (kineticHamiltonian g c) z =
      (WithLp.toLp 2 ((metricInChart g c z.1)⁻¹ *ᵥ WithLp.ofLp z.2),
        WithLp.toLp 2 (fun r => WithLp.ofLp z.2 ⬝ᵥ
          (connectionMatrix g c r z.1 *ᵥ
            ((metricInChart g c z.1)⁻¹ *ᵥ WithLp.ofLp z.2)))) := by
  apply Prod.ext
  · ext r
    exact kineticHamiltonian_momentum_partial g c z.1 z.2 hz r
  · ext r
    exact kineticHamiltonian_force g c z.1 z.2 hz r

theorem kineticHamiltonianField_zero_momentum (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target) :
    cotangentHamiltonianField (kineticHamiltonian g c) (x, 0) = 0 := by
  rw [kineticHamiltonianField_coordinates g c (x, 0) hx]
  simp
  rfl

theorem KineticLocalFlow.zero_momentum_fixed (g : SmoothMetric M) (c : M)
    (x : FourSpace) (hx : x ∈ (chartAt FourSpace c).target)
    (F : KineticLocalFlow g c (x, 0)) (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) :
    F.map ((x, 0), t) = (x, 0) := by
  have heq := F.eq_on (x, 0) (Metric.mem_ball_self F.radius_pos) (fun _ => (x, 0)) rfl
    (fun s _ => by
      rw [kineticHamiltonianField_zero_momentum g c x hx]
      exact hasDerivAt_const s (x, (0 : FourSpace)))
  exact heq ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The already constructed intrinsic frame flow has exactly the local
Hamiltonian trajectories produced by the variational ODE construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameCotangentState (g : SmoothMetric M) (c : M) (k : Fin 4)
    (e : FrameBundle g) : CotangentCoordinates :=
  (chartAt FourSpace c e.base,
    frameCotangentMomentum g c (chartAt FourSpace c e.base) (frameChartMatrix g c e) k)

theorem parallelFrameCurveAt_cotangent (g : SmoothMetric M) (c : M)
    (γ : ℝ → FrameBundle g) (k : Fin 4) (t : ℝ)
    (hγ : ContinuousAt γ t) (hc : (γ t).base ∈ (chartAt FourSpace c).source)
    (hp : ParallelFrameCurveAt g γ k t) :
    HasDerivAt (fun s => frameCotangentState g c k (γ s))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (frameCotangentState g c k (γ t))) t := by
  have hd := parallelFrameCurveAt_fixedChart g c γ t k hγ hc hp
  have hx : HasDerivAt (fun s => chartAt FourSpace c (γ s).base)
      (WithLp.toLp 2 (fun r => frameChartMatrix g c (γ t) r k)) t :=
    (ContinuousLinearMap.fst ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t hd
  have hE : HasDerivAt (fun s => frameChartMatrix g c (γ s))
      (-(parallelFrameConnection g c k (frameCoordinateState g c (γ t)) *
        frameChartMatrix g c (γ t))) t :=
    (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t hd
  exact hasDerivAt_parallelFrame_cotangentLift g c
    (fun s => chartAt FourSpace c (γ s).base)
    (fun s => frameChartMatrix g c (γ s)) t k
    ((chartAt FourSpace c).map_source hc) hx
    (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j)

variable [T2Space M] [CompactSpace M]

theorem parallelFrameFlowMap_cotangent_derivative (g : SmoothMetric M) (c : M)
    (k : Fin 4) (e : FrameBundle g) (t : ℝ)
    (ht : (parallelFrameFlowMap g k t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => frameCotangentState g c k (parallelFrameFlowMap g k s e))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (frameCotangentState g c k (parallelFrameFlowMap g k t e))) t :=
  parallelFrameCurveAt_cotangent g c _ k t
    (parallelFrameFlowMap_curve_continuous g k e).continuousAt ht
    (parallelFrameFlowMap_primitive g k e t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common neighborhood of actual frame trajectories is represented by
the constructed local kinetic flow. The chart-stay condition is obtained
from joint continuity, rather than supplied as an additional input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

namespace KineticLocalFlow

variable {g : SmoothMetric M} {c : M} {p : CotangentCoordinates}

theorem time_subset (F : KineticLocalFlow g c p)
    {δ : ℝ} (hδ : δ ≤ F.time) : Ioo (-δ) δ ⊆ Ioo (-F.time) F.time := by
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

/-- Restrict only the time interval of a constructed local flow. -/
def restrictTime (F : KineticLocalFlow g c p) (δ : ℝ)
    (hδ : 0 < δ) (hδF : δ ≤ F.time) : KineticLocalFlow g c p where
  radius := F.radius
  radius_pos := F.radius_pos
  time := δ
  time_pos := hδ
  map := F.map
  variation := F.variation
  continuous_map := F.continuous_map.mono (fun _ h => ⟨h.1, F.time_subset hδF h.2⟩)
  continuous_variation := F.continuous_variation.mono
    (fun _ h => ⟨h.1, F.time_subset hδF h.2⟩)
  initial := F.initial
  initial_variation := F.initial_variation
  inside := fun q hq t ht => F.inside q hq t (F.time_subset hδF ht)
  time_derivative := fun q hq t ht => F.time_derivative q hq t (F.time_subset hδF ht)
  variation_derivative := fun q hq t ht =>
    F.variation_derivative q hq t (F.time_subset hδF ht)
  joint_derivative := fun q hq t ht => F.joint_derivative q hq t (F.time_subset hδF ht)

end KineticLocalFlow

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial extension of the intrinsic frame flow is locally the actual
kinetic Hamiltonian flow, on an open set of radii and initial frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def radialFrameCotangentState (g : SmoothMetric M) (c : M) (k : Fin 4)
    (p : ℝ × FrameBundle g) : CotangentCoordinates :=
  kineticMomentumScale p.1 (frameCotangentState g c k p.2)

variable [T2Space M] [CompactSpace M]

theorem radialFrameFlowMap_cotangent_derivative (g : SmoothMetric M) (c : M)
    (k : Fin 4) (r t : ℝ) (e : FrameBundle g)
    (ht : (parallelFrameFlowMap g k (r * t) e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => radialFrameCotangentState g c k
        (r, parallelFrameFlowMap g k (r * s) e))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (radialFrameCotangentState g c k (r, parallelFrameFlowMap g k (r * t) e))) t := by
  apply hasDerivAt_kineticMomentumScale g c
    (fun s => frameCotangentState g c k (parallelFrameFlowMap g k s e)) r t
  · exact (chartAt FourSpace c).map_source ht
  · exact parallelFrameFlowMap_cotangent_derivative g c k e (r * t) ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The canonical unit tangent measure is normalized base volume times
spherical probability in every measurable positive reference frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

local instance instIsProbabilityMeasureDirectionsSphereMeasure_2_r862867_1 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
theorem continuous_unitTangentTurn :
    Continuous (fun p : FrameBundle g × Directions => unitTangentTurn p.1 p.2) :=
  (continuous_unitTangentOfFrame g).comp ((continuous_frameRotate g).comp
    (continuous_fst.prodMk (continuous_orientedToOrthogonal.comp
      (continuous_directionOrientedMatrix.comp continuous_snd))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The unit tangent fiber measure is independent of every orthonormal
reference frame, including its orientation. This allows the local Gram
frame in cotangent coordinates to compute the canonical spherical measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

local instance instIsProbabilityMeasureDirectionsSphereMeasure_3_r862867_1 : IsProbabilityMeasure sphereMeasure := actual_sphereMeasure_probability
theorem continuous_unitTangentTurn_fixed (e : FrameBundle g) :
    Continuous (unitTangentTurn e) := by
  have hp : Continuous (fun q : Directions => (e, q)) :=
    continuous_const.prodMk continuous_id
  have h : Continuous ((fun p : FrameBundle g × Directions => unitTangentTurn p.1 p.2) ∘
      (fun q : Directions => (e, q))) := continuous_unitTangentTurn.comp hp
  simpa only [Function.comp_def] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive-frame projection is a compact quotient. Consequently
the descended complete geodesic flow is jointly continuous, without a
continuous global choice of normal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M]

variable [CompactSpace M]

theorem compact_unitTangentBundle (g : SmoothMetric M) (o : FrameOrientation g) :
    CompactSpace (UnitTangentBundle g) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  let : CompactSpace o.positive :=
    isCompact_iff_compactSpace.mp o.clopen.isClosed.isCompact
  exact (positiveFirstProjection_surjective g o).compactSpace
    (positiveFirstProjection_quotient g o).continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cotangent coordinates of intrinsic unit tangent vectors. Lowering the
scaled tangent vector has an explicit inverse away from zero momentum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Bundle
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem unitCotangentState_frame (g : SmoothMetric M) (c : M)
    (r : ℝ) (e : FrameBundle g) :
    unitCotangentState g c r (unitTangentOfFrame e) =
      radialFrameCotangentState g c 0 (r, e) := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The base of the constructed complete parallel-frame curve is a genuine
C1 curve with unit metric speed. These are the curves used by the exponential
and polar-coordinate realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped BigOperators Manifold ContDiff _root_.Topology ENNReal Matrix.Norms.Elementwise

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def frameGeodesic (g : SmoothMetric M) (k : Fin 4) (e : FrameBundle g) (t : ℝ) : M :=
  (parallelFrameFlowMap g k t e).base

theorem frameGeodesic_continuous (g : SmoothMetric M) (k : Fin 4) (e : FrameBundle g) :
    Continuous (frameGeodesic g k e) :=
  (continuous_frameBase g).comp (parallelFrameFlowMap_curve_continuous g k e)

theorem frameGeodesic_chart_derivative (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (c : M) (t : ℝ)
    (ht : frameGeodesic g k e t ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => chartAt FourSpace c (frameGeodesic g k e s))
      (WithLp.toLp 2 (fun r => frameChartMatrix g c (parallelFrameFlowMap g k t e) r k)) t := by
  have hd := parallelFrameCurveAt_fixedChart g c (parallelFrameFlowMap g k · e) t k
    (parallelFrameFlowMap_curve_continuous g k e).continuousAt ht
    (parallelFrameFlowMap_primitive g k e t)
  exact (ContinuousLinearMap.fst ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t hd

theorem frameGeodesic_chart_contDiffOn (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (c : M) :
    ContDiffOn ℝ 1 (fun s => chartAt FourSpace c (frameGeodesic g k e s))
      {s | frameGeodesic g k e s ∈ (chartAt FourSpace c).source} := by
  let S : Set ℝ := {s | frameGeodesic g k e s ∈ (chartAt FourSpace c).source}
  let v : ℝ → FourSpace := fun s =>
    WithLp.toLp 2 (fun r => frameChartMatrix g c (parallelFrameFlowMap g k s e) r k)
  have hS : IsOpen S := (chartAt FourSpace c).open_source.preimage
    (frameGeodesic_continuous g k e)
  have hd : ∀ s ∈ S, HasDerivAt
      (fun t => chartAt FourSpace c (frameGeodesic g k e t)) (v s) s :=
    fun s hs => frameGeodesic_chart_derivative g k e c s hs
  have hv : ContinuousOn v S := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply (PiLp.continuous_toLp 2 _).continuousAt.comp
    apply continuousAt_pi.mpr
    intro r
    exact (frameChartMatrix_continuousAt g c _ hs r k).comp
      (f := fun t => parallelFrameFlowMap g k t e)
      (parallelFrameFlowMap_curve_continuous g k e).continuousAt
  apply (contDiffOn_one_iff_derivWithin hS.uniqueDiffOn).mpr
  refine ⟨fun s hs => (hd s hs).differentiableAt.differentiableWithinAt, ?_⟩
  apply hv.congr
  intro s hs
  exact (hd s hs).hasDerivWithinAt.derivWithin (hS.uniqueDiffOn s hs)

theorem frameGeodesic_contMDiff (g : SmoothMetric M) (k : Fin 4) (e : FrameBundle g) :
    ContMDiff 𝓘(ℝ, ℝ) I4 1 (frameGeodesic g k e) := by
  intro t
  let c := frameGeodesic g k e t
  let S : Set ℝ := {s | frameGeodesic g k e s ∈ (chartAt FourSpace c).source}
  have hS : S ∈ 𝓝 t := (frameGeodesic_continuous g k e).continuousAt.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds (mem_chart_source FourSpace c))
  have hx : ContDiffAt ℝ 1 (fun s => chartAt FourSpace c (frameGeodesic g k e s)) t :=
    (frameGeodesic_chart_contDiffOn g k e c t (mem_chart_source FourSpace c)).contDiffAt hS
  have hi : ContMDiffAt I4 I4 1 (chartAt FourSpace c).symm
      (chartAt FourSpace c (frameGeodesic g k e t)) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      ((chartAt FourSpace c).map_source (mem_chart_source FourSpace c))
  have hh := hi.comp t hx.contMDiffAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [hS] with s hs
  exact ((chartAt FourSpace c).left_inv hs).symm

omit [T2Space M] [CompactSpace M] in
theorem frameChart_column_eq_derivative (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (k : Fin 4) (he : e.base ∈ (chartAt FourSpace c).source) :
    WithLp.toLp 2 (fun r => frameChartMatrix g c e r k) =
      chartForwardOperator c e.base (e.frame.vector k) := by
  let u : UnitTangentBundle g := ⟨e.base, e.frame.vector k, e.frame.inner_vector_self k⟩
  calc
    _ = unitChartVelocity c u := by ext r; rfl
    _ = _ := unitChartVelocity_eq_derivative c u he

theorem frameGeodesic_mfderiv (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g k e) t 1 =
      (parallelFrameFlowMap g k t e).frame.vector k := by
  let c := frameGeodesic g k e t
  have hc : MDifferentiableAt I4 I4 (chartAt FourSpace c) c :=
    (contMDiffAt_of_mem_maximalAtlas (n := 1)
    (IsManifold.chart_mem_maximalAtlas c) (mem_chart_source FourSpace c)).mdifferentiableAt
      one_ne_zero
  have hγ := (frameGeodesic_contMDiff g k e).mdifferentiable one_ne_zero t
  have hcomp := mfderiv_comp t hc hγ
  have hd := frameGeodesic_chart_derivative g k e c t (mem_chart_source FourSpace c)
  have hd' : mfderiv 𝓘(ℝ, ℝ) I4
      (fun s => chartAt FourSpace c (frameGeodesic g k e s)) t 1 =
      WithLp.toLp 2 (fun r => frameChartMatrix g c (parallelFrameFlowMap g k t e) r k) := by
    rw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
    exact one_smul ℝ _
  have heq := congrArg (fun L : ℝ →L[ℝ] FourSpace => L 1) hcomp
  change (mfderiv 𝓘(ℝ, ℝ) I4
    (fun s => chartAt FourSpace c (frameGeodesic g k e s)) t) 1 =
      chartForwardOperator c c (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g k e) t 1) at heq
  rw [hd',
    frameChart_column_eq_derivative g c _ k (mem_chart_source FourSpace c)] at heq
  have hinj : Function.Injective (chartForwardOperator c c) := by
    apply Function.LeftInverse.injective (g := chartBackwardOperator c (chartAt FourSpace c c))
    intro v
    exact congrArg (fun L : FourSpace →L[ℝ] FourSpace => L v)
      (chartBackward_forward c c (mem_chart_source FourSpace c))
  exact hinj heq.symm

theorem frameGeodesic_metric_speed (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (t : ℝ) :
    metricTangentENorm g (frameGeodesic g k e t)
      (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g k e) t 1) = 1 := by
  rw [frameGeodesic_mfderiv]
  calc
    _ = ENNReal.ofReal (metricTangentNorm g (frameGeodesic g k e t)
        ((parallelFrameFlowMap g k t e).frame.vector k)) :=
      metricTangentENorm_eq_ofReal g _ _
    _ = ENNReal.ofReal (Real.sqrt (g.inner (frameGeodesic g k e t)
        ((parallelFrameFlowMap g k t e).frame.vector k)
        ((parallelFrameFlowMap g k t e).frame.vector k))) :=
      congrArg ENNReal.ofReal (metricTangentNorm_eq_sqrt g _ _)
    _ = 1 := by
      have h := congrArg (fun a : ℝ => ENNReal.ofReal (Real.sqrt a))
        ((parallelFrameFlowMap g k t e).frame.inner_vector_self k)
      simpa only [Real.sqrt_one, ENNReal.ofReal_one] using! h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Exact unit-speed length and endpoint distance bounds for the actual
complete geodesics, including their intrinsic unit-tangent formulation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameGeodesic_pathELength (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (a b : ℝ) :
    (let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I4 (frameGeodesic g k e) a b) = ENNReal.ofReal (b - a) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  change (∫⁻ s in Icc a b, metricTangentENorm g (frameGeodesic g k e s)
    (mfderiv 𝓘(ℝ, ℝ) I4 (frameGeodesic g k e) s 1)) = _
  simp_rw [frameGeodesic_metric_speed]
  simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc]

theorem frameGeodesic_distance_le (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (a b : ℝ) :
    metricEDistance g (frameGeodesic g k e a) (frameGeodesic g k e b) ≤
      ENNReal.ofReal |b - a| := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hbound (s t : ℝ) (hst : s ≤ t) :
      metricEDistance g (frameGeodesic g k e s) (frameGeodesic g k e t) ≤
        ENNReal.ofReal (t - s) := by
    change Manifold.riemannianEDist I4 _ _ ≤ _
    exact (Manifold.riemannianEDist_le_pathELength
      (frameGeodesic_contMDiff g k e).contMDiffOn rfl rfl hst).trans_eq
        (frameGeodesic_pathELength g k e s t)
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hbound a b hab
  · have hs : metricEDistance g (frameGeodesic g k e a) (frameGeodesic g k e b) =
        metricEDistance g (frameGeodesic g k e b) (frameGeodesic g k e a) :=
      Manifold.riemannianEDist_comm
    rw [hs, abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact hbound b a hba

theorem frameGeodesic_distance_from_start (g : SmoothMetric M) (k : Fin 4)
    (e : FrameBundle g) (t : ℝ) :
    metricEDistance g e.base (frameGeodesic g k e t) ≤ ENNReal.ofReal |t| := by
  simpa only [frameGeodesic, parallelFrameFlowMap_zero, sub_zero] using
    frameGeodesic_distance_le g k e 0 t

theorem unitGeodesic_eq_frameGeodesic (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) :
    unitGeodesic g o u = frameGeodesic g 0 (unitTangentFrame g o u) := rfl

theorem unitGeodesic_distance_from_start (g : SmoothMetric M) (o : FrameOrientation g)
    (u : UnitTangentBundle g) (t : ℝ) :
    metricEDistance g u.base (unitGeodesic g o u t) ≤ ENNReal.ofReal |t| := by
  have hbase : (unitTangentFrame g o u).base = u.base :=
    congrArg UnitTangentBundle.base (unitTangentOfFrame_lift g o u)
  simpa only [← unitGeodesic_eq_frameGeodesic g o u, hbase] using
    frameGeodesic_distance_from_start g 0 (unitTangentFrame g o u) t

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential in an orthonormal frame, constructed from the
complete unit-speed geodesics. The zero vector is included continuously,
using the proved metric length bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Bundle Filter Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : frameExponential g o e 0 = e.base := by
  apply Function.extend_apply'
  rintro ⟨v, hv⟩
  exact (show (v : FourSpace) ≠ 0 from v.property) hv

theorem frameExponential_distance (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) :
    metricEDistance g e.base (frameExponential g o e v) ≤ ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero, norm_zero, ENNReal.ofReal_zero]
    exact le_of_eq (Manifold.riemannianEDist_self (I := I4))
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
    have hr : (euclideanPolarHomeomorph w).2.val = ‖v‖ := by
      exact homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    rw [frameExponential_nonzero g o e w]
    have h := unitGeodesic_distance_from_start g o
      (unitTangentTurn e (euclideanPolarHomeomorph w).1)
      (euclideanPolarHomeomorph w).2.val
    have hb : (unitTangentTurn e (euclideanPolarHomeomorph w).1).base = e.base := rfl
    simpa only [frameExponentialNonzero, hb, hr, abs_of_nonneg (norm_nonneg v)] using h

theorem frameExponentialNonzero_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponentialNonzero g o e) := by
  have hu : Continuous (fun v : ({0}ᶜ : Set FourSpace) =>
      unitTangentTurn e (euclideanPolarHomeomorph v).1) :=
    (continuous_unitTangentTurn_fixed e).comp (euclideanPolarHomeomorph.continuous.fst)
  have ht : Continuous (fun v : ({0}ᶜ : Set FourSpace) =>
      (euclideanPolarHomeomorph v).2.val) :=
    continuous_subtype_val.comp euclideanPolarHomeomorph.continuous.snd
  exact (continuous_unitTangentBase g).comp
    ((unitTangentFlowMap_continuous g o).comp (ht.prodMk hu))

variable [T3Space M]

theorem frameExponential_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : Continuous (frameExponential g o e) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle FourSpace (TangentSpace I4 : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I4 M
  have ho : ContinuousOn (frameExponential g o e) ({0}ᶜ : Set FourSpace) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (frameExponentialNonzero_continuous g o e).congr
      (fun v => (frameExponential_nonzero g o e v).symm)
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    apply (tendsto_iff_edist_tendsto_0).mpr
    have hn : Tendsto (fun w : FourSpace => ENNReal.ofReal ‖w‖) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun w : FourSpace => ENNReal.ofReal ‖w‖) :=
        ENNReal.continuous_ofReal.comp continuous_norm
      simpa only [norm_zero, ENNReal.ofReal_zero] using hc.tendsto 0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn
      (fun _ => bot_le) (fun w => ?_)
    rw [frameExponential_zero, edist_comm]
    exact frameExponential_distance g o e w
  · exact (ho v hv).continuousAt (isOpen_compl_singleton.mem_nhds hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial geodesic motion, in each local cotangent chart, is
the constructed kinetic Hamiltonian flow. No continuous frame choice is
needed: uniqueness allows an arbitrary positive frame at the initial point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem unitRadialCotangentState_continuousAt (g : SmoothMetric M) (c : M)
    (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ContinuousAt (unitRadialCotangentState g c) p := by
  exact ContinuousAt.comp (x := p)
    (g := fun q : ℝ × UnitTangentBundle g => unitCotangentState g c q.1 q.2)
    (f := fun q : PositiveRadius × UnitTangentBundle g => (q.1.val, q.2))
    (unitCotangentState_continuousAt g c p.1.val p.2 hp)
    (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt)

theorem hasDerivAt_unitTangentRadial_cotangent (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (ht : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (fun s => unitRadialCotangentState g c (unitTangentRadialFlow g o s p))
      (cotangentHamiltonianField (kineticHamiltonian g c)
        (unitRadialCotangentState g c (unitTangentRadialFlow g o t p))) t := by
  obtain ⟨e, he, hue⟩ := exists_positive_unitTangent_frame g o p.2
  have heq (s : ℝ) : unitRadialCotangentState g c (unitTangentRadialFlow g o s p) =
      radialFrameCotangentState g c 0 (p.1.val,
        parallelFrameFlowMap g 0 (p.1.val * s) e) := by
    change unitCotangentState g c p.1.val
      (unitTangentFlowMap g o (p.1.val * s) p.2) = _
    rw [← hue, unitTangentFlowMap_of_frame g o _ e he, unitCotangentState_frame]
  have hbase : (parallelFrameFlowMap g 0 (p.1.val * t) e).base =
      (unitTangentRadialFlow g o t p).2.base := by
    change (parallelFrameFlowMap g 0 (p.1.val * t) e).base =
      (unitTangentFlowMap g o (p.1.val * t) p.2).base
    rw [← hue, unitTangentFlowMap_of_frame g o _ e he]
    rfl
  have h := radialFrameFlowMap_cotangent_derivative g c 0 p.1.val t e (hbase.symm ▸ ht)
  have hfun : (fun s => unitRadialCotangentState g c (unitTangentRadialFlow g o s p)) =
      (fun s => radialFrameCotangentState g c 0 (p.1.val,
        parallelFrameFlowMap g 0 (p.1.val * s) e)) := funext heq
  rw [hfun, heq]
  exact h

theorem unitTangentRadialFlow_joint_continuous (g : SmoothMetric M) (o : FrameOrientation g) :
    Continuous (fun z : ℝ × (PositiveRadius × UnitTangentBundle g) =>
      unitTangentRadialFlow g o z.1 z.2) := by
  have hr : Continuous (fun z : ℝ × (PositiveRadius × UnitTangentBundle g) => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hu : Continuous (fun z : ℝ × (PositiveRadius × UnitTangentBundle g) => z.2.2) :=
    continuous_snd.comp continuous_snd
  exact hr.prodMk ((unitTangentFlowMap_continuous g o).comp
    (((continuous_subtype_val.comp hr).mul continuous_fst).prodMk hu))

theorem unitTangentRadialFlow_chart_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
      ∃ δ > (0 : ℝ), ∀ q ∈ U, ∀ t ∈ Ioo (-δ) δ,
        (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace c).source := by
  have hb : Continuous (fun u : UnitTangentBundle g => u.base) :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp
      (show Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) from
        continuous_induced_dom)
  have hc := (hb.comp (continuous_snd.comp
    (unitTangentRadialFlow_joint_continuous g o))).continuousAt (x := (0, p))
  have hzero : (unitTangentRadialFlow g o 0 p).2 = p.2 := by
    change unitTangentFlowMap g o (p.1.val * 0) p.2 = p.2
    rw [mul_zero, unitTangentFlowMap_zero]
  have hn : {z : ℝ × (PositiveRadius × UnitTangentBundle g) |
      (unitTangentRadialFlow g o z.1 z.2).2.base ∈ (chartAt FourSpace c).source}
      ∈ 𝓝 ((0 : ℝ), p) := hc.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds (by
      change (unitTangentRadialFlow g o 0 p).2.base ∈ (chartAt FourSpace c).source
      rw [hzero]
      exact hp))
  obtain ⟨T, U, hT, h0, hU, hpU, hTU⟩ := mem_nhds_prod_iff'.mp hn
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨U, hU, hpU, δ, hδ, fun q hq t ht => ?_⟩
  have htT : t ∈ T := hδT (by simpa only [Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs] using abs_lt.mpr ht)
  exact hTU (show (t, q) ∈ T ×ˢ U from ⟨htT, hq⟩)

/-- A common open intrinsic neighborhood is conjugate to the actual local
Hamiltonian flow. This is the local input for transporting its volume law. -/
theorem exists_unitTangent_localHamiltonian (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
      ∃ F : KineticLocalFlow g c (unitRadialCotangentState g c p),
        (∀ q ∈ U, unitRadialCotangentState g c q ∈
          Metric.ball (unitRadialCotangentState g c p) F.radius) ∧
        (∀ q ∈ U, EqOn (fun t => F.map (unitRadialCotangentState g c q, t))
          (fun t => unitRadialCotangentState g c (unitTangentRadialFlow g o t q))
          (Ioo (-F.time) F.time)) := by
  obtain ⟨F₀⟩ := exists_kineticLocalFlow g c (unitRadialCotangentState g c p)
    ((chartAt FourSpace c).map_source hp)
  obtain ⟨V, hV, hpV, δ, hδ, hchart⟩ :=
    unitTangentRadialFlow_chart_neighborhood g o c p hp
  have hn : {q : PositiveRadius × UnitTangentBundle g | unitRadialCotangentState g c q ∈
      Metric.ball (unitRadialCotangentState g c p) F₀.radius} ∈ 𝓝 p :=
    (unitRadialCotangentState_continuousAt g c p hp).preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self F₀.radius_pos))
  obtain ⟨W, hWsub, hW, hpW⟩ := mem_nhds_iff.mp hn
  let τ := min F₀.time δ
  have hτ : 0 < τ := lt_min F₀.time_pos hδ
  let F := F₀.restrictTime τ hτ (min_le_left _ _)
  have htime {t : ℝ} (ht : t ∈ Ioo (-F.time) F.time) : t ∈ Ioo (-δ) δ := by
    have hle : F.time ≤ δ := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨V ∩ W, hV.inter hW, ⟨hpV, hpW⟩, F, (fun q hq => hWsub hq.2), ?_⟩
  intro q hq
  apply F.eq_on _ (hWsub hq.2)
  · change unitCotangentState g c q.1.val
      (unitTangentFlowMap g o (q.1.val * 0) q.2) = _
    rw [mul_zero, unitTangentFlowMap_zero]
    rfl
  · intro t ht
    exact hasDerivAt_unitTangentRadial_cotangent g o c q t (hchart q hq.1 t (htime ht))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial exponential is the actual local kinetic endpoint map near
zero. A common coordinate interval works for every unit direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

theorem unitGeodesic_turn_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (q : Directions) :
    unitGeodesic g o (unitTangentTurn e q) 0 = e.base := by
  rw [unitGeodesic, unitTangentFlowMap_zero]
  rfl

theorem unitGeodesic_turn_joint_continuous (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    Continuous (fun p : ℝ × Directions => unitGeodesic g o (unitTangentTurn e p.2) p.1) := by
  have harg : Continuous (fun p : ℝ × Directions => (p.1, unitTangentTurn e p.2)) :=
    continuous_fst.prodMk ((continuous_unitTangentTurn_fixed e).comp continuous_snd)
  exact (continuous_unitTangentBase g).comp ((unitTangentFlowMap_continuous g o).comp harg)

theorem direction_uniform_neighborhood {X : Type*} [TopologicalSpace X]
    (b : ℝ × Directions → X) (hb : Continuous b) (S : Set X) (hS : IsOpen S)
    (hzero : ∀ q, b (0, q) ∈ S) :
    ∃ δ > (0 : ℝ), ∀ q : Directions, ∀ t ∈ Ioo (-δ) δ, b (t, q) ∈ S := by
  have hz : ({0} : Set ℝ) ×ˢ (univ : Set Directions) ⊆ b ⁻¹' S := by
    rintro ⟨t, q⟩ ⟨ht, _⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero q
  obtain ⟨T, U, hT, _, h0, hU, hTU⟩ :=
    generalized_tube_lemma (s := ({0} : Set ℝ)) (t := (univ : Set Directions))
      isCompact_singleton isCompact_univ (hS.preimage hb) hz
  have h0T : (0 : ℝ) ∈ T := h0 rfl
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0T)
  refine ⟨δ, hδ, fun q t ht => hTU ?_⟩
  exact ⟨hδT (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    using abs_lt.mpr ht), hU (mem_univ q)⟩

theorem unitGeodesic_uniform_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ δ > (0 : ℝ), ∀ q : Directions, ∀ t ∈ Ioo (-δ) δ,
      unitGeodesic g o (unitTangentTurn e q) t ∈ (chartAt FourSpace c).source := by
  apply direction_uniform_neighborhood
    (fun p : ℝ × Directions => unitGeodesic g o (unitTangentTurn e p.2) p.1)
    (unitGeodesic_turn_joint_continuous g o e)
    (chartAt FourSpace c).source (chartAt FourSpace c).open_source
  intro q
  rw [unitGeodesic_turn_zero]
  exact he

/-- Every sufficiently short radial geodesic starting at a fixed frame
satisfies the same constructed local Hamiltonian flow, uniformly in direction. -/
theorem KineticLocalFlow.radial_endpoint_uniform (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (F : KineticLocalFlow g c (chartAt FourSpace c e.base, 0)) :
    ∃ ε > (0 : ℝ), ∀ q : Directions, ∀ r : ℝ, 0 < r → r < ε →
      ∀ t ∈ Ioo (-F.time) F.time,
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e (r • q.val)), t) =
          unitCotangentState g c r (unitTangentFlowMap g o (r * t) (unitTangentTurn e q)) := by
  obtain ⟨δ, hδ, hchart⟩ := unitGeodesic_uniform_chart g o c e he
  let P := frameMomentumMap g c e
  let ε := min (F.radius / (‖P‖ + 1)) (δ / (F.time + 1))
  have hP : 0 < ‖P‖ + 1 := by positivity
  have htime : 0 < F.time + 1 := by linarith [F.time_pos]
  have hε : 0 < ε := lt_min (div_pos F.radius_pos hP) (div_pos hδ htime)
  refine ⟨ε, hε, fun q r hr hrε t ht => ?_⟩
  have hrP : r * (‖P‖ + 1) < F.radius :=
    (lt_div_iff₀ hP).mp (hrε.trans_le (min_le_left _ _))
  have hrδ : r * (F.time + 1) < δ :=
    (lt_div_iff₀ htime).mp (hrε.trans_le (min_le_right _ _))
  have hqn : ‖q.val‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using q.property
  have hmoment : ‖P (r • q.val)‖ < F.radius := by
    have h := P.le_opNorm (r • q.val)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hqn, mul_one] at h
    nlinarith [norm_nonneg P]
  have hinit : (chartAt FourSpace c e.base, P (r • q.val)) ∈
      Metric.ball (chartAt FourSpace c e.base, 0) F.radius := by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_self, dist_zero_right,
      max_eq_right (norm_nonneg _)] using hmoment
  have hsource (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      unitGeodesic g o (unitTangentTurn e q) (r * s) ∈ (chartAt FourSpace c).source := by
    apply hchart q (r * s)
    have hsabs : |s| < F.time := abs_lt.mpr hs
    have hsmall : |r * s| < δ := by
      rw [abs_mul, abs_of_pos hr]
      nlinarith [abs_nonneg s]
    exact abs_lt.mp hsmall
  have hsol (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :=
    hasDerivAt_unitTangentRadial_cotangent g o c
      (⟨r, hr⟩, unitTangentTurn e q) s (hsource s hs)
  have heq := F.eq_on _ hinit
    (fun s => unitCotangentState g c r (unitTangentFlowMap g o (r * s) (unitTangentTurn e q)))
    (by simpa only [mul_zero, unitTangentFlowMap_zero] using
      unitCotangentState_turn g c e he r q) hsol
  exact heq ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Open cotangent neighborhoods for the actual radial flow. The local
Hamiltonian volume identity holds on every measurable subset of the initial
ball, and the intrinsic flow remains in the same chart on a common interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem isOpen_unitRadialCotangentState_image (g : SmoothMetric M) (c : M)
    (U : Set (PositiveRadius × UnitTangentBundle g)) (hU : IsOpen U)
    (hsource : ∀ q ∈ U, q.2.base ∈ (chartAt FourSpace c).source) :
    IsOpen (unitRadialCotangentState g c '' U) := by
  let E : PositiveRadius × ChartUnitTangent g c →
      PositiveRadius × UnitTangentBundle g := fun q => (q.1, q.2.val)
  have hE : Continuous E := continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)
  let H := unitTangentCotangentHomeomorph g c
  have hN : IsOpen {z : CotangentCoordinates |
      z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0} :=
    ((chartAt FourSpace c).open_target.preimage continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)
  have hopen : IsOpen (Subtype.val '' (H '' (E ⁻¹' U))) :=
    hN.isOpenMap_subtype_val _ (H.isOpenMap _ (hU.preimage hE))
  have heq : Subtype.val '' (H '' (E ⁻¹' U)) = unitRadialCotangentState g c '' U := by
    ext z
    constructor
    · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨E q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      let a : PositiveRadius × ChartUnitTangent g c :=
        (q.1, ⟨q.2, hsource q hq⟩)
      exact ⟨H a, ⟨a, hq, rfl⟩, rfl⟩
  rwa [heq] at hopen

variable [T2Space M] [CompactSpace M]

theorem radial_chart_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g), IsOpen U ∧ p ∈ U ∧
      ∃ δ > (0 : ℝ), ∀ q ∈ U, ∀ t ∈ Ioo (-δ) δ,
        (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace c).source := by
  have hb : Continuous (fun u : UnitTangentBundle g => u.base) :=
    (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).comp
      (show Continuous (unitTangentRealization : UnitTangentBundle g → TangentBundle I4 M) from
        continuous_induced_dom)
  have hc := (hb.comp (continuous_snd.comp
    (unitTangentRadialFlow_joint_continuous g o))).continuousAt (x := (0, p))
  have hzero : (unitTangentRadialFlow g o 0 p).2 = p.2 := by
    change unitTangentFlowMap g o (p.1.val * 0) p.2 = p.2
    rw [mul_zero, unitTangentFlowMap_zero]
  have hn : {z : ℝ × (PositiveRadius × UnitTangentBundle g) |
      (unitTangentRadialFlow g o z.1 z.2).2.base ∈ (chartAt FourSpace c).source}
      ∈ 𝓝 ((0 : ℝ), p) := hc.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds (by
      change (unitTangentRadialFlow g o 0 p).2.base ∈ (chartAt FourSpace c).source
      rw [hzero]
      exact hp))
  obtain ⟨T, U, hT, h0, hU, hpU, hTU⟩ := mem_nhds_prod_iff'.mp hn
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds h0)
  refine ⟨U, hU, hpU, δ, hδ, fun q hq t ht => ?_⟩
  have htT : t ∈ T := hδT (by simpa only [Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs] using abs_lt.mpr ht)
  exact hTU (show (t, q) ∈ T ×ˢ U from ⟨htT, hq⟩)

/-- An intrinsic neighborhood has an open cotangent image lying in the
initial Hamiltonian ball. Every trajectory stays in the chosen base chart,
and its cotangent image agrees with the constructed Hamiltonian flow. -/
theorem exists_unitTangent_cotangentNeighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p.2.base ∈ (chartAt FourSpace c).source) :
    ∃ U : Set (PositiveRadius × UnitTangentBundle g),
      ∃ V : Set CotangentCoordinates,
      ∃ F : KineticLocalFlow g c (unitRadialCotangentState g c p),
        IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ unitRadialCotangentState g c p ∈ V ∧
        V = unitRadialCotangentState g c '' U ∧
        V ⊆ Metric.ball (unitRadialCotangentState g c p) F.radius ∧
        (∀ z ∈ V, z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0) ∧
        (∀ q ∈ U, ∀ t ∈ Ioo (-F.time) F.time,
          (unitTangentRadialFlow g o t q).2.base ∈ (chartAt FourSpace c).source) ∧
        (∀ q ∈ U, EqOn (fun t => F.map (unitRadialCotangentState g c q, t))
          (fun t => unitRadialCotangentState g c (unitTangentRadialFlow g o t q))
          (Ioo (-F.time) F.time)) := by
  obtain ⟨U₀, hU₀, hpU₀, F₀, hball, heq⟩ :=
    exists_unitTangent_localHamiltonian g o c p hp
  obtain ⟨U₁, hU₁, hpU₁, δ, hδ, hchart⟩ := radial_chart_neighborhood g o c p hp
  let τ := min F₀.time δ
  have hτ : 0 < τ := lt_min F₀.time_pos hδ
  let F := F₀.restrictTime τ hτ (min_le_left _ _)
  let U := U₀ ∩ U₁
  have htime {t : ℝ} (ht : t ∈ Ioo (-F.time) F.time) :
      t ∈ Ioo (-F₀.time) F₀.time ∧ t ∈ Ioo (-δ) δ := by
    have h0 : F.time ≤ F₀.time := min_le_left _ _
    have h1 : F.time ≤ δ := min_le_right _ _
    constructor <;> constructor <;> linarith [ht.1, ht.2]
  have hsource (q) (hq : q ∈ U) : q.2.base ∈ (chartAt FourSpace c).source := by
    have h := hchart q hq.2 0 (by constructor <;> linarith)
    change (unitTangentFlowMap g o (q.1.val * 0) q.2).base ∈ _ at h
    simpa only [mul_zero, unitTangentFlowMap_zero] using h
  let V := unitRadialCotangentState g c '' U
  refine ⟨U, V, F, hU₀.inter hU₁, ⟨hpU₀, hpU₁⟩,
    isOpen_unitRadialCotangentState_image g c U (hU₀.inter hU₁) hsource,
    ⟨p, ⟨hpU₀, hpU₁⟩, rfl⟩, rfl, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨q, hq, rfl⟩
    exact hball q hq.1
  · rintro z ⟨q, hq, rfl⟩
    exact ⟨(chartAt FourSpace c).map_source (hsource q hq),
      unitCotangentState_momentum_ne_zero g c q.1.val q.1.property q.2 (hsource q hq)⟩
  · intro q hq t ht
    exact hchart q hq.2 t (htime ht).2
  · intro q hq t ht
    exact heq q hq.1 (htime ht).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative of the actual radial exponential at the zero vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_chart_eventually_kinetic (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (F : KineticLocalFlow g c (chartAt FourSpace c e.base, 0))
    (t : ℝ) (ht : t ∈ Ioo (-F.time) F.time) (ht0 : 0 < t) :
    ∀ᶠ v in 𝓝 (0 : FourSpace),
      chartAt FourSpace c (frameExponential g o e (t • v)) =
        (F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)).1 := by
  obtain ⟨ε, hε, hradial⟩ := F.radial_endpoint_uniform g o c e he
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) hε] with v hv
  have hvε : ‖v‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  by_cases hv0 : v = 0
  · subst v
    simp only [smul_zero, frameExponential_zero, map_zero]
    exact (congrArg Prod.fst (F.zero_momentum_fixed g c _
      ((chartAt FourSpace c).map_source he) t ht)).symm
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv0⟩
    let q := (euclideanPolarHomeomorph w).1
    let r := (euclideanPolarHomeomorph w).2
    have hr : 0 < r.val := r.property
    have hrnorm : r.val = ‖v‖ := homeomorphUnitSphereProd_apply_snd_coe FourSpace w
    have hvr : r.val • q.val = v := by
      have h := congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
      exact h
    have hexp : frameExponential g o e (t • v) =
        unitGeodesic g o (unitTangentTurn e q) (r.val * t) := by
      rw [← hvr, smul_smul]
      simpa only [mul_comm] using
        frameExponential_radial g o e q ⟨t * r.val, mul_pos ht0 hr⟩
    rw [hexp]
    have hh := congrArg Prod.fst (hradial q r.val hr (hrnorm ▸ hvε) t ht)
    rw [hvr] at hh
    exact hh.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact invariant radius slabs. A finite collection of the constructed
Hamiltonian charts provides one positive time valid throughout each slab. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def radialSlab (g : SmoothMetric M) (a b : ℝ) :
    Set (PositiveRadius × UnitTangentBundle g) :=
  {p | a ≤ p.1.val ∧ p.1.val ≤ b}

theorem isCompact_radialSlab (g : SmoothMetric M) (o : FrameOrientation g)
    {a b : ℝ} (ha : 0 < a) : IsCompact (radialSlab g a b) := by
  let : CompactSpace (UnitTangentBundle g) := compact_unitTangentBundle g o
  let f : Icc a b × UnitTangentBundle g → PositiveRadius × UnitTangentBundle g :=
    fun p => (⟨p.1.val, lt_of_lt_of_le ha p.1.property.1⟩, p.2)
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk
      (fun p => lt_of_lt_of_le ha p.1.property.1)).prodMk continuous_snd
  have heq : f '' univ = radialSlab g a b := by
    ext p
    constructor
    · rintro ⟨q, _, rfl⟩
      exact q.1.property
    · intro hp
      exact ⟨(⟨p.1.val, hp⟩, p.2), mem_univ _, rfl⟩
  rw [← heq]
  exact isCompact_univ.image hf

theorem unitTangentRadialFlow_mem_slab (g : SmoothMetric M) (o : FrameOrientation g)
    (a b t : ℝ) (p : PositiveRadius × UnitTangentBundle g) :
    unitTangentRadialFlow g o t p ∈ radialSlab g a b ↔ p ∈ radialSlab g a b := Iff.rfl

theorem exists_radialHamiltonianChart (g : SmoothMetric M) (o : FrameOrientation g)
    (p : PositiveRadius × UnitTangentBundle g) :
    ∃ C : RadialHamiltonianChart g o, p ∈ C.domain := by
  obtain ⟨U, V, F, hU, hpU, hV, _hpV, hVU, hball, hin, hchart, heq⟩ :=
    exists_unitTangent_cotangentNeighborhood g o p.2.base p
      (mem_chart_source FourSpace p.2.base)
  exact ⟨{
    anchor := p
    center := p.2.base
    domain := U
    image := V
    flow := F
    open_domain := hU
    anchor_mem := hpU
    open_image := hV
    image_eq := hVU
    image_subset_ball := hball
    image_in_chart := hin
    trajectory_in_chart := hchart
    conjugacy := heq }, hpU⟩

/-- A single positive time works in actual Hamiltonian charts around all
points of a compact radius slab. The centers and charts may vary pointwise. -/
theorem radialSlab_uniform_hamiltonian_time (g : SmoothMetric M) (o : FrameOrientation g)
    {a b : ℝ} (ha : 0 < a) :
    ∃ ε > (0 : ℝ), ∀ p ∈ radialSlab g a b,
      ∃ C : RadialHamiltonianChart g o, p ∈ C.domain ∧ ε ≤ C.flow.time := by
  classical
  choose C hC using exists_radialHamiltonianChart g o
  obtain ⟨s, hs⟩ := (isCompact_radialSlab g o ha).elim_finite_subcover
    (fun p => (C p).domain) (fun p => (C p).open_domain)
    (fun p _ => mem_iUnion.mpr ⟨p, hC p⟩)
  obtain ⟨ε, hε, he⟩ := finite_positive_lower_bound_p0 s
    (fun p => (C p).flow.time) (fun p _ => (C p).flow.time_pos)
  refine ⟨ε, hε, fun p hp => ?_⟩
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp (hs hp)
  exact ⟨C q, hpq, he q hq⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous differentiability of the actual radial flow is local in cotangent charts
and is stable under its intrinsic time-composition law. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_zero_eventually (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : p.2.base ∈ (chartAt FourSpace d).source) :
    radialCoordinateFlow g o c d 0 =ᶠ[𝓝 (unitRadialCotangentState g c p)]
      cotangentChartTransition g c d := by
  have hz := radial_state_domain_nhds g c p hc
  have hret := cotangentRadialRetraction_continuousAt g c (unitRadialCotangentState g c p)
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hb := (continuous_unitTangentBase g).continuousAt.comp
    (continuous_snd.continuousAt.comp hret)
  have hd' : (cotangentRadialRetraction g c (unitRadialCotangentState g c p)).2.base ∈
      (chartAt FourSpace d).source := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hd
  filter_upwards [hz, hb.preimage_mem_nhds ((chartAt FourSpace d).open_source.mem_nhds hd')] with z hzc hzd
  rw [radialCoordinateFlow, unitTangentRadialFlow_zero,
    cotangentChartTransition_retraction g o c d z hzc hzd]

theorem radialFlowContDiffAt_zero (g : SmoothMetric M) (o : FrameOrientation g)
    (p : PositiveRadius × UnitTangentBundle g) : RadialFlowContDiffAt g o 0 p := by
  intro c d hc hd
  rw [unitTangentRadialFlow_zero] at hd
  have hin : (chartAt FourSpace c).symm (unitRadialCotangentState g c p).1 ∈
      (chartAt FourSpace d).source := by
    change (chartAt FourSpace c).symm (chartAt FourSpace c p.2.base) ∈ _
    rwa [(chartAt FourSpace c).left_inv hc]
  exact ((cotangentChartTransition_contDiffAt g c d _
    ((chartAt FourSpace c).map_source hc) hin).of_le (by first | simp | exact_mod_cast le_top)).congr_of_eventuallyEq
      (radialCoordinateFlow_zero_eventually g o c d p hc hd)

/-- A derivative in one pair of actual charts gives the derivative in every
pair of charts at the same source and target. -/
theorem radialFlowContDiffAt_of_chart (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (p : PositiveRadius × UnitTangentBundle g) (c₀ d₀ : M)
    (hc₀ : p.2.base ∈ (chartAt FourSpace c₀).source)
    (hd₀ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₀).source)
    (hcore : ContDiffAt ℝ 1 (radialCoordinateFlow g o c₀ d₀ t)
      (unitRadialCotangentState g c₀ p)) : RadialFlowContDiffAt g o t p := by
  intro c d hc hd
  have hin := radialFlowContDiffAt_zero g o p c c₀ hc
    (by simpa only [unitTangentRadialFlow_zero] using hc₀)
  have hcore' : ContDiffAt ℝ 1 (radialCoordinateFlow g o c₀ d₀ t)
      (radialCoordinateFlow g o c c₀ 0 (unitRadialCotangentState g c p)) := by
    simpa only [radialCoordinateFlow_at_state g o c c₀ 0 p hc, unitTangentRadialFlow_zero] using hcore
  have hmid := hcore'.comp (unitRadialCotangentState g c p) hin
  have hmid' : ContDiffAt ℝ 1 (radialCoordinateFlow g o c d₀ t)
      (unitRadialCotangentState g c p) := by
    apply hmid.congr_of_eventuallyEq
    simpa only [add_zero] using radialCoordinateFlow_add_eventually g o c c₀ d₀ t 0 p hc
      (by simpa only [unitTangentRadialFlow_zero] using hc₀)
  have hout := radialFlowContDiffAt_zero g o (unitTangentRadialFlow g o t p) d₀ d hd₀
    (by simpa only [unitTangentRadialFlow_zero] using hd)
  have hout' : ContDiffAt ℝ 1 (radialCoordinateFlow g o d₀ d 0)
      (radialCoordinateFlow g o c d₀ t (unitRadialCotangentState g c p)) := by
    simpa only [radialCoordinateFlow_at_state g o c d₀ t p hc] using hout
  apply (hout'.comp (unitRadialCotangentState g c p) hmid').congr_of_eventuallyEq
  simpa only [zero_add] using radialCoordinateFlow_add_eventually g o c d₀ d 0 t p hc hd₀

theorem RadialHamiltonianChart.contDiffAt (g : SmoothMetric M) (o : FrameOrientation g)
    (C : RadialHamiltonianChart g o) (p : PositiveRadius × UnitTangentBundle g)
    (hp : p ∈ C.domain) (t : ℝ) (ht : t ∈ Ioo (-C.flow.time) C.flow.time) :
    RadialFlowContDiffAt g o t p := by
  have hzero : (0 : ℝ) ∈ Ioo (-C.flow.time) C.flow.time :=
    ⟨by linarith [C.flow.time_pos], C.flow.time_pos⟩
  have hc : p.2.base ∈ (chartAt FourSpace C.center).source := by
    simpa only [unitTangentRadialFlow_zero] using C.trajectory_in_chart p hp 0 hzero
  have hd := C.trajectory_in_chart p hp t ht
  apply radialFlowContDiffAt_of_chart g o t p C.center C.center hc hd
  have hz := radial_state_domain_nhds g C.center p hc
  have hr := cotangentRadialRetraction_continuousAt g C.center (unitRadialCotangentState g C.center p)
    ⟨(chartAt FourSpace C.center).map_source hc,
      unitCotangentState_momentum_ne_zero g C.center p.1.val p.1.property p.2 hc⟩
  have hp' : cotangentRadialRetraction g C.center (unitRadialCotangentState g C.center p) ∈ C.domain := by
    rwa [cotangentRadialRetraction_state g C.center p hc]
  have heq : radialCoordinateFlow g o C.center C.center t =ᶠ[𝓝 (unitRadialCotangentState g C.center p)]
      (fun z => C.flow.map (z, t)) := by
    filter_upwards [hz, hr.preimage_mem_nhds (C.open_domain.mem_nhds hp')] with z hzc hzp
    have h := C.conjugacy (cotangentRadialRetraction g C.center z) hzp ht
    rw [unitRadialCotangentState_retraction g C.center z hzc] at h
    exact h.symm
  have hball : unitRadialCotangentState g C.center p ∈
      Metric.ball (unitRadialCotangentState g C.center C.anchor) C.flow.radius := by
    apply C.image_subset_ball
    rw [C.image_eq]
    exact mem_image_of_mem _ hp
  exact (C.flow.contDiffAt_slice _ hball t ht).congr_of_eventuallyEq heq


/-- Compact radius slabs give one interval of continuously differentiable flow times. -/
theorem radialFlowContDiffAt_uniform_time (g : SmoothMetric M) (o : FrameOrientation g)
    (a b : ℝ) (ha : 0 < a) :
    ∃ ε > (0 : ℝ), ∀ p ∈ radialSlab g a b, ∀ t : ℝ, |t| < ε →
      RadialFlowContDiffAt g o t p := by
  obtain ⟨ε, hε, hcharts⟩ := radialSlab_uniform_hamiltonian_time g o (b := b) ha
  refine ⟨ε, hε, fun p hp t ht => ?_⟩
  obtain ⟨C, hpC, hεC⟩ := hcharts p hp
  apply C.contDiffAt g o p hpC t
  have htime : |t| < C.flow.time := ht.trans_le hεC
  exact abs_lt.mp htime

/-- The constructed complete radial flow is continuously differentiable in its initial
cotangent state at every time. No differentiability of a chosen global ODE
solution is assumed. -/
theorem radialFlowContDiffAt_all_time (g : SmoothMetric M) (o : FrameOrientation g)
    (t : ℝ) (p : PositiveRadius × UnitTangentBundle g) :
    RadialFlowContDiffAt g o t p := by
  let a := p.1.val / 2
  let b := 2 * p.1.val
  have ha : 0 < a := half_pos p.1.property
  have hp : p ∈ radialSlab g a b := by
    change p.1.val / 2 ≤ p.1.val ∧ p.1.val ≤ 2 * p.1.val
    have hr : 0 < p.1.val := p.1.property
    constructor <;> linarith
  obtain ⟨ε, hε, hlocal⟩ := radialFlowContDiffAt_uniform_time g o a b ha
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hε.le) hn
  have hnzero : (n : ℝ) ≠ 0 := hnpos.ne'
  let s : ℝ := t / n
  have hs : |s| < ε := by
    dsimp [s]
    rw [abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
    have hh := (div_lt_iff₀ hε).mp hn
    nlinarith
  have hmul (m : ℕ) : ∀ q ∈ radialSlab g a b,
      RadialFlowContDiffAt g o ((m : ℝ) * s) q := by
    induction m with
    | zero =>
      intro q _hq
      simpa only [Nat.cast_zero, zero_mul] using radialFlowContDiffAt_zero g o q
    | succ m ih =>
      intro q hq
      have hq' : unitTangentRadialFlow g o ((m : ℝ) * s) q ∈ radialSlab g a b :=
        (unitTangentRadialFlow_mem_slab g o a b _ q).mpr hq
      have hstep := hlocal _ hq' s hs
      have h := RadialFlowContDiffAt.add g o s ((m : ℝ) * s) q hstep (ih q hq)
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      rw [Nat.cast_succ]
      ring
  have heq : (n : ℝ) * s = t := by dsimp [s]; field_simp [hnzero]
  simpa only [heq] using hmul n p hp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous differentiability of the actual exponential in coordinate
charts, including the zero vector. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameExponential_chart_contDiffAt_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ContDiffAt ℝ 1 (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e v)) 0 := by
  obtain ⟨F⟩ := exists_kineticLocalFlow g c (chartAt FourSpace c e.base, 0)
    ((chartAt FourSpace c).map_source he)
  let t := F.time / 2
  have ht0 : 0 < t := half_pos F.time_pos
  have ht : t ∈ Ioo (-F.time) F.time := by
    dsimp [t]
    constructor <;> linarith [F.time_pos]
  have hinit : ContDiffAt ℝ 1
      (fun v : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e v)) 0 :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  have hF : ContDiffAt ℝ 1 (fun z => F.map (z, t))
      (chartAt FourSpace c e.base, frameMomentumMap g c e 0) := by
    simpa only [map_zero] using F.contDiffAt_slice _ (Metric.mem_ball_self F.radius_pos) t ht
  have hlocal : ContDiffAt ℝ 1
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v))) 0 := by
    have hcompose : ContDiffAt ℝ 1 (fun v : FourSpace =>
        F.map ((chartAt FourSpace c e.base, frameMomentumMap g c e v), t)) 0 :=
      ContDiffAt.comp (f := fun v : FourSpace =>
        (chartAt FourSpace c e.base, frameMomentumMap g c e v))
        (g := fun z : CotangentCoordinates => F.map (z, t)) 0 hF hinit
    exact hcompose.fst.congr_of_eventuallyEq
      (frameExponential_chart_eventually_kinetic g o c e he F t ht ht0)
  have hscale : ContDiffAt ℝ 1 (fun v : FourSpace => t⁻¹ • v) 0 :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).contDiff.contDiffAt
  have hlocal' : ContDiffAt ℝ 1
      (fun v : FourSpace => chartAt FourSpace c (frameExponential g o e (t • v)))
      (t⁻¹ • (0 : FourSpace)) := by simpa only [smul_zero] using hlocal
  have h := hlocal'.comp 0 hscale
  have heq : (fun v : FourSpace => chartAt FourSpace c
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace c (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  change ContDiffAt ℝ 1 (fun v : FourSpace => chartAt FourSpace c
    (frameExponential g o e (t • (t⁻¹ • v)))) 0 at h
  rwa [heq] at h

theorem frameExponential_chart_contDiffAt_nonzero (g : SmoothMetric M)
    (o : FrameOrientation g) (d : M) (e : FrameBundle g) (v : FourSpace) (hv : v ≠ 0)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 1 (fun w : FourSpace => chartAt FourSpace d (frameExponential g o e w)) v := by
  let c := e.base
  have he : e.base ∈ (chartAt FourSpace c).source := mem_chart_source FourSpace e.base
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  let p : PositiveRadius × UnitTangentBundle g := (r, unitTangentTurn e q)
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c p =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  have hout : (unitTangentRadialFlow g o 1 p).2.base = frameExponential g o e v := by
    change (unitTangentFlowMap g o (r.val * 1) (unitTangentTurn e q)).base = _
    rw [mul_one, ← hvr, frameExponential_radial]
    rfl
  have hcore := radialFlowContDiffAt_all_time g o 1 p c d he (by rwa [hout])
  rw [hstate] at hcore
  have hinit : ContDiffAt ℝ 1
      (fun w : FourSpace => (chartAt FourSpace c e.base, frameMomentumMap g c e w)) v :=
    contDiffAt_const.prodMk (frameMomentumMap g c e).contDiff.contDiffAt
  apply ((hcore.comp v hinit).fst).congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds hv] with z hz
  exact (radialCoordinateFlow_frame_endpoint g o c d e he z hz).symm

/-- Every coordinate representation of the constructed exponential is C1
where its value belongs to that coordinate chart. -/
theorem frameExponential_chart_contDiffAt (g : SmoothMetric M)
    (o : FrameOrientation g) (d : M) (e : FrameBundle g) (v : FourSpace)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    ContDiffAt ℝ 1 (fun w : FourSpace => chartAt FourSpace d (frameExponential g o e w)) v := by
  by_cases hv : v = 0
  · subst v
    rw [frameExponential_zero] at hd
    exact frameExponential_chart_contDiffAt_zero g o d e hd
  · exact frameExponential_chart_contDiffAt_nonzero g o d e v hv hd

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

theorem frameExponential_contMDiff (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) : ContMDiff I4 I4 1 (frameExponential g o e) := by
  intro v
  let c := frameExponential g o e v
  have hc : frameExponential g o e v ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have hchart := frameExponential_chart_contDiffAt g o c e v hc
  have hinv : ContMDiffAt I4 I4 1 (chartAt FourSpace c).symm
      (chartAt FourSpace c (frameExponential g o e v)) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c)
      ((chartAt FourSpace c).map_source hc)
  have h := hinv.comp v hchart.contMDiffAt
  apply h.congr_of_eventuallyEq
  have hnear := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
    ((chartAt FourSpace c).open_source.mem_nhds hc)
  filter_upwards [hnear] with w hw
  exact ((chartAt FourSpace c).left_inv hw).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Finite regularity of matrix inversion in the four-dimensional heat
construction, via the actual determinant and adjugate formulas. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff

noncomputable section

theorem heatMatrixDeterminant_contDiffAt (n : ℕ) (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) x) :
    ContDiffAt ℝ n (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ _
  exact contDiffAt_const.mul (contDiffAt_prod fun i _ => hA (σ i) i)

theorem heatMatrixInverse_contDiffAt (n : ℕ) (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ i j, ContDiffAt ℝ n (fun y => A y i j) x) (hdet : (A x).det ≠ 0)
    (i j : Fin 4) : ContDiffAt ℝ n (fun y => (A y)⁻¹ i j) x := by
  have hinv : ContDiffAt ℝ n (fun y => ((A y).det)⁻¹) x :=
    (heatMatrixDeterminant_contDiffAt n A x hA).inv hdet
  have hadj : ContDiffAt ℝ n (fun y => (A y).adjugate i j) x := by
    simp only [Matrix.adjugate_apply]
    apply heatMatrixDeterminant_contDiffAt
    intro r s
    by_cases hr : r = j
    · subst r
      simpa only [Matrix.updateRow_self] using
        (contDiffAt_const : ContDiffAt ℝ n
          (fun _ : FourSpace => (Pi.single i (1 : ℝ) : Fin 4 → ℝ) s) x)
    · simpa only [Matrix.updateRow_ne hr] using hA r s
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    using hinv.mul hadj

end
end PositiveEinsteinFour.Geometry
end


section

/-! Inverse-metric and density derivatives from metric compatibility.
These local identities will be applied to the actual normal pullback metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatCompatibleMetric_inverse (G : FourSpace → Mat4) (x : FourSpace)
    (hG : ∀ p q, ContDiffAt ℝ 1 (fun y => G y p q) x) (hdet : (G x).det ≠ 0)
    (C : Mat4) (i : Fin 4) (hC : matrixPartial G i x = Cᵀ * G x + G x * C) :
    matrixPartial (fun y => (G y)⁻¹) i x = -(C * (G x)⁻¹) - (G x)⁻¹ * Cᵀ := by
  let H := fun y => (G y)⁻¹
  have hu : IsUnit (G x).det := isUnit_iff_ne_zero.mpr hdet
  have hD := heatMatrixDeterminant_contDiffAt 1 G x hG
  have hn : ∀ᶠ y in 𝓝 x, (G y).det ≠ 0 :=
    hD.continuousAt.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hdet)
  have he : (fun y => H y * G y) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [hn] with y hy
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy)
  have hdH (p q : Fin 4) : DifferentiableAt ℝ (fun y => H y p q) x :=
    (heatMatrixInverse_contDiffAt 1 G x hG hdet p q).differentiableAt one_ne_zero
  have hdG (p q : Fin 4) : DifferentiableAt ℝ (fun y => G y p q) x :=
    (hG p q).differentiableAt one_ne_zero
  have hp := matrixPartial_congr he i
  rw [matrixPartial_mul H G x hdH hdG i, hC] at hp
  have hz : matrixPartial (fun _ : FourSpace => (1 : Mat4)) i x = 0 := by
    ext p q
    simp [matrixPartial, partialDeriv]
  rw [hz] at hp
  have hh := congrArg (fun A : Mat4 => A * H x) hp
  have ha : (matrixPartial H i x * G x + H x * (Cᵀ * G x + G x * C)) * H x =
      matrixPartial H i x + H x * Cᵀ + C * H x := by
    calc
      _ = matrixPartial H i x * (G x * H x) +
          (H x * Cᵀ) * (G x * H x) + (H x * G x) * (C * H x) := by noncomm_ring
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu]; simp
  rw [ha, zero_mul] at hh
  change matrixPartial H i x = -(C * H x) - H x * Cᵀ
  have hh' : matrixPartial H i x = -(H x * Cᵀ + C * H x) :=
    eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using hh)
  rw [hh']
  abel

theorem heatCompatibleMetric_density (G : FourSpace → Mat4) (x : FourSpace)
    (hG : ∀ p q, ContDiffAt ℝ 1 (fun y => G y p q) x) (hpos : 0 < (G x).det)
    (C : Mat4) (i : Fin 4) (hC : matrixPartial G i x = Cᵀ * G x + G x * C) :
    partialDeriv (fun y => Real.sqrt (G y).det) i x = C.trace * Real.sqrt (G x).det := by
  let γ := fun t : ℝ => x + t • coordinateVector i
  have hγ : HasDerivAt γ (coordinateVector i) 0 := by
    simpa only [γ, one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add x
  have hγ0 : γ 0 = x := by simp [γ]
  have hdG (p q : Fin 4) : HasDerivAt (fun t => G (γ t) p q)
      ((Cᵀ * G x + G x * C) p q) 0 := by
    have hf : HasFDerivAt (fun y => G y p q) (fderiv ℝ (fun y => G y p q) x) (γ 0) := by
      rw [hγ0]
      exact (hG p q).differentiableAt one_ne_zero |>.hasFDerivAt
    have hd := hf.comp_hasDerivAt 0 hγ
    have hc := congrArg (fun A : Mat4 => A p q) hC
    change (fderiv ℝ (fun y => G y p q) x) (coordinateVector i) = _ at hc
    simpa only [Function.comp_def, hc] using! hd
  have hd := hasDerivAt_det_of_components (fun t => G (γ t)) (Cᵀ * G x + G x * C) 0 hdG
  rw [hγ0, determinantDifferential_congruence] at hd
  have hs := hd.sqrt (by simpa only [hγ0] using hpos.ne')
  rw [hγ0] at hs
  have hr : (2 * C.trace * (G x).det) / (2 * Real.sqrt (G x).det) =
      C.trace * Real.sqrt (G x).det := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hpos).ne')).mpr
    calc
      _ = 2 * C.trace * (Real.sqrt (G x).det) ^ 2 := by rw [Real.sq_sqrt hpos.le]
      _ = _ := by ring
  rw [hr] at hs
  have hρ := (heatMatrixDeterminant_contDiffAt 1 G x hG).sqrt hpos.ne'
  have hfρ : HasFDerivAt (fun y => Real.sqrt (G y).det)
      (fderiv ℝ (fun y => Real.sqrt (G y).det) x) (γ 0) := by
    rw [hγ0]
    exact hρ.differentiableAt one_ne_zero |>.hasFDerivAt
  have hρc := hfρ.comp_hasDerivAt 0 hγ
  exact hρc.unique hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Covariant pullback by a moving frame. The frame matrix and the
Jacobian of the base map are kept distinct. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_frameTensor_weighted_sum {n : ℕ} (E : Mat4)
    (c : Fin 4 → ℝ) (T : Fin 4 → CovariantCoordinates n) (a : Fin n → Fin 4) :
    frameTensor E (∑ r, c r • T r) a = ∑ r, c r * frameTensor E (T r) a := by
  have he : (∑ r, c r • T r) = (fun b => ∑ r, c r * T r b) := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he, frameTensor_sum]
  simp only [frameTensor_const_mul]

theorem heat_covariantDirection_pullback {n : ℕ}
    (F : FourSpace → FourSpace) (E : FourSpace → Mat4)
    (C D : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (z : FourSpace) (hF : DifferentiableAt ℝ F z)
    (hE : ∀ a b, DifferentiableAt ℝ (fun w => E w a b) z)
    (hT : ∀ a, DifferentiableAt ℝ (fun w => T w a) (F z)) (i : Fin 4)
    (hC : E z * C i z = matrixPartial E i z +
      (∑ r, jacobianMatrix F z r i • D r (F z)) * E z) :
    tensorCovariantDirection C (fun w => frameTensor (E w) (T (F w))) i z =
      frameTensor (E z) (∑ r, jacobianMatrix F z r i • tensorCovariantDirection D T r (F z)) := by
  have hcomp (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun w => T (F w) a) z := (hT a).comp z hF
  have hder := tensorPartial_frameTensor E (fun w => T (F w)) z hE hcomp i
  have hchain := tensorPartial_comp F T z hF hT i
  have hvar := frameVariation_connection (E z) (matrixPartial E i z)
    (∑ r, jacobianMatrix F z r i • D r (F z)) (C i z) hC (T (F z))
  have hslot : tensorSlotAction (∑ r, jacobianMatrix F z r i • D r (F z)) (T (F z)) =
      ∑ r, jacobianMatrix F z r i • tensorSlotAction (D r (F z)) (T (F z)) := by
    simp only [tensorSlotAction_sum_matrix, tensorSlotAction_smul_matrix]
  funext a
  have hv := congrFun hvar a
  change tensorPartial (fun w => frameTensor (E w) (T (F w))) i z a -
    tensorSlotAction (C i z) (frameTensor (E z) (T (F z))) a = _
  rw [hder, hchain]
  rw [hslot] at hv
  simp only [Pi.add_apply] at hv ⊢
  rw [heat_frameTensor_weighted_sum] at hv
  rw [heat_frameTensor_weighted_sum, heat_frameTensor_weighted_sum]
  simp only [tensorCovariantDirection, frameTensor_sub, mul_sub, Finset.sum_sub_distrib]
  linarith only [hv]

theorem heatFrame_baseJacobian (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : DifferentiableAt ℝ P x) (i r : Fin 4) :
    jacobianMatrix (fun y => (P y).1) x r i =
      (fderiv ℝ P x (coordinateVector i)).1 r := by
  have hp : HasFDerivAt P (fderiv ℝ P x) x := hP.hasFDerivAt
  have hf : HasFDerivAt (fun y => (P y).1)
      ((ContinuousLinearMap.fst ℝ FourSpace Mat4).comp (fderiv ℝ P x)) x := hp.fst
  have h := hf.fderiv
  have he := congrArg (fun L : FourSpace →L[ℝ] FourSpace => L (coordinateVector i) r) h
  simpa only [jacobianMatrix] using! he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The derivative-slot correction in the covariant Hessian trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem heat_connection_trace_expand (H Q : Mat4) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (S : Fin 4 → ℝ) :
    -(∑ p, ∑ q, H p q * Q p q) +
      (∑ r, (∑ p, ∑ q, H p q * Γ r p q) * S r) =
    -(∑ p, ∑ q, H p q * (Q p q - ∑ r, Γ r p q * S r)) := by
  have he : (∑ r, (∑ p, ∑ q, H p q * Γ r p q) * S r) =
      ∑ p, ∑ q, H p q * (∑ r, Γ r p q * S r) := by
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  rw [he]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framed_second_covariant {n : ℕ} (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates n) (E : Mat4) (x : FourSpace)
    (p q : Fin 4) (a : Fin n → Fin 4) :
    frameTensor E (fun v => covariantDerivative g c (covariantDerivative g c T) x
      (Fin.cons q (Fin.cons p v))) a =
      frameTensor E (tensorCovariantDirection (connectionMatrix g c)
        (tensorCovariantDirection (connectionMatrix g c) T p) q x) a -
      ∑ r, christoffel g c x r q p *
        frameTensor E (tensorCovariantDirection (connectionMatrix g c) T r x) a := by
  have he : (fun v => covariantDerivative g c (covariantDerivative g c T) x
      (Fin.cons q (Fin.cons p v))) =
      tensorCovariantDirection (connectionMatrix g c)
        (tensorCovariantDirection (connectionMatrix g c) T p) q x -
      (fun v => ∑ r, christoffel g c x r q p *
        tensorCovariantDirection (connectionMatrix g c) T r x v) := by
    funext v
    exact covariantDerivative_iterated_direction g c T x q p v
  rw [he, frameTensor_sub, frameTensor_sum]
  simp only [frameTensor_const_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! First-order product and germ rules used for the second covariant
derivative in normal coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_covariant_congr {n : ℕ} (C : Fin 4 → FourSpace → Mat4)
    (S T : FourSpace → CovariantCoordinates n) (x : FourSpace)
    (h : S =ᶠ[𝓝 x] T) (i : Fin 4) :
    tensorCovariantDirection C S i x = tensorCovariantDirection C T i x := by
  funext a
  have he : (fun y => S y a) =ᶠ[𝓝 x] (fun y => T y a) :=
    h.mono fun y hy => congrFun hy a
  have hd := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq
  change partialDeriv (fun y => S y a) i x = partialDeriv (fun y => T y a) i x at hd
  change partialDeriv (fun y => S y a) i x - tensorSlotAction (C i x) (S x) a = _
  rw [hd, h.self_of_nhds]
  rfl

theorem heat_covariant_weighted_sum {n : ℕ} (C : Fin 4 → FourSpace → Mat4)
    (f : Fin 4 → FourSpace → ℝ) (S : Fin 4 → FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hf : ∀ r, DifferentiableAt ℝ (f r) x)
    (hS : ∀ r a, DifferentiableAt ℝ (fun y => S r y a) x) (i : Fin 4) :
    tensorCovariantDirection C (fun y a => ∑ r, f r y * S r y a) i x =
      fun a => ∑ r, (partialDeriv (f r) i x * S r x a +
        f r x * tensorCovariantDirection C (S r) i x a) := by
  funext a
  have hd : partialDeriv (fun y => ∑ r, f r y * S r y a) i x =
      ∑ r, (partialDeriv (f r) i x * S r x a +
        f r x * partialDeriv (fun y => S r y a) i x) := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun r y => f r y * S r y a)
      (fun r _ => (hf r).mul (hS r a)), _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro r _
    simp only [fderiv_fun_mul (hf r) (hS r a), _root_.add_apply, _root_.smul_apply,
      smul_eq_mul]
    ring
  change partialDeriv (fun y => ∑ r, f r y * S r y a) i x -
    tensorSlotAction (C i x) (fun b => ∑ r, f r x * S r x b) a = _
  rw [hd, tensorSlotAction_sum]
  simp only [tensorSlotAction_const_mul, tensorCovariantDirection, Pi.sub_apply,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, tensorPartial]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Jacobian calculus needed for the finite-regularity normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatJacobian_entry_regular (n : ℕ) {F : FourSpace → FourSpace} {x : FourSpace}
    (hF : ContDiffAt ℝ (n + 1) F x) (r i : Fin 4) :
    ContDiffAt ℝ n (fun y => jacobianMatrix F y r i) x := by
  have hd : ContDiffAt ℝ n (fderiv ℝ F) x := hF.fderiv_right (by norm_cast)
  exact (EuclideanSpace.proj r : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt.comp x
    (hd.clm_apply (contDiffAt_const (c := coordinateVector i)))

theorem heatJacobian_partial {F : FourSpace → FourSpace} {x : FourSpace}
    (hF : ContDiffAt ℝ 2 F x) (r i j : Fin 4) :
    partialDeriv (fun y => jacobianMatrix F y r j) i x =
      fderiv ℝ (fderiv ℝ F) x (coordinateVector i) (coordinateVector j) r := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ F) x := hF.fderiv_right (by norm_num)
  have he := hd.differentiableAt one_ne_zero |>.hasFDerivAt
  have ha := he.clm_apply (hasFDerivAt_const (coordinateVector j) x)
  have hp := (EuclideanSpace.proj r : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp x ha
  have hh := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hp.fderiv
  simpa [partialDeriv, jacobianMatrix, Function.comp_def] using! hh

theorem heatJacobian_partials_commute {F : FourSpace → FourSpace} {x : FourSpace}
    (hF : ContDiffAt ℝ 2 F x) (r i j : Fin 4) :
    partialDeriv (fun y => jacobianMatrix F y r j) i x =
      partialDeriv (fun y => jacobianMatrix F y r i) j x := by
  rw [heatJacobian_partial hF, heatJacobian_partial hF]
  exact congrArg (fun v : FourSpace => v r)
    ((hF.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector i) (coordinateVector j))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame connection acts on actual covariant derivatives of
the original geometric tensor, with the differential of the base map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_covariant_pullback {n : ℕ} (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hP : DifferentiableAt ℝ P x)
    (hT : ∀ a, DifferentiableAt ℝ (fun z => T z a) (P x).1)
    (hG : (P x).2ᵀ * metricInChart g c (P x).1 * (P x).2 = 1) (i : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (T (P y).1)) i x =
    frameTensor (P x).2 (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      tensorCovariantDirection (connectionMatrix g c) T r (P x).1) := by
  have hE (a b : Fin 4) : DifferentiableAt ℝ (fun y => (P y).2 a b) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hP.snd a) b
  have hdet : IsUnit (P x).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hG
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hC : (P x).2 * heatNormalFrameConnection g c P i x =
      matrixPartial (fun y => (P y).2) i x +
        (∑ r : Fin 4, jacobianMatrix (fun y => (P y).1) x r i •
          connectionMatrix g c r (P x).1) * (P x).2 := by
    rw [heatFrame_matrixPartial P x hP i]
    simp_rw [heatFrame_baseJacobian P x hP]
    exact pulledConnection_equation _ _ _ hdet
  have h := heat_covariantDirection_pullback (fun y => (P y).1) (fun y => (P y).2)
    (heatNormalFrameConnection g c P) (connectionMatrix g c) T x hP.fst hE hT i hC
  simpa only [heatFrame_baseJacobian P x hP] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The twice-differentiated moving-frame pullback. The derivative of the
base Jacobian is retained explicitly, for cancellation against the drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_covariant_second_pullback {n : ℕ}
    (F : FourSpace → FourSpace) (E : FourSpace → Mat4)
    (C D : Fin 4 → FourSpace → Mat4) (T : FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hE : ∀ a b, DifferentiableAt ℝ (fun y => E y a b) x)
    (hS : ∀ r a, DifferentiableAt ℝ
      (fun y => tensorCovariantDirection D T r y a) (F x))
    (hC : ∀ j, E x * C j x = matrixPartial E j x +
      (∑ s, jacobianMatrix F x s j • D s (F x)) * E x)
    (hfirst : ∀ᶠ y in 𝓝 x, ∀ i,
      tensorCovariantDirection C (fun z => frameTensor (E z) (T (F z))) i y =
        frameTensor (E y) (∑ r, jacobianMatrix F y r i • tensorCovariantDirection D T r (F y)))
    (i j : Fin 4) :
    tensorCovariantDirection C
      (tensorCovariantDirection C (fun y => frameTensor (E y) (T (F y))) i) j x =
      fun a => ∑ r, (partialDeriv (fun y => jacobianMatrix F y r i) j x *
        frameTensor (E x) (tensorCovariantDirection D T r (F x)) a +
        jacobianMatrix F x r i * frameTensor (E x)
          (∑ s, jacobianMatrix F x s j • tensorCovariantDirection D
            (tensorCovariantDirection D T r) s (F x)) a) := by
  let S := fun r y => frameTensor (E y) (tensorCovariantDirection D T r (F y))
  have hFd := hF.differentiableAt (by norm_num)
  have he : tensorCovariantDirection C (fun y => frameTensor (E y) (T (F y))) i =ᶠ[𝓝 x]
      (fun y a => ∑ r, jacobianMatrix F y r i * S r y a) := by
    filter_upwards [hfirst] with y hy
    rw [hy i]
    funext a
    exact heat_frameTensor_weighted_sum (E y) (fun r => jacobianMatrix F y r i) _ a
  rw [heat_covariant_congr C _ _ x he j]
  have hdiff (r : Fin 4) (a : Fin n → Fin 4) :
      DifferentiableAt ℝ (fun y => S r y a) x :=
    frameTensor_differentiableAt E _ x hE (fun b => (hS r b).comp x hFd) a
  rw [heat_covariant_weighted_sum C _ S x
    (fun r => (heatJacobian_entry_regular 1 hF r i).differentiableAt one_ne_zero) hdiff j]
  funext a
  apply Finset.sum_congr rfl
  intro r _
  rw [heat_covariantDirection_pullback F E C D
    (tensorCovariantDirection D T r) x hFd hE (hS r) j (hC j)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Contraction of the two covariant derivative slots for actual one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def oneFormSecondTrace (G : Mat4) (T : CovariantCoordinates 3) : CovariantCoordinates 1 :=
  fun v => ∑ a, ∑ b, G a b * T (Fin.cons a (Fin.cons b v))

theorem oneFormSecondTrace_frame (E : Mat4) (T : CovariantCoordinates 3)
    (v : Fin 1 → Fin 4) :
    (∑ i, frameTensor E T (Fin.cons i (Fin.cons i v))) =
      frameTensor E (oneFormSecondTrace (E * Eᵀ) T) v := by
  simp only [frameTensor_cons]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ i, E a i * ∑ b, E b i * frameTensor E (fun w => T (Fin.cons a (Fin.cons b w))) v) =
        ∑ a, ∑ b, (∑ i, E a i * E b i) *
          frameTensor E (fun w => T (Fin.cons a (Fin.cons b w))) v := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      symm
      change frameTensor E (fun w => ∑ a, ∑ b, (E * Eᵀ) a b *
        T (Fin.cons a (Fin.cons b w))) v = _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [frameTensor_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [frameTensor_const_mul]
      rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framed_oneFormSecondTrace (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 1) (E H : Mat4) (x : FourSpace)
    (hH : Hᵀ = H) (a : Fin 1 → Fin 4) :
    frameTensor E (oneFormSecondTrace H (covariantDerivative g c
      (covariantDerivative g c T) x)) a =
      ∑ p, ∑ q, H p q * (frameTensor E
        (tensorCovariantDirection (connectionMatrix g c)
          (tensorCovariantDirection (connectionMatrix g c) T p) q x) a -
        ∑ r, christoffel g c x r p q *
          frameTensor E (tensorCovariantDirection (connectionMatrix g c) T r x) a) := by
  have hsym (p q : Fin 4) : H q p = H p q := congrArg (fun A : Mat4 => A p q) hH
  unfold oneFormSecondTrace
  rw [frameTensor_sum]
  simp_rw [frameTensor_sum, frameTensor_const_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hsym, heat_framed_second_covariant]
  have hc (r : Fin 4) : christoffel g c x r q p = christoffel g c x r p q :=
    christoffel_comm g c x r q p
  simp only [hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame curvature and potential are the intrinsic geometric
ones, evaluated on actual orthonormal frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T2Space M] [CompactSpace M]

def HeatNormalFrameData.frame {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) : FrameBundle g :=
  chartFrameStateToBundle g c ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Second covariant differentiation in the constructed normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_covariant_second_pullback {n : ℕ} (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates n)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hT : ∀ z ∈ (chartAt FourSpace c).target, ∀ a,
      ContDiffAt ℝ ∞ (fun y => T y a) z)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i j : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x =
      fun a => ∑ r, (partialDeriv
        (fun y => jacobianMatrix (fun z => (P z).1) y r i) j x *
        frameTensor (P x).2 (tensorCovariantDirection (connectionMatrix g c) T r (P x).1) a +
        jacobianMatrix (fun y => (P y).1) x r i * frameTensor (P x).2
          (∑ s, jacobianMatrix (fun y => (P y).1) x s j •
            tensorCovariantDirection (connectionMatrix g c)
              (tensorCovariantDirection (connectionMatrix g c) T r) s (P x).1) a) := by
  have hPd := hP.differentiableAt (by norm_num)
  have hE (a b : Fin 4) : DifferentiableAt ℝ (fun y => (P y).2 a b) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hPd.snd a) b
  have hS (r : Fin 4) (a : Fin n → Fin 4) : DifferentiableAt ℝ
      (fun y => tensorCovariantDirection (connectionMatrix g c) T r y a) (P x).1 :=
    (covariantDerivative_contDiffAt g c (P x).1 hx
      (metricInChart_posDef g c (P x).1 hx).det_pos.ne' T (hT _ hx)
      (Fin.cons r a)).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hdet : IsUnit (P x).2.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hG.self_of_nhds
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hC (k : Fin 4) : (P x).2 * heatNormalFrameConnection g c P k x =
      matrixPartial (fun y => (P y).2) k x +
      (∑ s, jacobianMatrix (fun y => (P y).1) x s k • connectionMatrix g c s (P x).1) *
        (P x).2 := by
    rw [heatFrame_matrixPartial P x hPd k]
    simp_rw [heatFrame_baseJacobian P x hPd]
    exact pulledConnection_equation _ _ _ hdet
  have hnear : ∀ᶠ y in 𝓝 x, ∀ k,
      tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun z => frameTensor (P z).2 (T (P z).1)) k y =
      frameTensor (P y).2 (∑ r, jacobianMatrix (fun z => (P z).1) y r k •
        tensorCovariantDirection (connectionMatrix g c) T r (P y).1) := by
    have hp : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 P y :=
      (hP.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).eventually (by norm_num)
    have ht : ∀ᶠ y in 𝓝 x, (P y).1 ∈ (chartAt FourSpace c).target :=
      hP.continuousAt.fst.preimage_mem_nhds ((chartAt FourSpace c).open_target.mem_nhds hx)
    filter_upwards [hp, ht, hG] with y hy hyt hyg
    intro k
    have hd := hy.differentiableAt one_ne_zero
    have h := heatNormal_covariant_pullback g c P T y hd
      (fun a => (hT _ hyt a).differentiableAt (by simp)) hyg k
    simpa only [heatFrame_baseJacobian P y hd] using h
  exact heat_covariant_second_pullback (fun y => (P y).1) (fun y => (P y).2)
    (heatNormalFrameConnection g c P) (connectionMatrix g c) T x hP.fst hE hS hC hnear i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame rough operator is the actual metric trace of the
covariant Hessian once the proved metric and drift transport laws apply. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_oneForm_rough_pullback (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates 1)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hT : ∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (A : Mat4) (b : Fin 4 → ℝ)
    (hA : jacobianMatrix (fun y => (P y).1) x * A *
      (jacobianMatrix (fun y => (P y).1) x)ᵀ = (metricInChart g c (P x).1)⁻¹)
    (hb : ∀ r, (∑ i, jacobianMatrix (fun y => (P y).1) x r i * b i) -
      (∑ i, ∑ j, A i j * partialDeriv
        (fun y => jacobianMatrix (fun z => (P z).1) y r j) i x) =
      ∑ p, ∑ q, (metricInChart g c (P x).1)⁻¹ p q * christoffel g c (P x).1 r p q)
    (v : Fin 1 → Fin 4) :
    -(∑ i, ∑ j, A i j * tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v) +
      (∑ i, b i * tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i x v) =
    -frameTensor (P x).2 (oneFormSecondTrace (metricInChart g c (P x).1)⁻¹
      (covariantDerivative g c (covariantDerivative g c T) (P x).1)) v := by
  let J := jacobianMatrix (fun y => (P y).1)
  let H := (metricInChart g c (P x).1)⁻¹
  let S := fun r => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c) T r (P x).1) v
  let Q : Mat4 := Matrix.of fun r s => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c)
      (tensorCovariantDirection (connectionMatrix g c) T r) s (P x).1) v
  have hPd := hP.differentiableAt (by norm_num)
  have hf (i : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (T (P y).1)) i x v = ∑ r, J x r i * S r := by
    have h := heatNormal_covariant_pullback g c P T x hPd
      (fun a => (hT _ hx a).differentiableAt (by simp)) hG.self_of_nhds i
    rw [h]
    simp_rw [← heatFrame_baseJacobian P x hPd]
    exact heat_frameTensor_weighted_sum _ _ _ v
  have hs (i j : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v =
      (∑ r, partialDeriv (fun y => J y r i) j x * S r) +
        ∑ r, ∑ s, J x r i * J x s j * Q r s := by
    rw [heatNormal_covariant_second_pullback g c P T x hP hT hx hG i j]
    simp only [heat_frameTensor_weighted_sum, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    change J x r i * (J x s j * Q r s) = _
    ring
  simp_rw [hf, hs]
  have h := heat_rough_trace_algebra (J x) A H Q
    (fun i => matrixPartial J i x) b S
    (fun r => ∑ p, ∑ q, H p q * christoffel g c (P x).1 r p q) hA
    (fun i j r => heatJacobian_partials_commute hP.fst r j i) hb
  simp only [matrixPartial] at h
  rw [h, heat_connection_trace_expand]
  have hH : Hᵀ = H := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    ext i j
    exact metricInChart_comm g c (P x).1 j i
  rw [heat_framed_oneFormSecondTrace g c T (P x).2 H (P x).1 hH v]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous intrinsic Jacobian density for the actual exponential.
Its expression in any output chart is the metric density times the
absolute coordinate determinant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_chart_backward (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (d : M) (v w : FourSpace)
    (hd : frameExponential g o e v ∈ (chartAt FourSpace d).source) :
    chartBackwardOperator d (chartAt FourSpace d (frameExponential g o e v))
      (fderiv ℝ (fun z => chartAt FourSpace d (frameExponential g o e z)) v w) =
        mfderiv I4 I4 (frameExponential g o e) v w := by
  have h := mfderiv_comp v
    ((mdifferentiable_chart (I := I4) d).mdifferentiableAt hd)
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero v)
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ (fun z => chartAt FourSpace d (frameExponential g o e z)) v =
    (chartForwardOperator d (frameExponential g o e v)).comp
      (mfderiv I4 I4 (frameExponential g o e) v) at h
  rw [h]
  have hb := congrArg (fun L : FourSpace →L[ℝ] FourSpace =>
    L (mfderiv I4 I4 (frameExponential g o e) v w))
      (chartBackward_forward d (frameExponential g o e v) hd)
  exact hb

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

/-! The density divergence coefficient is the contracted torsion-free
metric connection, with no coordinate or curvature assumption. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section

theorem heatCompatibleDrift_algebra (H : Mat4) (C : Fin 4 → Mat4) (ρ : ℝ)
    (hρ : ρ ≠ 0) (hC : ∀ i j r, C i r j = C j r i) (j : Fin 4) :
    -((∑ i, (-(∑ k, C i i k * H k j) - ∑ k, H i k * C i j k)) +
      ρ⁻¹ * ∑ i, H i j * ((C i).trace * ρ)) =
      ∑ i, ∑ k, H i k * C i j k := by
  have ht : (∑ i, H i j * (C i).trace) = ∑ i, ∑ k, C i i k * H k j := by
    simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hC k i i]
    ring
  have hp : ρ⁻¹ * (∑ i, H i j * ((C i).trace * ρ)) =
      ∑ i, ∑ k, C i i k * H k j := by
    calc
      _ = ρ⁻¹ * ((∑ i, H i j * (C i).trace) * ρ) := by
        simp only [Finset.sum_mul, mul_assoc]
      _ = ∑ i, H i j * (C i).trace := by field_simp
      _ = _ := ht
  rw [hp]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

theorem heatCompatibleMetric_drift (G : FourSpace → Mat4) (x : FourSpace)
    (hG : ∀ p q, ContDiffAt ℝ 1 (fun y => G y p q) x)
    (hpos : 0 < (G x).det) (C : Fin 4 → Mat4)
    (hcompat : ∀ i, matrixPartial G i x = (C i)ᵀ * G x + G x * C i)
    (htorsion : ∀ i j r, C i r j = C j r i) (j : Fin 4) :
    fourHeatDensityDrift (fun y => (G y)⁻¹) (fun y => Real.sqrt (G y).det) x j =
      ∑ i, ∑ k, (G x)⁻¹ i k * C i j k := by
  have hInv (i : Fin 4) : partialDeriv (fun y => (G y)⁻¹ i j) i x =
      -(∑ k, C i i k * (G x)⁻¹ k j) - ∑ k, (G x)⁻¹ i k * C i j k := by
    have h := congrArg (fun A : Mat4 => A i j)
      (heatCompatibleMetric_inverse G x hG hpos.ne' (C i) i (hcompat i))
    simpa only [matrixPartial, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.mul_apply, Matrix.transpose_apply] using h
  have hρ (i : Fin 4) := heatCompatibleMetric_density G x hG hpos (C i) i (hcompat i)
  simp only [fourHeatDensityDrift, hInv, hρ]
  exact heatCompatibleDrift_algebra _ C _ (Real.sqrt_pos.mpr hpos).ne' htorsion j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Regularity of the actual normal metric, volume density and leading heat
amplitude. All are derived from the exponential and the smooth metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalMetric_chart_pairing (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (c : M) (v : FourSpace)
    (hv : frameExponential g o e v ∈ (chartAt FourSpace c).source) (i j : Fin 4) :
    heatNormalMetric g o e v i j =
      WithLp.ofLp (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v
        (coordinateVector i)) ⬝ᵥ
      (metricInChart g c (chartAt FourSpace c (frameExponential g o e v)) *ᵥ
        WithLp.ofLp (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v
          (coordinateVector j))) := by
  have h := metricInChart_pairing g c
    (chartAt FourSpace c (frameExponential g o e v))
    (WithLp.ofLp (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v
      (coordinateVector i)))
    (WithLp.ofLp (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v
      (coordinateVector j)))
  simp only [WithLp.toLp_ofLp] at h
  change _ = g.inner ((chartAt FourSpace c).symm
      (chartAt FourSpace c (frameExponential g o e v)))
    (chartBackwardOperator c (chartAt FourSpace c (frameExponential g o e v))
      (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v
        (coordinateVector i)))
    (chartBackwardOperator c (chartAt FourSpace c (frameExponential g o e v))
      (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v
        (coordinateVector j))) at h
  rw [frameExponential_chart_backward g o e c v (coordinateVector i) hv,
    frameExponential_chart_backward g o e c v (coordinateVector j) hv,
    (chartAt FourSpace c).left_inv hv] at h
  exact h.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual pulled-back metric and torsion-free coordinate connection.
Only two derivatives of the base map are needed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatPullbackMetric (g : SmoothMetric M) (c : M) (F : FourSpace → FourSpace)
    (x : FourSpace) : Mat4 :=
  (jacobianMatrix F x)ᵀ * metricInChart g c (F x) * jacobianMatrix F x

def heatPullbackConnection (g : SmoothMetric M) (c : M) (F : FourSpace → FourSpace)
    (i : Fin 4) (x : FourSpace) : Mat4 :=
  pulledConnection (jacobianMatrix F x) (matrixPartial (jacobianMatrix F) i x)
    (weightedConnection (jacobianMatrix F x) (fun r => connectionMatrix g c r (F x)) i)

theorem heatPullbackConnection_torsion (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (i j r : Fin 4) :
    heatPullbackConnection g c F i x r j = heatPullbackConnection g c F j x r i := by
  unfold heatPullbackConnection
  apply pulledConnection_torsion (jacobianMatrix F x)
    (fun k => matrixPartial (jacobianMatrix F) k x)
    (fun k => connectionMatrix g c k (F x))
  · intro a b k
    exact heatJacobian_partials_commute hF k a b
  · intro a b k
    exact christoffel_comm g c (F x) k a b

theorem heatPullbackMetric_regular (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ∈ (chartAt FourSpace c).target) (i j : Fin 4) :
    ContDiffAt ℝ 1 (fun y => heatPullbackMetric g c F y i j) x := by
  simp only [heatPullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro r _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro s _
    exact (heatJacobian_entry_regular 1 hF s i).mul
      (((metricInChart_contDiffAt g c (F x) hx s r).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp x
        (hF.of_le (by norm_num)))
  · exact heatJacobian_entry_regular 1 hF r j

theorem heatPullbackConnection_compatible (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ∈ (chartAt FourSpace c).target)
    (hJ : IsUnit (jacobianMatrix F x).det) (i : Fin 4) :
    matrixPartial (heatPullbackMetric g c F) i x =
      (heatPullbackConnection g c F i x)ᵀ * heatPullbackMetric g c F x +
        heatPullbackMetric g c F x * heatPullbackConnection g c F i x := by
  let J := jacobianMatrix F
  let H := fun y => metricInChart g c (F y)
  have hdF := hF.differentiableAt (by norm_num)
  have hdJ (r s : Fin 4) : DifferentiableAt ℝ (fun y => J y r s) x :=
    (heatJacobian_entry_regular 1 hF r s).differentiableAt one_ne_zero
  have hdH (r s : Fin 4) : DifferentiableAt ℝ (fun y => H y r s) x :=
    ((metricInChart_contDiffAt g c (F x) hx r s).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp x hdF
  have hrate : matrixPartial H i x =
      (weightedConnection (J x) (fun r => connectionMatrix g c r (F x)) i)ᵀ * H x +
        H x * weightedConnection (J x) (fun r => connectionMatrix g c r (F x)) i := by
    rw [matrixPartial_comp hdF (fun r s =>
      (metricInChart_contDiffAt g c (F x) hx r s).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
    exact parallelFrame_metric_rate g c (F x) hx (fun r => J x r i)
  have hcongr : heatPullbackMetric g c F = fun y => (J y)ᵀ * (H y * J y) := by
    funext y
    exact Matrix.mul_assoc _ _ _
  rw [hcongr, matrixPartial_congruence J H x hdJ hdH i, hrate]
  simpa only [heatPullbackConnection, J, H, Matrix.mul_assoc] using
    (pulledConnection_metric_compatibility (H x) (J x)
    (matrixPartial J i x)
    (weightedConnection (J x) (fun r => connectionMatrix g c r (F x)) i) hJ).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport of the actual normal metric and its inverse by the base
Jacobian of the constructed frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_matrix_congruence_pairing (H J : Mat4) (i j : Fin 4) :
    (Jᵀ * H * J) i j = (fun r => J r i) ⬝ᵥ (H *ᵥ fun r => J r j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem heat_matrix_inverse_congruence (H J : Mat4) (hJ : IsUnit J.det) :
    J * (Jᵀ * H * J)⁻¹ * Jᵀ = H⁻¹ := by
  have hJt : IsUnit Jᵀ.det := by simpa only [Matrix.det_transpose] using hJ
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = (J * J⁻¹) * H⁻¹ * (Jᵀ⁻¹ * Jᵀ) := by simp only [Matrix.mul_assoc]
    _ = H⁻¹ := by rw [Matrix.mul_nonsing_inv J hJ, Matrix.nonsing_inv_mul Jᵀ hJt]; simp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.metric_pullback {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source) :
    heatNormalMetric g o e x =
      (jacobianMatrix (fun y => (D.point y).1) x)ᵀ *
        metricInChart g c (D.point x).1 * jacobianMatrix (fun y => (D.point y).1) x := by
  have hF : (fun y => (D.point y).1) =ᶠ[𝓝 x]
      (fun y => chartAt FourSpace c (frameExponential g o e y)) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.exponential y hy
  have hd : fderiv ℝ (fun y => (D.point y).1) x =
      fderiv ℝ (fun y => chartAt FourSpace c (frameExponential g o e y)) x := hF.fderiv_eq
  ext i j
  rw [heat_matrix_congruence_pairing]
  have h := heatNormalMetric_chart_pairing g o e c x hs i j
  rw [← hd, ← D.exponential x hx] at h
  exact h

theorem HeatNormalFrameData.inverseMetric_transport {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hg : (heatNormalMetric g o e x).det ≠ 0) :
    jacobianMatrix (fun y => (D.point y).1) x * (heatNormalMetric g o e x)⁻¹ *
      (jacobianMatrix (fun y => (D.point y).1) x)ᵀ = (metricInChart g c (D.point x).1)⁻¹ := by
  have hG := D.metric_pullback x hx hs
  have hJ : IsUnit (jacobianMatrix (fun y => (D.point y).1) x).det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply hg
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hz]
    ring
  rw [hG]
  exact heat_matrix_inverse_congruence _ _ hJ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact coordinate transformation of the density drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatPullbackMetric_jacobian_unit (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace)
    (hdet : (heatPullbackMetric g c F x).det ≠ 0) :
    IsUnit (jacobianMatrix F x).det := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply hdet
  simp only [heatPullbackMetric, Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, mul_zero]

theorem heatPullback_drift (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ∈ (chartAt FourSpace c).target)
    (hpos : 0 < (heatPullbackMetric g c F x).det) (r : Fin 4) :
    fourHeatDensityDrift (fun y => (heatPullbackMetric g c F y)⁻¹)
      (fun y => Real.sqrt (heatPullbackMetric g c F y).det) x r =
      ∑ i, ∑ j, (heatPullbackMetric g c F x)⁻¹ i j * heatPullbackConnection g c F i x r j := by
  exact heatCompatibleMetric_drift _ x (heatPullbackMetric_regular g c F x hF hx)
    hpos (fun i => heatPullbackConnection g c F i x)
    (heatPullbackConnection_compatible g c F x hF hx
      (heatPullbackMetric_jacobian_unit g c F x hpos.ne'))
    (heatPullbackConnection_torsion g c F x hF) r

theorem heatPullback_drift_transport (g : SmoothMetric M) (c : M)
    (F : FourSpace → FourSpace) (x : FourSpace) (hF : ContDiffAt ℝ 2 F x)
    (hx : F x ∈ (chartAt FourSpace c).target)
    (hpos : 0 < (heatPullbackMetric g c F x).det) (r : Fin 4) :
    (∑ k, jacobianMatrix F x r k * fourHeatDensityDrift
      (fun y => (heatPullbackMetric g c F y)⁻¹)
      (fun y => Real.sqrt (heatPullbackMetric g c F y).det) x k) -
      (∑ i, ∑ j, (heatPullbackMetric g c F x)⁻¹ i j *
        partialDeriv (fun y => jacobianMatrix F y r j) i x) =
      ∑ p, ∑ q, (metricInChart g c (F x))⁻¹ p q * christoffel g c (F x) r p q := by
  simp_rw [heatPullback_drift g c F x hF hx hpos]
  have hJ := heatPullbackMetric_jacobian_unit g c F x hpos.ne'
  exact heat_drift_transport_algebra (jacobianMatrix F x)
    (heatPullbackMetric g c F x)⁻¹ (metricInChart g c (F x))⁻¹
    (fun i => heatPullbackConnection g c F i x)
    (fun i => matrixPartial (jacobianMatrix F) i x)
    (fun i => connectionMatrix g c i (F x))
    (fun i => pulledConnection_equation _ _ _ hJ)
    (heat_matrix_inverse_congruence _ _ hJ) r

end
end PositiveEinsteinFour.Geometry
end


section

/-! The drift used by the actual normal parametrix has the geometric
coordinate transformation law on a proved neighborhood of its center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatDensityDrift_congr (a A : FourSpace → Mat4) (ρ R : FourSpace → ℝ)
    (x : FourSpace) (ha : a =ᶠ[𝓝 x] A) (hρ : ρ =ᶠ[𝓝 x] R) (i : Fin 4) :
    fourHeatDensityDrift a ρ x i = fourHeatDensityDrift A R x i := by
  have hd (j : Fin 4) : partialDeriv (fun y => a y j i) j x =
      partialDeriv (fun y => A y j i) j x := by
    have he : (fun y => a y j i) =ᶠ[𝓝 x] (fun y => A y j i) :=
      ha.mono (fun y hy => congrArg (fun T : Mat4 => T j i) hy)
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector j))
      he.fderiv_eq
  have hρd (j : Fin 4) : partialDeriv ρ j x = partialDeriv R j x :=
    congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector j)) hρ.fderiv_eq
  simp only [fourHeatDensityDrift, ha.self_of_nhds, hρ.self_of_nhds, hd, hρd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pointwise drift transport wherever the actual normal frame is regular
and the actual exponential remains in its coordinate chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.metric_pullback_germ (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source) :
    heatNormalMetric g o e =ᶠ[𝓝 x] heatPullbackMetric g c (fun y => (D.point y).1) := by
  have hsource : ∀ᶠ y in 𝓝 x, frameExponential g o e y ∈ (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hs)
  filter_upwards [isOpen_ball.mem_nhds hx, hsource] with y hy hsy
  exact D.metric_pullback y hy hsy

theorem HeatNormalFrameData.drift_transport_at (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hdet : 0 < (heatNormalMetric g o e x).det) (r : Fin 4) :
    (∑ k, jacobianMatrix (fun y => (D.point y).1) x r k * heatNormalDrift g o e x k) -
      (∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        partialDeriv (fun y => jacobianMatrix (fun z => (D.point z).1) y r j) i x) =
      ∑ p, ∑ q, (metricInChart g c (D.point x).1)⁻¹ p q *
        christoffel g c (D.point x).1 r p q := by
  let F := fun y => (D.point y).1
  have hG := D.metric_pullback_germ x hx hs
  have hd (k : Fin 4) : heatNormalDrift g o e x k =
      fourHeatDensityDrift (fun y => (heatPullbackMetric g c F y)⁻¹)
        (fun y => Real.sqrt (heatPullbackMetric g c F y).det) x k := by
    apply fourHeatDensityDrift_congr
    · exact hG.mono fun y hy => congrArg Inv.inv hy
    · exact hG.mono fun y hy => congrArg (fun G : Mat4 => Real.sqrt G.det) hy
  simp_rw [hd, hG.self_of_nhds]
  exact heatPullback_drift_transport g c F x hP.fst (D.in_chart x hx)
    (by simpa only [hG.self_of_nhds] using hdet) r

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the coordinate Hessian contraction with the
actual framed rough trace of a smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_orthonormal_inverse (H E : Mat4) (hE : Eᵀ * H * E = 1) :
    E * Eᵀ = H⁻¹ := by
  have hu : IsUnit E.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have h := congrArg Matrix.det hE
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
    norm_num at h
  have h := heat_matrix_inverse_congruence H E hu
  simpa only [hE, inv_one, mul_one] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate product rule for two successive covariant derivatives
of four-component fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatOneCovariantDerivative (A : Fin 4 → FourSpace → Mat4)
    (u : FourSpace → Fin 4 → ℝ) (i : Fin 4) (x : FourSpace) (k : Fin 4) : ℝ :=
  partialDeriv (fun y => u y k) i x + ∑ l : Fin 4, A i x k l * u x l

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The exterior derivative of an actual smooth one-form is closed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem tensorSlotAction_one (A : Mat4) (T : CovariantCoordinates 1) (k : Fin 4) :
    tensorSlotAction A T ![k] = ∑ p, A p k * T ![p] := by
  have hup (p : Fin 4) : Function.update ![k] (0 : Fin 1) p = ![p] := by
    ext i
    fin_cases i
    simp
  simp only [tensorSlotAction, Fin.sum_univ_one, covariantSlotAction,
    Matrix.cons_val_zero, hup]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual one-form components and the Levi-Civita derivative in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatOneForm_covariant_skew (A : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates 1) (x : FourSpace) (i k : Fin 4)
    (hA : (A i x)ᵀ = -A i x) :
    tensorCovariantDirection A T i x ![k] =
      partialDeriv (fun y => T y ![k]) i x + ∑ l, A i x k l * T x ![l] := by
  have hs (l : Fin 4) : A i x l k = -A i x k l :=
    congrArg (fun B : Mat4 => B k l) hA
  change partialDeriv (fun y => T y ![k]) i x - tensorSlotAction (A i x) (T x) ![k] = _
  rw [tensorSlotAction_one]
  simp_rw [hs, neg_mul, Finset.sum_neg_distrib]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def heatNormalOneFormValue (c : M) (P : FourSpace → CoordinateFrameSpace)
    (u : smoothCovariantFields M 1) (x : FourSpace) (k : Fin 4) : ℝ :=
  frameTensor (P x).2 (covariantFieldCoordinates u.val c (P x).1) ![k]

end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second covariant derivatives in the actual four-component frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem heat_oneForm_covariant_component (A : Fin 4 → FourSpace → Mat4)
    (T : FourSpace → CovariantCoordinates 1) (x : FourSpace) (i k : Fin 4)
    (hA : (A i x)ᵀ = -A i x) :
    tensorCovariantDirection A T i x ![k] =
      fourHeatOneCovariantDerivative A (fun y l => T y ![l]) i x k :=
  heatOneForm_covariant_skew A T x i k hA

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-coordinate rough contraction agrees with the actual one-form Hessian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_covariantField_chart {n : ℕ} (g : SmoothMetric M)
    (T : M → CovariantCoordinates n) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    covariantFieldFramed g T e = frameTensor (frameChartMatrix g c e)
      (covariantFieldCoordinates T c (chartAt FourSpace c e.base)) := by
  have hb := mem_chart_source FourSpace e.base
  have ht := covariantFieldCoordinates_transition T e.base c
    (chartAt FourSpace e.base e.base) ((chartAt FourSpace e.base).map_source hb)
    (by simpa only [(chartAt FourSpace e.base).left_inv hb] using he)
  have hz : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    change chartAt FourSpace c ((chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base e.base)) = _
    rw [(chartAt FourSpace e.base).left_inv hb]
  rw [hz] at ht
  rw [frameChartMatrix_eq, frameTensor_mul, ← ht]
  rfl

variable {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneFormSecond_coordinates (u : smoothCovariantFields M 1) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    covariantFieldCoordinates (covariantFieldDerivative g (covariantFieldDerivative g u.val)) c z =
      covariantDerivative g c (covariantDerivative g c (covariantFieldCoordinates u.val c)) z := by
  rw [covariantFieldDerivative_coordinates u.property.derivative c z hz]
  apply covariantDerivative_congr
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact covariantFieldDerivative_coordinates u.property c w hw

variable [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.oneRoughTrace_as_actual {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (u : smoothCovariantFields M 1)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (k : Fin 4) :
    (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
      (D.frame x hx) ![i,i,k]) =
      frameTensor (D.point x).2 (oneFormSecondTrace (metricInChart g c (D.point x).1)⁻¹
        (covariantDerivative g c (covariantDerivative g c (covariantFieldCoordinates u.val c))
          (D.point x).1)) ![k] := by
  have hsource : (D.frame x hx).base ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target (D.in_chart x hx)
  have h := heat_covariantField_chart g
    (covariantFieldDerivative g (covariantFieldDerivative g u.val)) c (D.frame x hx) hsource
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hm, hb, oneFormSecond_coordinates u c _ (D.in_chart x hx)] at h
  simp_rw [h]
  have hi (i : Fin 4) : ![i,i,k] = Fin.cons i (Fin.cons i ![k]) := by
    ext j
    fin_cases j <;> rfl
  simp_rw [hi]
  rw [oneFormSecondTrace_frame, heat_orthonormal_inverse _ _ (D.orthonormal x hx)]

theorem HeatNormalFrameData.oneTensor_rough_at {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det)
    (u : smoothCovariantFields M 1) (k : Fin 4) :
    -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (covariantFieldCoordinates u.val c (D.point y).1)) i)
        j x ![k]) +
      (∑ i, heatNormalDrift g o e x i *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (covariantFieldCoordinates u.val c (D.point y).1)) i x ![k]) =
      -(∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (D.frame x hx) ![i,i,k]) := by
  have hgx : ∀ᶠ y in 𝓝 x,
      (D.point y).2ᵀ * metricInChart g c (D.point y).1 * (D.point y).2 = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.orthonormal y hy
  rw [D.oneRoughTrace_as_actual u x hx k]
  exact heatNormal_oneForm_rough_pullback g c D.point (covariantFieldCoordinates u.val c)
    x hP (fun z hz => u.property c z hz) (D.in_chart x hx) hgx
    (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
    (D.inverseMetric_transport x hx hs hd.ne') (D.drift_transport_at x hx hP hs hd) ![k]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


