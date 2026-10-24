-- Prove2me | Definitions.Def_OAIQWPH001
-- name    : OAIQWPH001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:04:16.841459+00:00
-- url     : https://prove2.me/theorems/dc153cdc-354d-45a8-92e8-8e5bc6b63585
-- title:
--   OpenAI pinched Kähler split: definitions bundle 2 of 2
-- statement:
--   The main definitions bundle of the split of OpenAI's proof of the negatively pinched Kähler threefold without bounded holomorphic coordinates (`OAI.PinchedHartogs.main_theorem`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/Kahler` (OpenAI, *A negatively pinched Kähler threefold without bounded holomorphic coordinates*, OpenAI Math Release, September 25, 2026, result family 359, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them:
--   - the sphere, peaks and logarithmic tests of Sections 3 and 5 (`Sphere`, `projectiveDistance`, `ProjectivelySeparated`, `peakPolynomial`, `regularizedLog`, `logarithmicTest`, `basePotential`);
--   - the radial profiles, densities and their stage conditions of Section 4 (`RadialProfiles`, `density`, `densityCorrection`, `DensityStage`, `PhaseBandwidth`, `OrbitMeanOne`, `densityMeasure`, `Represents`, `sigma`) and the test system of the construction (`TestSystem`);
--   - the gauge normalization, normalized potentials, curvature model and error tensors of Sections 8–9 (`baseGaugePolynomial`, `normalLogWeight`, `normalPotential`, `barrierX`, `barrierQ`, `horizontalMetric`, `curvatureModel`, `normalCurvature`, `normalError`, `horizontalPart`, `componentNorm`, `liftedThird`, `liftedFourth`) and the thresholds (`metricErrorConstant`, `metricThreshold`, `pinchingThreshold`).
--
--   It also contains the 39 lemmas and 10 instances those definitions use in their bodies; none of them is a named result of the paper. The definitions of the published statement (`Base`, `Ambient`, `ball`, `hartogs`, `hartogsMetric`, `ChartControl`, `ChartJets`, `ControlledPotential`, `MainTheorem` and the curvature notions) come from the published bundle `Def_PinchedKahler`, which this bundle imports; it imports no statement.
--
--   Modules: `BaseAdaptedHopf.lean`, `BaseAnisotropic.lean`, `BaseCentralComparison.lean`, `BaseChartJets.lean`, `BaseChartLow.lean`, `BaseCorrectionEstimate.lean`, `BaseCorrectionMoments.lean`, `BaseDensityBandwidth.lean`, `BaseDensityDefinitions.lean`, `BaseDensityFourier.lean`, `BaseDensityInduction.lean`, `BaseDensityMeasure.lean`, `BaseDensityPatchEstimates.lean`, `BaseDensityStepSupport.lean`, `BaseGaussian.lean`, `BaseHessianJet.lean`, `BaseHopf.lean`, `BaseHorizontalArc.lean`, `BaseHorizontalGeometry.lean`, `BaseJetNorms.lean`, `BaseLogApproximation.lean`, `BaseLogFactor.lean`, `BaseLogTests.lean`, `BaseMeans.lean`, `BaseModelParameters.lean`, `BaseModelSign.lean`, `BasePacking.lean`, `BasePatchDecomposition.lean`, `BasePatches.lean`, `BasePatchModel.lean`, `BasePhaseAveraging.lean`, `BasePhaseFourier.lean`, `BasePhaseSupport.lean`, `BasePolynomialChange.lean`, `BaseProfiles.lean`, `BaseProjective.lean`, `BaseRadialLaw.lean`, `BaseRadialMeasure.lean`, `BaseRadialMoments.lean`, `BaseRadialPatch.lean`, `BaseRadii.lean`, `BaseSphere.lean`, `BaseTestSystem.lean`, `BaseWeightedDerivative.lean`, `Definitions.lean`, `HartogsCharts.lean`, `HartogsCompletenessSupport.lean`, `HartogsCurvature.lean`, `HartogsFrame.lean`, `HartogsGauge.lean`, `HartogsJetLinearity.lean`, `HartogsJets.lean`, `HartogsLiftedJets.lean`, `HartogsModelBridge.lean`, `HartogsNormalBlocks.lean`, `HartogsNormalJets.lean`, `HartogsNormalTables.lean`, `HartogsTopologySupport.lean`, `HartogsTransferTools.lean`, `MetricCalculus.lean`, `Obstruction.lean`, `PinchingCompact.lean`.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Sections 3–9; Apache License 2.0); definitions carved from lean/OAI/Geometry/Kahler at commit adc7f12

import Mathlib
import Definitions.Def_PinchedKahler

section
-- module Solutions.OAIQW_PinchedHartogs.Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace PinchedHartogs

def BoundedHolomorphic (F : Ambient → Target) (φ : Base → ℝ) : Prop :=
  AnalyticOnNhd ℂ F (hartogs φ) ∧ ∃ B : ℝ, ∀ p ∈ hartogs φ, ∀ i, ‖F p i‖ ≤ B

def MapObstruction : Prop :=
  ∀ φ : Base → ℝ, ContDiffOn ℝ ∞ φ ball → noMinorant φ →
    ∀ F : Ambient → Target, BoundedHolomorphic F φ →
      ¬ ∀ p ∈ hartogs φ, (jacobian F p).det ≠ 0

open scoped Matrix.Norms.Elementwise

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler69_1

open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace PinchedHartogs

lemma ball_eq : ball = Metric.ball (0 : Base) 1 := by
  ext z
  simp [ball, Metric.mem_ball, dist_zero_right]

lemma isOpen_ball : IsOpen ball := by
  rw [ball_eq]
  exact Metric.isOpen_ball

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.MetricCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler1607_1 uKahler1618_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

namespace PinchedHartogs

open scoped Matrix.Norms.Elementwise

lemma dz_congr {f g : Ambient → ℂ} {p : Ambient} (h : f =ᶠ[𝓝 p] g) (i : Fin 3) :
    dz f p i = dz g p i := by
  simp only [dz, h.fderiv_eq]

lemma fderiv_real_cast {f : Ambient → ℝ} {p : Ambient} (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun q => (f q : ℂ)) p = Complex.ofRealCLM.comp (fderiv ℝ f p) := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp p hf.hasFDerivAt).fderiv

lemma dbar_eq_star_dz_real {f : Ambient → ℝ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (i : Fin 3) :
    dbar (fun q => (f q : ℂ)) p i = star (dz (fun q => (f q : ℂ)) p i) := by
  simp [dbar, dz, fderiv_real_cast hf]

lemma _root_.OAI.ContDiffAt.hartogs_dz {f : Ambient → ℂ} {p : Ambient} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 3) :
    ContDiffAt ℝ m (fun q => dz f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dz
  exact ((hd.clm_apply contDiffAt_const).sub
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma _root_.OAI.ContDiffAt.hartogs_real_cast {f : Ambient → ℝ} {p : Ambient} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) : ContDiffAt ℝ n (fun q => (f q : ℂ)) p :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp p hf

lemma dz_conj {f : Ambient → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p) (i : Fin 3) :
    dz (fun q => star (f q)) p i = star (dbar f p i) := by
  have hd : fderiv ℝ (fun q => star (f q)) p = Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f p) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p hf.hasFDerivAt).fderiv
  simp only [dz, dbar, hd]
  simp [star_add, star_mul]
  ring

def dzFunctional (i : Fin 3) : (Ambient →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (coordVector i) -
    Complex.I • ContinuousLinearMap.apply ℝ ℂ (Complex.I • coordVector i))

def dbarFunctional (i : Fin 3) : (Ambient →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.apply ℝ ℂ (coordVector i) +
    Complex.I • ContinuousLinearMap.apply ℝ ℂ (Complex.I • coordVector i))

lemma dzFunctional_apply (D : Ambient →L[ℝ] ℂ) (i : Fin 3) :
    dzFunctional i D = (D (coordVector i) - Complex.I * D (Complex.I • coordVector i)) / 2 := by
  simp only [dzFunctional, sub_apply, smul_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

lemma dbarFunctional_apply (D : Ambient →L[ℝ] ℂ) (i : Fin 3) :
    dbarFunctional i D = (D (coordVector i) + Complex.I * D (Complex.I • coordVector i)) / 2 := by
  simp only [dbarFunctional, add_apply, smul_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

lemma fderiv_dz_apply {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i : Fin 3) (v : Ambient) :
    fderiv ℝ (fun q => dz f q i) p v =
      (fderiv ℝ (fderiv ℝ f) p v (coordVector i) -
        Complex.I * fderiv ℝ (fderiv ℝ f) p v (Complex.I • coordVector i)) / 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun q => dz f q i) = (fun q => dzFunctional i (fderiv ℝ f q)) := by
    funext q
    exact (dzFunctional_apply _ i).symm
  rw [he]
  have hh : fderiv ℝ (fun q => dzFunctional i (fderiv ℝ f q)) p =
      (dzFunctional i).comp (fderiv ℝ (fderiv ℝ f) p) :=
    ((dzFunctional i).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
  rw [hh, ContinuousLinearMap.comp_apply, dzFunctional_apply]

lemma fderiv_dbar_apply {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i : Fin 3) (v : Ambient) :
    fderiv ℝ (fun q => dbar f q i) p v =
      (fderiv ℝ (fderiv ℝ f) p v (coordVector i) +
        Complex.I * fderiv ℝ (fderiv ℝ f) p v (Complex.I • coordVector i)) / 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : (fun q => dbar f q i) = (fun q => dbarFunctional i (fderiv ℝ f q)) := by
    funext q
    exact (dbarFunctional_apply _ i).symm
  rw [he]
  have hh : fderiv ℝ (fun q => dbarFunctional i (fderiv ℝ f q)) p =
      (dbarFunctional i).comp (fderiv ℝ (fderiv ℝ f) p) :=
    ((dbarFunctional i).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
  rw [hh, ContinuousLinearMap.comp_apply, dbarFunctional_apply]

lemma dz_dbar_comm {f : Ambient → ℂ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i j : Fin 3) :
    dz (fun q => dbar f q j) p i = dbar (fun q => dz f q i) p j := by
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  change (fderiv ℝ (fun q => dbar f q j) p (coordVector i) -
    Complex.I * fderiv ℝ (fun q => dbar f q j) p (Complex.I • coordVector i)) / 2 =
    (fderiv ℝ (fun q => dz f q i) p (coordVector j) +
    Complex.I * fderiv ℝ (fun q => dz f q i) p (Complex.I • coordVector j)) / 2
  simp only [fderiv_dz_apply hf, fderiv_dbar_apply hf]
  conv_lhs =>
    rw [hs (coordVector i) (coordVector j), hs (coordVector i) (Complex.I • coordVector j),
      hs (Complex.I • coordVector i) (coordVector j),
      hs (Complex.I • coordVector i) (Complex.I • coordVector j)]
  ring

lemma complexHessian_hermitian {f : Ambient → ℝ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (i j : Fin 3) :
    complexHessian f p i j = star (complexHessian f p j i) := by
  have hdc := (_root_.OAI.ContDiffAt.hartogs_real_cast hf)
  have he : (fun q => dbar (fun r => (f r : ℂ)) q i) =ᶠ[𝓝 p]
      (fun q => star (dz (fun r => (f r : ℂ)) q i)) := by
    filter_upwards [hf.eventually (by norm_num)] with q hq
    exact dbar_eq_star_dz_real (hq.differentiableAt (by norm_num)) i
  unfold complexHessian
  rw [dz_congr he, dz_conj ((_root_.OAI.ContDiffAt.hartogs_dz hdc (m := 1) (by norm_num) i).differentiableAt (by norm_num)),
    star_star, dz_dbar_comm hdc]

def coordinateLinearEquiv : Ambient ≃ₗ[ℂ] Target where
  toFun := coordinates
  invFun t := (WithLp.toLp 2 ![t 0, t 1], t 2)
  left_inv p := by
    apply Prod.ext
    · ext i
      fin_cases i <;> rfl
    · rfl
  right_inv t := by
    funext i
    fin_cases i <;> rfl
  map_add' p q := by
    ext i
    fin_cases i <;> rfl
  map_smul' c p := by
    ext i
    fin_cases i <;> rfl

def coordinateEquiv : Ambient ≃L[ℂ] Target := coordinateLinearEquiv.toContinuousLinearEquiv

def coordCLM (i : Fin 3) : Ambient →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp coordinateEquiv.toContinuousLinearMap

lemma dz_lift_base {f : Base → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p.1) (i : Fin 3) :
    dz (fun q : Ambient => f q.1) p i = ![dzBase f p.1 0, dzBase f p.1 1, 0] i := by
  have hd : fderiv ℝ (fun q : Ambient => f q.1) p =
      (fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ Base ℂ) :=
    (hf.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ Base ℂ).hasFDerivAt).fderiv
  fin_cases i <;> simp [dz, dzBase, hd, coordVector]

lemma dbar_lift_base {f : Base → ℂ} {p : Ambient} (hf : DifferentiableAt ℝ f p.1) (i : Fin 3) :
    dbar (fun q : Ambient => f q.1) p i = ![dbarBase f p.1 0, dbarBase f p.1 1, 0] i := by
  have hd : fderiv ℝ (fun q : Ambient => f q.1) p =
      (fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ Base ℂ) :=
    (hf.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ Base ℂ).hasFDerivAt).fderiv
  fin_cases i <;> simp [dbar, dbarBase, hd, coordVector]

lemma _root_.OAI.ContDiffAt.hartogs_dbarBase {f : Base → ℂ} {p : Base} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f p) (hmn : m + 1 ≤ n) (i : Fin 2) :
    ContDiffAt ℝ m (fun q => dbarBase f q i) p := by
  have hd := hf.fderiv_right hmn
  unfold PinchedHartogs.dbarBase
  exact ((hd.clm_apply contDiffAt_const).add
    (contDiffAt_const.mul (hd.clm_apply contDiffAt_const))).div_const 2

lemma complexHessian_lift_base {f : Base → ℝ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p.1)
    (i j : Fin 3) :
    complexHessian (fun q : Ambient => f q.1) p i j =
      !![baseHessian f p.1 0 0, baseHessian f p.1 0 1, 0;
         baseHessian f p.1 1 0, baseHessian f p.1 1 1, 0;
         0, 0, 0] i j := by
  have hfc : ContDiffAt ℝ 2 (fun z => (f z : ℂ)) p.1 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p.1 hf
  have hd (k : Fin 2) : DifferentiableAt ℝ (fun z => dbarBase (fun r => (f r : ℂ)) z k) p.1 :=
    (_root_.OAI.ContDiffAt.hartogs_dbarBase hfc (m := 1) (by norm_num) k).differentiableAt (by norm_num)
  have he : (fun q : Ambient => dbar (fun r : Ambient => (f r.1 : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q : Ambient => ![dbarBase (fun r => (f r : ℂ)) q.1 0,
        dbarBase (fun r => (f r : ℂ)) q.1 1, 0] j) := by
    filter_upwards [continuousAt_fst.preimage_mem_nhds (hfc.eventually (by norm_num))] with q hq
    change ContDiffAt ℝ 2 (fun z => (f z : ℂ)) q.1 at hq
    exact dbar_lift_base (hq.differentiableAt (by norm_num)) j
  unfold complexHessian
  rw [dz_congr he]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact dz_lift_base (hd 0) _
    | exact dz_lift_base (hd 1) _
    | simp [dz]

def IsPshBase (φ : Base → ℝ) : Prop :=
  ∀ z ∈ ball, ∀ v : Base, 0 ≤ (∑ i, ∑ j, baseHessian φ z i j * v i * star (v j)).re

def fiberParameter (φ : Base → ℝ) (p : Ambient) : ℝ := Real.exp (φ p.1) * ‖p.2‖ ^ 2

def fiberPotential (φ : Base → ℝ) (p : Ambient) : ℝ := -Real.log (1 - fiberParameter φ p)

def thetaValue (φ : Base → ℝ) (p u : Ambient) : ℂ :=
  u.2 + p.2 * (dzBase (fun z => (φ z : ℂ)) p.1 0 * u.1 0 +
    dzBase (fun z => (φ z : ℂ)) p.1 1 * u.1 1)

def hartogsCompactSet (φ : Base → ℝ) (ρ τ : ℝ) : Set Ambient :=
  {p | ‖p.1‖ ≤ ρ ∧ fiberParameter φ p ≤ τ}

lemma exp_half_sq (a : ℝ) : (Real.exp (a / 2)) ^ 2 = Real.exp a := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

@[simp] lemma coordinates_equiv_symm (v : Target) : coordinates (coordinateEquiv.symm v) = v :=
  coordinateEquiv.apply_symm_apply v

@[simp] lemma coordinates_zero : coordinates (0 : Ambient) = 0 := coordinateEquiv.map_zero

def geodesicAcceleration (g : Ambient → CMatrix) (p v : Ambient) : Ambient :=
  coordinateEquiv.symm (fun k => -∑ a, ∑ c,
    christoffel g p k a c * coordinates v a * coordinates v c)

def geodesicField (g : Ambient → CMatrix) (y : Ambient × Ambient) : Ambient × Ambient :=
  (y.2, geodesicAcceleration g y.1 y.2)

def connectionCubic (g : Ambient → CMatrix) (p v : Ambient) : ℂ :=
  ∑ a, ∑ c, ∑ e, dz (fun q => g q c e) p a *
    coordinates v a * coordinates v c * star (coordinates v e)

def metricEnergy (g : Ambient → CMatrix) (y : Ambient × Ambient) : ℝ :=
  (hermitianValue (g y.1) y.2 y.2).re

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler2074_1 uKahler2080_1 uKahler2312_1 uKahler2472_1

open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def complexJacobian (F : Ambient → Ambient) (p : Ambient) : Fin 3 → Fin 3 → ℂ :=
  fun a i => coordinates (fderiv ℂ F p (coordVector i)) a

def dzMatrix (g : Ambient → CMatrix) (p : Ambient) (a : Fin 3) : CMatrix :=
  Matrix.of (fun i j => dz (fun q => g q i j) p a)
def dbarMatrix (g : Ambient → CMatrix) (p : Ambient) (a : Fin 3) : CMatrix :=
  Matrix.of (fun i j => dbar (fun q => g q i j) p a)

def curvatureMatrix (g : Ambient → CMatrix) (p : Ambient) (a b : Fin 3) : CMatrix :=
  -dbarMatrix (fun q => dzMatrix g q a) p b + dzMatrix g p a * (g p)⁻¹ * dbarMatrix g p b

def jacobianMatrix (F : Ambient → Ambient) (p : Ambient) : CMatrix :=
  Matrix.of (complexJacobian F p)

def pullbackMetric (g : Ambient → CMatrix) (F : Ambient → Ambient) (p : Ambient) : CMatrix :=
  (jacobianMatrix F p)ᵀ * g (F p) * (jacobianMatrix F p)ᵀᴴ

def matrixPush (A : CMatrix) (u : Ambient) : Ambient :=
  coordinateEquiv.symm (A *ᵥ coordinates u)

def matrixPull (A h : CMatrix) : CMatrix := Aᵀ * h * Aᵀᴴ

def tensorPairMatrix (R : CurvatureTensor) (w y : Ambient) : CMatrix :=
  Matrix.of (fun a b => hermitianValue (Matrix.of (R a b)) w y)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def logarithmicBarrier (s : ℝ) : ℝ := -Real.log (1 - Real.exp s)
def barrierX (s : ℝ) : ℝ := Real.exp s / (1 - Real.exp s)
def barrierQ (s : ℝ) : ℝ := barrierX s * (1 + barrierX s)
def barrierThird (s : ℝ) : ℝ := barrierQ s * (1 + 2 * barrierX s)
def barrierFourth (s : ℝ) : ℝ := barrierQ s * (1 + 6 * barrierX s + 6 * barrierX s ^ 2)

def horizontalIdentity (i j : Fin 3) : ℂ :=
  (if i = 0 then 1 else 0) * (if j = 0 then 1 else 0) +
  (if i = 1 then 1 else 0) * (if j = 1 then 1 else 0)

def inverseCube (s : ℝ) : ℝ := 2 / (1 - s) ^ 3
def inverseFourth (s : ℝ) : ℝ := 6 / (1 - s) ^ 4

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def baseCoordinateEquiv : Base ≃L[ℂ] (Fin 2 → ℂ) :=
  PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)

def baseCoordinate (i : Fin 2) : Base →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp baseCoordinateEquiv.toContinuousLinearMap

@[simp] lemma baseCoordinate_apply (i : Fin 2) (z : Base) : baseCoordinate i z = z i := rfl

lemma centeredChart_analyticAt {r : ℝ} (U : Base ≃ₗᵢ[ℂ] Base) {z : Base}
    (hden : 1 + (r : ℂ) * z 0 ≠ 0) : AnalyticAt ℂ (centeredChart r U) z := by
  have h0 : AnalyticAt ℂ (fun z : Base => z 0) z := (baseCoordinate 0).analyticAt _
  have h1 : AnalyticAt ℂ (fun z : Base => z 1) z := (baseCoordinate 1).analyticAt _
  have hd : AnalyticAt ℂ (fun z : Base => 1 + (r : ℂ) * z 0) z := analyticAt_const.add (analyticAt_const.mul h0)
  have hv : AnalyticAt ℂ (fun z : Base => ![((r : ℂ) + z 0) / (1 + (r : ℂ) * z 0),
      (Real.sqrt (1-r^2) : ℂ) * z 1 / (1 + (r : ℂ) * z 0)]) z := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact (analyticAt_const.add h0).div hd hden
    · exact (analyticAt_const.mul h1).div hd hden
  exact (U.toContinuousLinearEquiv.analyticAt _).comp ((baseCoordinateEquiv.symm.analyticAt _).comp hv)

lemma centeredChart_zero (r : ℝ) (U : Base ≃ₗᵢ[ℂ] Base) :
    centeredChart r U 0 = U ((r : ℂ) • EuclideanSpace.single 0 1) := by
  unfold centeredChart
  congr 1
  ext i
  fin_cases i <;> simp

lemma centeredChart_zero_mem {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) : centeredChart r U 0 ∈ ball := by
  rw [centeredChart_zero]
  simpa [ball, norm_smul, abs_of_nonneg hr] using hr1

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def horizontalCoordinate (i : Fin 2) : Ambient →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ Base ℂ))

@[simp] lemma horizontalCoordinate_apply (i : Fin 2) (p : Ambient) :
    horizontalCoordinate i p = p.1 i := rfl

@[simp] lemma horizontalCoordinate_coordVector (i : Fin 2) (j : Fin 3) :
    horizontalCoordinate i (coordVector j) = if j = i.castSucc then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coordVector]

def gaugePolynomial (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (p : Ambient) : ℂ :=
  (∑ i, a i * p.1 i) + (1/2 : ℂ) * ∑ i, ∑ k, B i k * p.1 i * p.1 k

@[simp] lemma gaugePolynomial_center (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (w : ℂ) :
    gaugePolynomial a B (0,w) = 0 := by simp [gaugePolynomial]

def firstGaugeJet (f : Ambient → ℝ) (p : Ambient) (i : Fin 2) : ℂ :=
  dz (fun q => (f q : ℂ)) p i.castSucc

def secondGaugeJet (f : Ambient → ℝ) (p : Ambient) (i k : Fin 2) : ℂ :=
  dz (fun q => dz (fun r => (f r : ℂ)) q k.castSucc) p i.castSucc

def fiberGaugeMap (C : Base → Base) (P : Ambient → ℂ) (q : Ambient) : Ambient :=
  (C q.1, Complex.exp (q.2 - P q))

def gaugeLogParameter (φ : Base → ℝ) (C : Base → Base) (P : Ambient → ℂ)
    (q : Ambient) : ℝ := φ (C q.1) + 2 * (q.2 - P q).re

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def baseGaugePolynomial (f : Base → ℝ) (w : ℂ) : Ambient → ℂ :=
  gaugePolynomial (firstGaugeJet (fun q => f q.1) (0,w))
    (secondGaugeJet (fun q => f q.1) (0,w))

def normalLogWeight (f : Base → ℝ) (w : ℂ) (q : Ambient) : ℝ :=
  f q.1 - 2 * (baseGaugePolynomial f w q - q.2).re

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def verticalDelta (i : Fin 3) : ℂ := if i = 2 then 1 else 0

def liftedHessian (f : Base → ℝ) (q : Ambient) : CMatrix :=
  complexHessian (fun q : Ambient => f q.1) q

def liftedThird (f : Base → ℝ) (q : Ambient) (a c d : Fin 3) : ℂ :=
  dz (fun r => liftedHessian f r c d) q a

def liftedBarThird (f : Base → ℝ) (q : Ambient) (b c d : Fin 3) : ℂ :=
  dbar (fun r => liftedHessian f r c d) q b

def liftedFourth (f : Base → ℝ) (q : Ambient) (a b c d : Fin 3) : ℂ :=
  dbar (fun r => liftedThird f r a c d) q b

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsJetLinearity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def normalPotential (f : Base → ℝ) (lam : ℝ) (w : ℂ) (q : Ambient) : ℝ :=
  lam * psi q.1 + logarithmicBarrier (normalLogWeight f w q)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsLiftedJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma liftedHessian_horizontal {f : Base → ℝ} {q : Ambient}
    (hf : ContDiffAt ℝ 2 f q.1) (i j : Fin 2) :
    liftedHessian f q i.castSucc j.castSucc = baseHessian f q.1 i j := by
  dsimp [liftedHessian]
  rw [complexHessian_lift_base hf]
  fin_cases i <;> fin_cases j <;> rfl

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsNormalBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

def block3 (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) : CMatrix :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0,0,r]

@[simp] lemma block3_horizontal (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (i j : Fin 2) :
    block3 A r i.castSucc j.castSucc = A i j := by
  fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma block3_vertical_left (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (j : Fin 2) :
    block3 A r 2 j.castSucc = 0 := by fin_cases j <;> rfl
@[simp] lemma block3_vertical_right (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) (i : Fin 2) :
    block3 A r i.castSucc 2 = 0 := by fin_cases i <;> rfl
@[simp] lemma block3_vertical (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℂ) : block3 A r 2 2 = r := rfl

@[simp] lemma verticalDelta_horizontal (i : Fin 2) : verticalDelta i.castSucc = 0 := by
  fin_cases i <;> simp [verticalDelta, Fin.ext_iff]
@[simp] lemma verticalDelta_vertical : verticalDelta 2 = 1 := rfl
@[simp] lemma horizontalIdentity_horizontal (i j : Fin 2) :
    horizontalIdentity i.castSucc j.castSucc = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases i <;> fin_cases j <;> norm_num [horizontalIdentity, Matrix.one_apply]
@[simp] lemma horizontalIdentity_vertical_left (i : Fin 3) : horizontalIdentity 2 i = 0 := by
  simp [horizontalIdentity]
@[simp] lemma horizontalIdentity_vertical_right (i : Fin 3) : horizontalIdentity i 2 = 0 := by
  simp [horizontalIdentity]

lemma barrierX_positive {s : ℝ} (hs : s < 0) : 0 < barrierX s :=
  div_pos (Real.exp_pos s) (sub_pos.mpr (Real.exp_lt_one_iff.mpr hs))

lemma barrierQ_positive {s : ℝ} (hs : s < 0) : 0 < barrierQ s := by
  dsimp [barrierQ]
  have := barrierX_positive hs
  positivity

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.PinchingCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler4409_1 uKahler5342_1 uKahler5693_1 uKahler5694_1 uKahler5695_1 uKahler6181_1 uKahler6341_1 uKahler6602_1 uKahler6602_2 uKahler6609_1 uKahler6612_1 uKahler6615_1 uKahler6620_1 uKahler7053_1 uKahler7224_1

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Complex
namespace PinchedHartogs
namespace PlaneAlgebra

variable (V : Type uKahler4409_1) [AddCommGroup V] [Module ℂ V]

structure HForm where
  val : V → V → ℂ
  add_left : ∀ u v w, val (u + v) w = val u w + val v w
  smul_left : ∀ (c : ℂ) u v, val (c • u) v = c * val u v
  hermitian : ∀ u v, val v u = star (val u v)

instance instCoeFunHFormForallForallComplex : CoeFun (HForm V) (fun _ ↦ V → V → ℂ) := ⟨HForm.val⟩

variable {V}
namespace HForm
variable (h E : HForm V) (u v w : V) (c : ℂ)

@[simp] theorem map_add_left : h (u + v) w = h u w + h v w := h.add_left u v w
@[simp] theorem map_smul_left : h (c • u) v = c * h u v := h.smul_left c u v
@[simp] theorem map_add_right : h u (v + w) = h u v + h u w := by
  rw [h.hermitian, h.map_add_left, star_add, ← h.hermitian v u, ← h.hermitian w u]
@[simp] theorem map_smul_right : h u (c • v) = star c * h u v := by
  rw [h.hermitian, h.map_smul_left, star_mul, ← h.hermitian v u, mul_comm]
@[simp] theorem map_zero_left : h 0 u = 0 := by
  simpa using h.map_smul_left u u 0
@[simp] theorem map_zero_right : h u 0 = 0 := by
  rw [h.hermitian, h.map_zero_left, star_zero]
@[simp] theorem map_neg_left : h (-u) v = -h u v := by
  simpa using h.map_smul_left u v (-1)
@[simp] theorem map_neg_right : h u (-v) = -h u v := by
  simpa using h.map_smul_right u v (-1)
@[simp] theorem map_sub_left : h (u - v) w = h u w - h v w := by simp [sub_eq_add_neg]
@[simp] theorem map_sub_right : h u (v - w) = h u v - h u w := by simp [sub_eq_add_neg]
@[simp] theorem diag_im : (h u u).im = 0 := by
  have H := congrArg Complex.im (h.hermitian u u)
  simp only [Complex.star_def, Complex.conj_im] at H
  linarith
@[simp] theorem diag_real : ((h u u).re : ℂ) = h u u := by
  apply Complex.ext <;> simp

def q (u : V) : ℝ := (h u u).re

def area (u v : V) : ℝ := h.q u * h.q v - (h u v).re ^ 2

def imag (u v : V) : ℝ := (h u v).im

def Nonneg : Prop := ∀ u, 0 ≤ h.q u

def Pos : Prop := ∀ u, u ≠ 0 → 0 < h.q u

def Below (h E : HForm V) : Prop := ∀ u, h.q u ≤ E.q u

@[simp] theorem q_zero : h.q 0 = 0 := by simp [q]
@[simp] theorem q_smul (c : ℂ) (u : V) : h.q (c • u) = Complex.normSq c * h.q u := by
  simp [q, Complex.mul_re, Complex.normSq_apply]
  ring
@[simp] theorem q_add : h.q (u + v) = h.q u + h.q v + 2 * (h u v).re := by
  simp [q, h.hermitian v u]
  ring
@[simp] theorem q_sub : h.q (u - v) = h.q u + h.q v - 2 * (h u v).re := by
  simp [q, h.hermitian v u]
  ring

@[instance_reducible] def toCore (hh : h.Nonneg) : PreInnerProductSpace.Core ℂ V where
  inner u v := h v u
  conj_inner_symm u v := by exact (h.hermitian u v).symm
  re_inner_nonneg := hh
  add_left u v w := h.map_add_right w u v
  smul_left u v c := h.map_smul_right v u c

@[simp] theorem q_real_smul (a : ℝ) (u : V) : h.q ((a : ℂ) • u) = a ^ 2 * h.q u := by
  rw [q_smul]
  simp [pow_two]

@[simp] theorem q_add_I : h.q (u + Complex.I • v) = h.q u + h.q v + 2 * h.imag u v := by
  simp [imag, Complex.mul_re]

@[simp] theorem q_sub_I : h.q (u - Complex.I • v) = h.q u + h.q v - 2 * h.imag u v := by
  simp [imag, Complex.mul_re]

@[simp] theorem area_symm : h.area v u = h.area u v := by
  simp only [area, h.hermitian u v, star_def, conj_re]
  ring

def withVertical : HForm (V × ℂ) where
  val u v := h u.1 v.1 + u.2 * star v.2
  add_left u v w := by simp only [Prod.fst_add, Prod.snd_add, map_add_left, add_mul]; ring
  smul_left c u v := by simp [mul_add, mul_assoc]
  hermitian u v := by simp [h.hermitian u.1 v.1, mul_comm]

@[simp] theorem withVertical_q (p : V × ℂ) :
    h.withVertical.q p = h.q p.1 + Complex.normSq p.2 := by
  simp [withVertical, q, Complex.normSq_apply]

def scale (a : ℝ) : HForm V where
  val u v := (a : ℂ) * h u v
  add_left u v w := by simp [mul_add]
  smul_left c u v := by simp [mul_left_comm]
  hermitian u v := by simp [h.hermitian u v]

@[simp] theorem scale_q (a : ℝ) (u : V) : (h.scale a).q u = a * h.q u := by
  simp [scale, q]

@[simp] theorem scale_imag (a : ℝ) (u v : V) : (h.scale a).imag u v = a * h.imag u v := by
  simp [scale, imag]

@[simp] theorem scale_area (a : ℝ) (u v : V) : (h.scale a).area u v = a ^ 2 * h.area u v := by
  rw [area, scale_q, scale_q]
  change a * h.q u * (a * h.q v) - ((a : ℂ) * h u v).re ^ 2 = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, area]
  ring

end HForm

variable (h E : HForm V) (u v : V) (y z : ℂ)

def verticalImag (y z : ℂ) : ℝ := (y * star z).im

def verticalArea (y z : ℂ) : ℝ :=
  Complex.normSq y * Complex.normSq z - (y * star z).re ^ 2

def mixed : ℝ := h.q u * Complex.normSq z + h.q v * Complex.normSq y -
  2 * (h u v).re * (y * star z).re

def xi : V := star z • u - star y • v

def P : ℝ := h.area u v + 3 * h.imag u v ^ 2 + 4 * verticalArea y z +
  mixed E u v y z + 6 * E.imag u v * verticalImag y z

def errorCoefficient (c E : ℝ) : ℝ := E + E ^ 2 / (2 * c)

def thresholdGap (c C E : ℝ) : ℝ :=
  c ^ 3 / (8 * (2 * (errorCoefficient c E + 1) + C))

def pinchingThreshold (c C E : ℝ) : ℝ :=
  max (C + 1) (max (18 * C ^ 2 + errorCoefficient c E + 1)
    (max (2 * (5 * C ^ 2 / 4) + 1)
      (2 * (errorCoefficient c E + 1) *
        ((errorCoefficient c E + 1) / thresholdGap c C E + 1))))

def numerator (g h D : HForm V) (lam x e4 e3 : ℝ) (u v : V) (y z : ℂ) : ℝ :=
  lam * (g.area u v + 3 * g.imag u v ^ 2) +
  x * (1 + x) * (h.area u v + 3 * h.imag u v ^ 2) +
  4 * verticalArea y z + mixed D u v y z + 6 * D.imag u v * verticalImag y z - e4 - e3

end PlaneAlgebra
end PinchedHartogs

namespace PinchedHartogs.PlaneAlgebra
namespace MatrixAlgebra
open Matrix Unitary
open scoped ComplexOrder
variable {n : Type uKahler5342_1} [finiteIndex : Fintype n] [decidableIndex : DecidableEq n]

def form (A : Matrix n n ℂ) (hA : A.IsHermitian) : HForm (n → ℂ) where
  val u v := dotProduct u (A *ᵥ star v)
  add_left u v w := by simp [add_dotProduct]
  smul_left c u v := by simp
  hermitian u v := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul, star_star,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hA.apply i j]
    ring

omit finiteIndex decidableIndex in
@[simp] theorem form_q {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (u : n → ℂ) :
    (form A hA).q u = (dotProduct u (A *ᵥ star u)).re := rfl

@[simp] theorem form_one_q (u : n → ℂ) :
    (form 1 Matrix.isHermitian_one).q u = ∑ i, Complex.normSq (u i) := by
  simp [form_q, dotProduct, Complex.mul_conj]

omit finiteIndex decidableIndex in
@[simp] theorem form_sub_q {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (u : n → ℂ) : (form (A - B) (hA.sub hB)).q u = (form A hA).q u - (form B hB).q u := by
  simp [form_q, sub_mulVec, dotProduct_sub]

omit finiteIndex decidableIndex in
@[simp] theorem form_real_smul_q {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (r : ℝ)
    (u : n → ℂ) : (form (r • A) (hA.smul (by rfl : IsSelfAdjoint r))).q u = r * (form A hA).q u := by
  simp [form_q, smul_mulVec, dotProduct_smul]

def horizontalMetric (A : Matrix n n ℂ) (lam x : ℝ) : Matrix n n ℂ := lam • 1 + x • A

def mixedMatrix (A : Matrix n n ℂ) (lam x : ℝ) : Matrix n n ℂ :=
  (1 + 2 * x) • A - (x * (1 + x)) • (A * (horizontalMetric A lam x)⁻¹ * A)

omit finiteIndex decidableIndex in
theorem horizontalMetric_hermitian {n : Type uKahler5342_1} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian) (lam x : ℝ) :
    (horizontalMetric A lam x).IsHermitian :=
  (Matrix.isHermitian_one.smul (by rfl)).add (hA.smul (by rfl))

theorem mixedMatrix_hermitian (A : Matrix n n ℂ) (hA : A.IsHermitian) (lam x : ℝ) :
    (mixedMatrix A lam x).IsHermitian := by
  have H := Matrix.isHermitian_conjTranspose_mul_mul A (horizontalMetric_hermitian A hA lam x).inv
  rw [hA.eq] at H
  exact (hA.smul (by rfl)).sub (H.smul (by rfl))

end MatrixAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
variable {n : Type uKahler5693_1} [finiteIndex : Fintype n]
abbrev Quad (n : Type uKahler5694_1) := n × n × n × n
abbrev Tensor (n : Type uKahler5695_1) := n → n → n → n → ℂ

structure Symmetries (T : Tensor n) : Prop where
  hol : ∀ a b c d, T a b c d = T c b a d
  anti : ∀ a b c d, T a b c d = T a d c b
  reality : ∀ a b c d, star (T a b c d) = T b a d c

def eval (T : Tensor n) (u v w y : n → ℂ) : ℂ :=
  ∑ t : Quad n, T t.1 t.2.1 t.2.2.1 t.2.2.2 *
    u t.1 * star (v t.2.1) * w t.2.2.1 * star (y t.2.2.2)

def H (T : Tensor n) (u v : n → ℂ) : ℝ :=
  (eval T u u v v).re - (eval T u v u v).re

def Xi (u v : n → ℂ) (a b : n) : ℂ := u a * star (v b) - v a * star (u b)

def xiContract (T : Tensor n) (u v : n → ℂ) : ℂ :=
  ∑ t : Quad n, T t.1 t.2.1 t.2.2.1 t.2.2.2 * Xi u v t.1 t.2.1 * Xi u v t.2.2.1 t.2.2.2

def swapHol : Quad n ≃ Quad n where
  toFun t := (t.2.2.1, t.2.1, t.1, t.2.2.2)
  invFun t := (t.2.2.1, t.2.1, t.1, t.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def swapAnti : Quad n ≃ Quad n where
  toFun t := (t.1, t.2.2.2, t.2.2.1, t.2.1)
  invFun t := (t.1, t.2.2.2, t.2.2.1, t.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def swapConj : Quad n ≃ Quad n where
  toFun t := (t.2.1, t.1, t.2.2.2, t.2.2.1)
  invFun t := (t.2.1, t.1, t.2.2.2, t.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def componentNorm (T : Tensor n) : ℝ :=
  Real.sqrt (∑ t : Quad n, Complex.normSq (T t.1 t.2.1 t.2.2.1 t.2.2.2))

abbrev Index := Option (Fin 2)

def lift (u : Fin 2 → ℂ) (y : ℂ) : Index → ℂ | none => y | some i => u i

def horizontalCount (a b c d : Index) : ℕ :=
  (if a.isSome then 1 else 0) + (if b.isSome then 1 else 0) +
    (if c.isSome then 1 else 0) + (if d.isSome then 1 else 0)

def Supported (T : Tensor Index) (j : ℕ) : Prop :=
  ∀ a b c d, horizontalCount a b c d ≠ j → T a b c d = 0

abbrev euclidean : HForm (Fin 2 → ℂ) := form 1 Matrix.isHermitian_one

section SymmetricTensor
variable [decidableIndex : DecidableEq n]

def S (A : Matrix n n ℂ) : Tensor n :=
  fun a b c d ↦ A a b * A c d + A a d * A c b

def productTensor (A B : Matrix n n ℂ) : Tensor n :=
  fun a b c d ↦ A a b * B c d

end SymmetricTensor

def block (A : Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) : Matrix Index Index ℂ
  | none, none => r
  | some i, some j => A i j
  | _, _ => 0

omit finiteIndex in
theorem block_hermitian {n : Type uKahler5693_1} [Fintype n] (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (r : ℝ) : (block A r).IsHermitian := by
  ext a b
  cases a <;> cases b <;> simp [Matrix.conjTranspose, block]
  exact hA.apply _ _

def curvatureModel (A : Matrix (Fin 2) (Fin 2) ℂ) (lam x : ℝ)
    (T4 T3 : Tensor Index) : Tensor Index :=
  (-lam) • S (block 1 0) - (x * (1 + x)) • S (block A 0) - S (block 0 1) -
    (S (block (mixedMatrix A lam x) 1) - S (block (mixedMatrix A lam x) 0) -
      S (block 0 1)) + T4 + T3

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

section Rescaling
variable {n : Type uKahler6181_1} [finiteIndex : Fintype n]

def pullTensor (r : n → ℝ) (T : Tensor n) : Tensor n :=
  fun a b c d ↦ (r a : ℂ) * r b * r c * r d * T a b c d

def pullVector (r : n → ℝ) (u : n → ℂ) : n → ℂ := fun a ↦ (r a : ℂ) * u a

def pullMatrix (r : n → ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  fun a b ↦ (r a : ℂ) * r b * A a b

end Rescaling

def horizontalScale (r : ℝ) : Index → ℝ | none => 1 | some _ => r

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

def mixedTensor (A : Matrix (Fin 2) (Fin 2) ℂ) : Tensor Index :=
  S (block A 1) - S (block A 0) - S (block 0 1)

def compactG (A : Matrix (Fin 2) (Fin 2) ℂ) (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1-t)*lam) • 1 + t • A

def compactD (A : Matrix (Fin 2) (Fin 2) ℂ) (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1+t) • A - t • (A * (compactG A lam t)⁻¹ * A)

def compactCurvature (A : Matrix (Fin 2) (Fin 2) ℂ) (lam t : ℝ)
    (E4 E3 : Tensor Index) : Tensor Index :=
  (-(lam * (1-t)^2)) • S (block 1 0) - t • S (block A 0) - S (block 0 1) -
    mixedTensor (compactD A lam t) + E4 + E3

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

def liftEquiv : ((Fin 2 → ℂ) × ℂ) ≃ₗ[ℂ] (Index → ℂ) where
  toFun p := lift p.1 p.2
  invFun w := (fun i ↦ w (some i), w none)
  left_inv _ := rfl
  right_inv w := by ext a; cases a <;> rfl
  map_add' _ _ := by ext a; cases a <;> rfl
  map_smul' _ _ := by ext a; cases a <;> rfl

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

open scoped Matrix.Norms.Elementwise

abbrev BaseMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev FullVector := Index → ℂ

def pairValue {n : Type uKahler6609_1} [finiteIndex : Fintype n] (A : Matrix n n ℂ) (u v : n → ℂ) : ℂ :=
  dotProduct u (A *ᵥ star v)

def qValue {n : Type uKahler6612_1} [finiteIndex : Fintype n] (A : Matrix n n ℂ) (u : n → ℂ) : ℝ :=
  (pairValue A u u).re

def matrixSet (c C : ℝ) : Set BaseMatrix :=
  {A | A.IsHermitian ∧ ∀ w, c * qValue 1 w ≤ qValue A w ∧ qValue A w ≤ C * qValue 1 w}

def pairSet : Set (FullVector × FullVector) :=
  {p | qValue 1 p.1 = 1 ∧ qValue 1 p.2 = 1 ∧ (pairValue 1 p.1 p.2).re = 0}

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder

open scoped Matrix.Norms.Elementwise

local instance tensorTopology : TopologicalSpace (Tensor Index) := Pi.topologicalSpace
local instance matrixTopology : TopologicalSpace BaseMatrix := inferInstance
local instance pairTopology : TopologicalSpace (FullVector × FullVector) := instTopologicalSpaceProd

abbrev CompactData := ℝ × BaseMatrix × Tensor Index × Tensor Index × (FullVector × FullVector)

def dataSet (c C Ce : ℝ) : Set CompactData := {d |
  d.1 ∈ Set.Icc 0 1 ∧ d.2.1 ∈ matrixSet c C ∧
  Symmetries d.2.2.1 ∧ Supported d.2.2.1 4 ∧
  Symmetries d.2.2.2.1 ∧ Supported d.2.2.2.1 3 ∧
  componentNorm d.2.2.1 ≤ Ce*(d.1*(1-d.1)) ∧
  componentNorm d.2.2.2.1 ≤ Ce*Real.sqrt (d.1*(1-d.1)) ∧ d.2.2.2.2 ∈ pairSet}

theorem compactG_hermitian (A : BaseMatrix) (hA : A.IsHermitian) (lam t : ℝ) :
    (compactG A lam t).IsHermitian :=
  (Matrix.isHermitian_one.smul (by rfl)).add (hA.smul (by rfl))

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

local instance tensorTopology' : TopologicalSpace (Tensor Index) := Pi.topologicalSpace
local instance matrixTopology' : TopologicalSpace BaseMatrix := inferInstance
local instance pairTopology' : TopologicalSpace (FullVector × FullVector) := instTopologicalSpaceProd
local instance compactDataTopology : TopologicalSpace CompactData := inferInstance

def metricArea (A : BaseMatrix) (u v : FullVector) : ℝ :=
  qValue (block A 1) u * qValue (block A 1) v - (pairValue (block A 1) u v).re^2

def compactQuotient (lam : ℝ) (d : CompactData) : ℝ :=
  H (compactCurvature d.2.1 lam d.1 d.2.2.1 d.2.2.2.1) d.2.2.2.2.1 d.2.2.2.2.2 /
    (2 * metricArea (compactG d.2.1 lam d.1) d.2.2.2.2.1 d.2.2.2.2.2)

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

namespace PinchedHartogs.PlaneAlgebra
namespace TensorAlgebra
open MatrixAlgebra Matrix
open scoped ComplexOrder Matrix.Norms.Elementwise

def horizontalPullEquiv (r : ℝ) (hr : r ≠ 0) : FullVector ≃ₗ[ℂ] FullVector where
  toFun := pullVector (horizontalScale r)
  invFun := pullVector (horizontalScale r⁻¹)
  left_inv u := by
    ext a
    cases a <;> simp [pullVector, horizontalScale, hr]
  right_inv u := by
    ext a
    cases a <;> simp [pullVector, horizontalScale, hr]
  map_add' u v := by
    ext a
    simp [pullVector, mul_add]
  map_smul' z u := by
    ext a
    simp [pullVector, mul_left_comm]

end TensorAlgebra
end PinchedHartogs.PlaneAlgebra

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsModelBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Complex
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra

 def normalIndex : Index → Fin 3
  | none => 2
  | some i => i.castSucc

 def verticalScale (r : ℝ) : Index → ℝ
  | none => r
  | some _ => 1

 def normalCurvature (f : Base → ℝ) (lam : ℝ) (w : ℂ) : Tensor Index :=
  pullTensor (verticalScale ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹))
    (fun a b c d => curvature (complexHessian (normalPotential f lam w)) (0,w)
      (normalIndex a) (normalIndex b) (normalIndex c) (normalIndex d))

 def horizontalPart (j : ℕ) (T : Tensor Index) : Tensor Index :=
  fun a b c d => if horizontalCount a b c d = j then T a b c d else 0

lemma baseHessian_isHermitian {f : Base → ℝ} {z : Base} (hf : ContDiffAt ℝ 2 f z) :
    (baseHessian f z).IsHermitian := by
  ext i j
  change star (baseHessian f z j i) = baseHessian f z i j
  have hc := complexHessian_hermitian (hf.comp (f := fun q : Ambient => q.1) (z,0) contDiffAt_fst) i.castSucc j.castSucc
  change liftedHessian f (z,0) i.castSucc j.castSucc = star (liftedHessian f (z,0) j.castSucc i.castSucc) at hc
  rw [liftedHessian_horizontal hf, liftedHessian_horizontal hf] at hc
  exact hc.symm

def normalError (f : Base → ℝ) (lam : ℝ) (w : ℂ) : Tensor Index :=
  normalCurvature f lam w - curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w))) 0 0

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

def normalIndexEquiv : Index ≃ Fin 3 := Equiv.ofBijective normalIndex (by
  constructor
  · intro a b hab
    cases a <;> cases b
    · rfl
    · rename_i b; fin_cases b <;> simp [normalIndex] at hab
    · rename_i a; fin_cases a <;> simp [normalIndex] at hab
    · rename_i a b
      exact congrArg some (Fin.castSucc_injective _ hab)
  · intro a
    fin_cases a
    · exact ⟨some 0, rfl⟩
    · exact ⟨some 1, rfl⟩
    · exact ⟨none, rfl⟩)

def normalFrameEquiv (r : ℝ) (hr : r ≠ 0) : FullVector ≃ₗ[ℂ] Ambient :=
  (LinearEquiv.piCongrRight (fun a : Index => LinearEquiv.smulOfNeZero ℂ ℂ
    (verticalScale r a : ℂ) (by cases a <;> simp [verticalScale, hr]))).trans
      ((LinearEquiv.funCongrLeft ℂ ℂ normalIndexEquiv).symm.trans coordinateLinearEquiv.symm)

def metricErrorConstant (c C : ℝ) : ℝ := 9*(C+4*C^2/c)
def metricThreshold (c C : ℝ) : ℝ := pinchingThreshold c C (162*metricErrorConstant c C)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTransferTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

def liftBaseMap (C : Base → Base) (q : Ambient) : Ambient := (C q.1,q.2)

lemma chartWeight_contDiffAt {φ : Base → ℝ} (hφ : ContDiffOn ℝ ∞ φ ball)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) :
    ContDiffAt ℝ ∞ (φ ∘ centeredChart r U) 0 := by
  exact (hφ.contDiffAt (isOpen_ball.mem_nhds (centeredChart_zero_mem hr hr1 U))).comp 0
    ((centeredChart_analyticAt U (z := 0) (by simp)).contDiffAt.restrict_scalars ℝ)

end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
namespace PinchedHartogs
namespace BaseConstruction

abbrev Sphere := Metric.sphere (0 : Base) 1

def bracket (z p : Base) : ℂ := inner ℂ p z

def peakPolynomial (P : Finset Sphere) (k : ℕ) (z : Base) : ℂ :=
  ∑ p ∈ P, bracket z p ^ k

def regularizedLog (a ε : ℝ) (v : ℂ) : ℝ :=
  Real.log ((‖1-(a:ℂ)*v‖^2+ε^2)/(1+ε^2))

def logarithmicTest (a ε : ℝ) (P : Finset Sphere) (k : ℕ) (z : Base) : ℝ :=
  regularizedLog a ε (peakPolynomial P k z)

def basePotential (P : ℕ → Finset Sphere) (a ε L : ℝ) (Q : ℕ) (z : Base) : ℝ :=
  psi z + L * ∑' j : ℕ, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) z

@[simp] lemma regularizedLog_zero (a ε : ℝ) : regularizedLog a ε 0 = 0 := by
  simp [regularizedLog]

def regularizedFiberLog (ε : ℝ) (q : Ambient) : ℝ :=
  Real.log (‖q.2‖^2+ε^2)-Real.log (1+ε^2)

end BaseConstruction
end PinchedHartogs

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8561_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

instance instCompactSpaceElemBaseSphere : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere (0:Base) 1)

@[simp] lemma sphere_norm (ξ : Sphere) : ‖(ξ:Base)‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp ξ.property

def Represents (μ : Measure Sphere) : Prop :=
  ∀ p : MvPolynomial (Fin 2) ℂ, (∫ ξ : Sphere, MvPolynomial.eval (fun i => (ξ:Base) i) p ∂μ) =
    MvPolynomial.eval (fun _ => 0) p

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8786_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def sigma : Measure Sphere :=
  ((volume : Measure Base).toSphere univ)⁻¹ • (volume : Measure Base).toSphere

instance instIsProbabilityMeasureElemBaseSphereSigma : IsProbabilityMeasure sigma where
  measure_univ := by
    rw [sigma, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (ne_of_gt (Measure.measure_univ_pos.mpr (Measure.toSphere_ne_zero volume)))
      (measure_ne_top _ _)

def sphereAction (U : Base ≃ₗᵢ[ℂ] Base) : Sphere ≃ₜ Sphere :=
  U.toHomeomorph.subtype (fun z => by simp [])

@[simp] lemma sphereAction_coe (U : Base ≃ₗᵢ[ℂ] Base) (ξ : Sphere) :
    (sphereAction U ξ : Base) = U (ξ:Base) := rfl

def realIsometry (U : Base ≃ₗᵢ[ℂ] Base) : Base ≃ₗᵢ[ℝ] Base where
  toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ
  norm_map' := U.norm_map

def phaseIsometry (c : ℂ) (hc : ‖c‖ = 1) : Base ≃ₗᵢ[ℂ] Base where
  toLinearEquiv := LinearEquiv.smulOfUnit (Units.mk0 c (by intro h; simp [h] at hc))
  norm_map' z := by change ‖c • z‖ = ‖z‖; simp [norm_smul,hc]

@[simp] lemma phaseIsometry_apply (c : ℂ) (hc : ‖c‖ = 1) (z : Base) :
    phaseIsometry c hc z = c • z := rfl

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def suMap (a b : ℂ) : Base →ₗ[ℂ] Base :=
  Matrix.toEuclideanLin !![a,b; -star b,star a]

lemma suMap_norm (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) (z : Base) :
    ‖suMap a b z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two]
  have h0 : suMap a b z 0 = a*z 0+b*z 1 := by simp [suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]
  have h1 : suMap a b z 1 = -star b*z 0+star a*z 1 := by simp [suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]
  rw [h0,h1]
  simp only [← Complex.normSq_eq_norm_sq]
  calc
    _ = (Complex.normSq a+Complex.normSq b)*(Complex.normSq (z 0)+Complex.normSq (z 1)) := by
      simp [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im]
      ring
    _ = _ := by rw [h,one_mul]

def suIsometry (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) : Base ≃ₗᵢ[ℂ] Base :=
  let L : Base →ₗᵢ[ℂ] Base := ⟨suMap a b,suMap_norm a b h⟩
  LinearIsometryEquiv.ofSurjective L (LinearMap.surjective_of_injective L.injective)

@[simp] lemma suIsometry_zero (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) (z : Base) :
    suIsometry a b h z 0 = a*z 0+b*z 1 := by
  simp [suIsometry,suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

@[simp] lemma suIsometry_one (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) (z : Base) :
    suIsometry a b h z 1 = -star b*z 0+star a*z 1 := by
  simp [suIsometry,suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

def rotationIsometry (t : ℝ) : Base ≃ₗᵢ[ℂ] Base :=
  suIsometry (Real.cos t) (Real.sin t) (by
    simp only [Complex.normSq_ofReal]
    linarith [Real.cos_sq_add_sin_sq t])

def diagIsometry (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : Base ≃ₗᵢ[ℂ] Base :=
  let L : Base →ₗᵢ[ℂ] Base :=
    { toLinearMap := Matrix.toEuclideanLin !![a,0;0,b]
      norm_map' z := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,Matrix.toLpLin_apply,
          dotProduct,ha,hb] }
  LinearIsometryEquiv.ofSurjective L (LinearMap.surjective_of_injective L.injective)

@[simp] lemma diagIsometry_zero (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (z : Base) :
    diagIsometry a b ha hb z 0 = a*z 0 := by
  simp [diagIsometry,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

@[simp] lemma diagIsometry_one (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (z : Base) :
    diagIsometry a b ha hb z 1 = b*z 1 := by
  simp [diagIsometry,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

def radialU (ξ : Sphere) : ℝ := Complex.normSq ((ξ:Base) 0)
def radialV (ξ : Sphere) : ℝ := Complex.normSq ((ξ:Base) 1)
def radialR (ξ : Sphere) : ℝ := (((ξ:Base) 0)*star ((ξ:Base) 1)).re

def radialJ (ξ : Sphere) : ℝ := (((ξ:Base) 0)*star ((ξ:Base) 1)).im

lemma radialUV (ξ : Sphere) : radialU ξ + radialV ξ = 1 := by
  have h := congrArg (fun r : ℝ => r^2) (sphere_norm ξ)
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two] at h
  simpa only [one_pow,← Complex.normSq_eq_norm_sq,radialU,radialV] using h

lemma radialU_continuous : Continuous radialU := by
  exact Complex.continuous_normSq.comp ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
lemma radialV_continuous : Continuous radialV := by
  exact Complex.continuous_normSq.comp ((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val)
lemma radialR_continuous : Continuous radialR := by
  exact Complex.continuous_re.comp (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).mul
    (((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val).star))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def rotA (u v r t : ℝ) := Real.cos t^2*u+Real.sin t^2*v+2*Real.cos t*Real.sin t*r
def rotA' (u v r t : ℝ) := 2*Real.cos t*Real.sin t*(v-u)+2*(Real.cos t^2-Real.sin t^2)*r
def rotA'' (u v r t : ℝ) := 2*(Real.cos t^2-Real.sin t^2)*(v-u)-8*Real.cos t*Real.sin t*r

def rotF (n : ℕ) (t : ℝ) (ξ : Sphere) := rotA (radialU ξ) (radialV ξ) (radialR ξ) t^(n+2)
def rotF' (n : ℕ) (t : ℝ) (ξ : Sphere) :=
  (n+2 : ℝ)*rotA (radialU ξ) (radialV ξ) (radialR ξ) t^(n+1)*rotA' (radialU ξ) (radialV ξ) (radialR ξ) t
def rotF'' (n : ℕ) (t : ℝ) (ξ : Sphere) :=
  (n+2 : ℝ)*((n+1 : ℝ)*rotA (radialU ξ) (radialV ξ) (radialR ξ) t^n*
    (rotA' (radialU ξ) (radialV ξ) (radialR ξ) t)^2+
    rotA (radialU ξ) (radialV ξ) (radialR ξ) t^(n+1)*rotA'' (radialU ξ) (radialV ξ) (radialR ξ) t)

attribute [local fun_prop] radialU_continuous radialV_continuous radialR_continuous

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler9159_1 uKahler9161_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def radialUnit (ξ : Sphere) : unitInterval :=
  ⟨radialU ξ,Complex.normSq_nonneg _,by
    have hv : 0 ≤ radialV ξ := Complex.normSq_nonneg _
    linarith [radialUV ξ]⟩

def integralCM {X : Type uKahler9159_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {Y : Type uKahler9161_1} [TopologicalSpace Y] [CompactSpace Y] (g : X → Y) (hg : Continuous g) :
    C(Y,ℝ) →L[ℝ] ℝ :=
  ({ toFun := fun f => ∫ x, f (g x) ∂μ
     map_add' := fun f h => integral_add
       ((f.continuous.comp hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
       ((h.continuous.comp hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
     map_smul' := fun r f => by simp only [ContinuousMap.smul_apply,smul_eq_mul,integral_const_mul,RingHom.id_apply] } : C(Y,ℝ) →ₗ[ℝ] ℝ).mkContinuous 1 (by
    intro f
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall (fun x => f.norm_coe_le_norm (g x))))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def projectiveDistance (ξ p : Sphere) : ℝ := Real.sqrt (1-‖bracket (ξ:Base) (p:Base)‖^2)

def bloch (ξ : Sphere) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![radialU ξ,radialR ξ,radialJ ξ]

def adaptedIsometry (p : Sphere) : Base ≃ₗᵢ[ℂ] Base :=
  suIsometry (star ((p:Base) 0)) (star ((p:Base) 1)) (by
    simpa only [Complex.normSq_conj,Complex.star_def,radialU,radialV] using radialUV p)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def ProjectivelySeparated (ρ : ℝ) (P : Finset Sphere) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ ≤ projectiveDistance p q

def ProjectiveCover (ρ : ℝ) (P : Finset Sphere) : Prop :=
  ∀ ξ : Sphere, ∃ p ∈ P, projectiveDistance ξ p < ρ

def projectiveCap (p : Sphere) (s : ℝ) : Set Sphere := {ξ | projectiveDistance ξ p < s}

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def gaussianConstant : ℝ := ∑' n : ℕ, 9*((n:ℝ)+2)^2*Real.exp (-(n:ℝ)^2/4)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseAnisotropic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def anisotropicMap (k : ℕ) (r : ℝ) (z : Base) : Base :=
  WithLp.toLp 2 ![(r:ℂ)+z 0/(k:ℂ),z 1/(Real.sqrt (k:ℝ):ℂ)]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartLow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def anisotropicChart (k : ℕ) (r : ℝ) (z : Base) : Base :=
  WithLp.toLp 2 ![(k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ)),
    (Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0)]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseChartJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def chartScale (k : ℕ) (δ : ℝ) : ℝ :=
  if (k:ℝ)*δ ≤ 1 then Real.sqrt ((k:ℝ)*δ) else Real.exp (-(k:ℝ)*δ/16)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseJetNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def wirtingerCLM (b : Bool) (i : Fin 2) : (Base →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i 1)) +
    (if b then Complex.I else -Complex.I) •
      (ContinuousLinearMap.apply ℝ ℂ (Complex.I • EuclideanSpace.single i 1)))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHessianJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

abbrev ComplexJet2 := ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Base) ℂ
abbrev RealJet2 := ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Base) ℝ

def complexHessianJet (i j : Fin 2) : ComplexJet2 →L[ℝ] ℂ :=
  (1/4 : ℂ) •
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] +
    Complex.I • ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1] -
    Complex.I • ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![Complex.I • EuclideanSpace.single i 1, EuclideanSpace.single j 1] +
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Base) ℂ
      ![Complex.I • EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1])

def realHessianJet (i j : Fin 2) : RealJet2 →L[ℝ] ℂ :=
  (complexHessianJet i j).comp
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin 2 => Base) ℝ ℂ Complex.ofRealCLM)

def realHessianValueJet (v : Base) : RealJet2 →L[ℝ] ℝ :=
  Complex.reCLM.comp (∑ i : Fin 2, ∑ j : Fin 2, (v i*star (v j)) • realHessianJet i j)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler10884_1 uKahler10884_2 uKahler10889_1 uKahler10889_2 uKahler10889_3

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := borel Circle
instance instBorelSpaceCircle_solutions : BorelSpace Circle := ⟨rfl⟩

def circleMeasure : Measure Circle :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : TopologicalSpace.PositiveCompacts Circle)

instance instIsProbabilityMeasureCircleCircleMeasure : IsProbabilityMeasure circleMeasure where
  measure_univ := Measure.haarMeasure_self
instance instIsHaarMeasureCircleCircleMeasure : Measure.IsHaarMeasure circleMeasure := inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure _))

def torusMeasure : Measure (Circle × Circle) := circleMeasure.prod circleMeasure
instance instIsProbabilityMeasureProdCircleTorusMeasure : IsProbabilityMeasure torusMeasure := inferInstanceAs (IsProbabilityMeasure (circleMeasure.prod circleMeasure))
instance instIsMulLeftInvariantProdCircleTorusMeasure : Measure.IsMulLeftInvariant torusMeasure := inferInstanceAs (Measure.IsMulLeftInvariant (circleMeasure.prod circleMeasure))
instance instIsMulRightInvariantProdCircleTorusMeasure : Measure.IsMulRightInvariant torusMeasure := inferInstanceAs (Measure.IsMulRightInvariant (circleMeasure.prod circleMeasure))

def torusAction (z : Circle × Circle) (ξ : Sphere) : Sphere :=
  sphereAction (diagIsometry z.1 z.2 z.1.norm_coe z.2.norm_coe) ξ

@[simp] lemma torusAction_zero (z : Circle × Circle) (ξ : Sphere) :
    (torusAction z ξ : Base) 0 = (z.1:ℂ)*(ξ:Base) 0 := by simp [torusAction]
@[simp] lemma torusAction_one (z : Circle × Circle) (ξ : Sphere) :
    (torusAction z ξ : Base) 1 = (z.2:ℂ)*(ξ:Base) 1 := by simp [torusAction]

def radialSphere (u : unitInterval) : Sphere :=
  ⟨(WithLp.toLp 2 ![(Real.sqrt (u:ℝ):ℂ),(Real.sqrt (1-(u:ℝ)):ℂ)] : Base),by
    rw [Metric.mem_sphere,dist_zero_right]
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt u.property.1,Real.sq_sqrt (sub_nonneg.mpr u.property.2),one_pow]
    ring⟩

@[simp] lemma radialSphere_zero (u : unitInterval) : (radialSphere u : Base) 0 = (Real.sqrt (u:ℝ):ℂ) := rfl
@[simp] lemma radialSphere_one (u : unitInterval) : (radialSphere u : Base) 1 = (Real.sqrt (1-(u:ℝ)):ℂ) := rfl

attribute [irreducible] torusAction radialSphere

def hopf (p : unitInterval × (Circle × Circle)) : Sphere := torusAction p.2 (radialSphere p.1)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def phaseChar (n : ℤ) (z : Circle) : ℂ := (z^n : Circle)

@[simp] lemma phaseChar_mul (n : ℤ) (z w : Circle) : phaseChar n (z*w)=phaseChar n z*phaseChar n w := by
  simp [phaseChar,mul_zpow]
@[simp] lemma phaseChar_zero (z : Circle) : phaseChar 0 z=1 := by simp [phaseChar]
@[simp] lemma phaseChar_one (n : ℤ) : phaseChar n 1=1 := by simp [phaseChar]
@[simp] lemma phaseChar_norm (n : ℤ) (z : Circle) : ‖phaseChar n z‖=1 := (z^n).norm_coe

def phaseSum (s : Finset ℤ) (a : ℤ → ℂ) (z : Circle) : ℂ := ∑ n ∈ s, a n*phaseChar n z

def PhaseBandwidth (W : Base → ℝ) (ℓ : ℕ) : Prop :=
  ∀ p : Sphere, ∃ s : Finset ℤ, ∃ a : ℤ → ℂ,
    (∀ n ∈ s, |n| ≤ (ℓ:ℤ)) ∧ ∀ z : Circle, (W ((z:ℂ) • (p:Base)):ℂ) = phaseSum s a z

def OrbitMeanOne (W : Base → ℝ) : Prop :=
  ∀ p : Sphere, (∫ z : Circle, W ((z:ℂ) • (p:Base)) ∂circleMeasure) = 1

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler11043_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def phaseBand (ℓ : ℕ) : Finset ℤ := Finset.Icc (-(ℓ:ℤ)) ℓ

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def leftCut (α δ y : ℝ) : ℝ := 1-Real.smoothTransition ((y-α)/δ)

def rightCut (α δ R y : ℝ) : ℝ :=
  Real.smoothTransition ((y-(α+2*δ))/δ) * (1-Real.smoothTransition ((y-R)/δ))

def profilePrimitive (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp y * ∫ v in 0..y, Real.exp (-v)*f v

structure RadialProfiles (a : ℝ) where
  s : ℝ
  F : ℝ
  R : ℝ
  cutoff : ℝ
  f : ℝ → ℝ
  b : ℝ → ℝ
  s_pos : 0 < s
  s_lt : s < 1
  F_nonneg : 0 ≤ F
  F_lt : F < 1
  R_pos : 0 < R
  cutoff_pos : 0 < cutoff
  cutoff_lt : cutoff < R
  smooth_f : ContDiff ℝ ∞ f
  smooth_b : ContDiff ℝ ∞ b
  small : ∀ y, 0 ≤ y → |f y| ≤ F
  plateau : ∀ y ∈ Icc 0 (Real.log a), f y = -s
  cancellation : ∫ y in Ioi 0, Real.exp (-y)*f y = 0
  ode : ∀ y, HasDerivAt b (b y+f y) y
  b_zero : b 0 = 0
  tail : ∀ y, cutoff ≤ y → f y = 0 ∧ b y = 0
  negativity : (Real.log a)^2-2*s*(Real.cosh (Real.log a)-1) < 0

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityDefinitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def phaseDerivative (W : Base → ℝ) (z : Base) : ℝ := fderiv ℝ W z (Complex.I • z)

def centralPoint (p : Sphere) (z : Base) : Base :=
  (bracket z (p:Base) / (‖bracket z (p:Base)‖:ℂ)) • (p:Base)

def densityHeight (k : ℕ) (p : Sphere) (z : Base) : ℝ :=
  -(k:ℝ)*Real.log ‖bracket z (p:Base)‖

def densityCorrectionRaw (k : ℕ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (z : Base) : ℝ :=
  let c := bracket z (p:Base)
  let phase := c/(‖c‖:ℂ)
  let y := densityHeight k p z
  (‖c‖^2)⁻¹ * (f y * W (centralPoint p z) * (phase^k).re -
    b y / k * phaseDerivative W (centralPoint p z) * (phase^k).im)

def densityCorrection (k : ℕ) (R : ℝ) (f b : ℝ → ℝ) (W : Base → ℝ) (p : Sphere) (z : Base) : ℝ :=
  if Real.exp (-R/k) < ‖bracket z (p:Base)‖ then densityCorrectionRaw k f b W p z else 0

def density (Q : ℕ) (R : ℝ) (f b : ℝ → ℝ) (P : ℕ → Finset Sphere) : ℕ → Base → ℝ
  | 0 => fun _ => 1
  | j+1 => fun z => density Q R f b P j z +
      ∑ p ∈ P (Q^(j+1)), densityCorrection (Q^(j+1)) R f b (density Q R f b P j) p z

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseWeightedDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler11626_1 uKahler11629_1 uKahler11634_1 uKahler11642_1 uKahler11661_1 uKahler11675_1 uKahler11691_1 uKahler11701_1 uKahler11718_1 uKahler11754_1 uKahler11763_1 uKahler11780_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def expSum {ι : Type uKahler11626_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i ∈ s, a i * Complex.exp (Complex.I*(w i:ℂ)*z)

def dampedSum {ι : Type uKahler11634_1} (s : Finset ι) (a : ι → ℂ) (w : ι → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (∑ i ∈ s, a i * Complex.exp (-((2:ℝ)+w i:ℝ)*z))/(1+z)^N

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

@[simp] lemma bracket_smul (c : ℂ) (z p : Base) : bracket (c • z) p = c*bracket z p := by
  simp [bracket]

lemma centralPoint_norm (p : Sphere) {ξ : Base} (hξ : bracket ξ (p:Base) ≠ 0) :
    ‖centralPoint p ξ‖=1 := by
  simp [centralPoint,norm_smul,Complex.norm_real,div_self (norm_ne_zero_iff.mpr hξ)]

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityBandwidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def densityBandwidth (Q : ℕ) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, Q^(i+1)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePhaseAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def phaseAction (z : Circle) (ξ : Sphere) : Sphere := sphereAction (phaseIsometry z z.norm_coe) ξ

@[simp] lemma phaseAction_coe (z : Circle) (ξ : Sphere) : (phaseAction z ξ : Base)=(z:ℂ) • (ξ:Base) := rfl

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def logFactor (q ε : ℝ) : ℝ :=
  (1+q^2+ε^2+Real.sqrt ((1+q^2+ε^2)^2-4*q^2))/2

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseLogApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def logMean (ε : ℝ) (v : ℂ) : ℝ := Real.log (logFactor ‖v‖ ε)-Real.log (1+ε^2)
def logNormalized (ε : ℝ) (v : ℂ) : ℂ := v/(logFactor ‖v‖ ε:ℂ)
def logTerm (ε : ℝ) (n : ℕ) (v : ℂ) : ℝ := -2*((logNormalized ε v)^(n+1)).re/(n+1)
def logTruncation (ε : ℝ) (M : ℕ) (v : ℂ) : ℝ := logMean ε v+∑ n ∈ Finset.range M, logTerm ε n v

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseAdaptedHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def adaptedHopf (p : Sphere) (t : unitInterval) (z : Circle × Circle) : Sphere :=
  sphereAction (adaptedIsometry p).symm (hopf (t,z))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCorrectionMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def adaptedMonomial (p : Sphere) (n m : ℕ) (ξ : Base) : ℂ :=
  (adaptedIsometry p ξ 0)^n*(adaptedIsometry p ξ 1)^m

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePolynomialChange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def linearSubstitution (U : Base →ₗ[ℂ] Base) (i : Fin 2) : MvPolynomial (Fin 2) ℂ :=
  ∑ j : Fin 2, MvPolynomial.C (U (EuclideanSpace.single j 1) i)*MvPolynomial.X j

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler13116_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal
namespace PinchedHartogs.BaseConstruction

def densityMeasure (W : Base → ℝ) : Measure Sphere := sigma.withDensity (fun ξ : Sphere => ENNReal.ofReal (W ξ))

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def peakPatch (k : ℕ) (R : ℝ) (p : Sphere) : Set Sphere :=
  {ξ | Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖}

def patchHeight (k : ℕ) (p : Sphere) (z : Base) : ℝ := -(k:ℝ)*Real.log ‖bracket z (p:Base)‖

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHorizontalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff ENNReal
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def Horizontal (ξ : Sphere) (v : Base) : Prop := bracket v (ξ:Base)=0

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseHorizontalArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def horizontalArc (q d : Base) (t : ℝ) : Base :=
  (Real.sqrt (1+t^2*‖d‖^2))⁻¹ • (q+t • d)

def horizontalArcVelocity (q d : Base) (t : ℝ) : Base :=
  (-(t*‖d‖^2)/(Real.sqrt (1+t^2*‖d‖^2))^3) • (q+t • d)+
    (Real.sqrt (1+t^2*‖d‖^2))⁻¹ • d

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCentralComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def HorizontalBound (W : Base → ℝ) (H : ℝ) : Prop :=
  ∀ ξ : Sphere, ∀ v : Base, Horizontal ξ v →
    |fderiv ℝ W ξ v| ≤ H*‖v‖*W ξ

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCorrectionEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def correctionModel (k : ℝ) (f b : ℝ → ℝ) (y S T : ℝ) (z : ℂ) : ℝ :=
  Real.exp (2*y/k)*(f y*S*z.re - b y/k*T*z.im)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityPatchEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def centralSphere (p ξ : Sphere) (hξ : bracket (ξ:Base) (p:Base) ≠ 0) : Sphere :=
  ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityStepSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def phaseSphere (z : Circle) (ξ : Sphere) : Sphere :=
  ⟨(z:ℂ) • (ξ:Base),by simp only [Metric.mem_sphere,dist_zero_right,norm_smul,z.norm_coe,sphere_norm,one_mul]⟩

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseDensityInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

structure DensityStage (W : ℕ → Base → ℝ) (Q : ℕ) (c K : ℝ) (j : ℕ) : Prop where
  positive : ∀ ξ : Sphere, 0 < W j ξ
  horizontal : HorizontalBound (W j) (K*Real.sqrt ((Q:ℝ)^j))
  phase : ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ K*(Q:ℝ)^j*W j ξ
  step : ∀ i, j=i+1 → ∀ ξ : Sphere, c*W i ξ ≤ W j ξ ∧ W j ξ ≤ 2*W i ξ

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadialPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def bracketUnit (p ξ : Sphere) : unitInterval := radialUnit (sphereAction (adaptedIsometry p) ξ)

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseModelSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def modelIntegrand (a ε ρ : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)-
    f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε

def modelMean (a ε ρ R : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ y in 0..R, modelIntegrand a ε ρ f y

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseModelParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def modelGap (a : ℝ) (p : RadialProfiles a) : ℝ := 2*p.s*(Real.cosh (Real.log a)-1)-(Real.log a)^2

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatchModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def radialPatchModel (a ε ρ : ℝ) (k : ℕ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (-2*y/k)*(Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2))-
    f y*(a*ρ*Real.exp (-y))/logFactor (a*ρ*Real.exp (-y)) ε

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BasePatchDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def peakPatchUnion (P : Finset Sphere) (k : ℕ) (R : ℝ) : Set Sphere := ⋃ p ∈ P, peakPatch k R p

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseTestSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

structure TestSystem where
  a : ℝ
  ε : ℝ
  η : ℝ
  d : ℝ
  D : ℝ
  Q : ℕ
  P : ℕ → Finset Sphere
  pr : RadialProfiles a
  a_pos : 0 < a
  eps_pos : 0 < ε
  eta_pos : 0 < η
  eta_lt : η < 1/2
  d_pos : 0 < d
  D_ge : 1 ≤ D
  Q_ge : 2 ≤ Q
  separated : ∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))
  positive : ∀ N (ξ : Sphere), 0 ≤ density Q pr.R pr.f pr.b P N ξ
  probability : ∀ N, IsProbabilityMeasure (densityMeasure (density Q pr.R pr.f pr.b P N))
  representing : ∀ N, Represents (densityMeasure (density Q pr.R pr.f pr.b P N))
  negative : ∀ N j, j+1 ≤ N → ∀ r ∈ Icc (0:ℝ) 1, 1-η ≤ r^(Q^(j+1)) →
    (∫ ξ : Sphere, logarithmicTest a ε (P (Q^(j+1))) (Q^(j+1)) ((r:ℂ) • (ξ:Base))
      ∂densityMeasure (density Q pr.R pr.f pr.b P N)) ≤ -d

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.BaseRadii
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def testRadius (Q : ℕ) (η : ℝ) (N : ℕ) : ℝ := 1-η/(Q:ℝ)^N

end PinchedHartogs.BaseConstruction

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsCompletenessSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler16710_1

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace CompactODE

variable {E : Type uKahler16710_1} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def CurveOn (V : E → E) (S : Set E) (γ : ℝ → E) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, HasDerivAt γ (V (γ t)) t ∧ γ t ∈ S

end CompactODE

end

end OAI
end

section
-- module Solutions.OAIQW_PinchedHartogs.HartogsTopologySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs
lemma scaled_fibre_lt (s : ℝ) (w : ℂ)
    (hw : Real.exp s * ‖w‖ ^ 2 < 1) : ‖Real.exp (s / 2) • w‖ < 1 := by
  have hsq := exp_half_sq s
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith only [hw, hsq, norm_nonneg w, Real.exp_pos (s / 2)]

lemma unscaled_fibre_lt (s : ℝ) (w : ℂ) (hw : ‖w‖ < 1) :
    Real.exp s * ‖Real.exp (-(s / 2)) • w‖ ^ 2 < 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have hs : Real.exp s * Real.exp (-(s / 2)) ^ 2 = 1 := by
    rw [pow_two, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1; congr 1; ring
  rw [← mul_assoc, hs, one_mul]
  nlinarith only [hw, norm_nonneg w]

def hartogsHomeomorph (φ : Base → ℝ) (hφ : ContinuousOn φ ball) :
    hartogs φ ≃ₜ ball × Metric.ball (0 : ℂ) 1 where
  toFun p := (⟨p.1.1, p.2.1⟩,
    ⟨Real.exp (φ p.1.1 / 2) • p.1.2, by
      simpa using scaled_fibre_lt (φ p.1.1) p.1.2 p.2.2⟩)
  invFun p := ⟨(p.1.1, Real.exp (-(φ p.1.1 / 2)) • p.2.1),
    p.1.2, unscaled_fibre_lt (φ p.1.1) p.2.1 (by simpa only [Metric.mem_ball, dist_zero_right] using p.2.2)⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp only [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  continuous_toFun := by
    have hb : Continuous (fun p : hartogs φ ↦ (⟨p.1.1, p.2.1⟩ : ball)) :=
      continuous_subtype_val.fst.subtype_mk _
    have hp : Continuous (fun p : hartogs φ ↦ φ p.1.1) := (continuousOn_iff_continuous_domRestrict.mp hφ).comp hb
    exact hb.prodMk (((hp.div_const 2).rexp.smul continuous_subtype_val.snd).subtype_mk _)
  continuous_invFun := by
    have hp : Continuous (fun p : ball × Metric.ball (0 : ℂ) 1 ↦ φ p.1.1) :=
      (continuousOn_iff_continuous_domRestrict.mp hφ).comp continuous_fst
    exact ((continuous_subtype_val.comp continuous_fst).prodMk
      (((hp.div_const 2).neg.rexp).smul (continuous_subtype_val.comp continuous_snd))).subtype_mk _

end PinchedHartogs

end

end OAI
end


