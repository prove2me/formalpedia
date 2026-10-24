-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
-- name    : KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:31:16.315204+00:00
-- url     : https://prove2.me/theorems/beda8b82-1ea5-4b9a-8878-72b53f283102
-- title:
--   Construction of a Borell density from ball ratios
-- statement:
--   `BorellRepresentation.radius` uses the sequence $r_n=1/(n+1)$, while `ballRatio` is the closed-ball mass ratio $\nu(\overline B(x,r_n))/m(\overline B(0,r_n))$ and `lowerDensity` is its $\liminf$ along n. `envelope` is the infimum over neighborhoods of the corresponding suprema of `lowerDensity`; it is upper semicontinuous, log-concave under the stated hypotheses, and agrees almost everywhere with the lower density when that density is uniformly bounded. Under compact-set log-concavity, nonempty interior support, and absolute continuity with respect to an additive Haar measure, `LogConcave.exists_isBorellDensity_of_interior_support_nonempty` produces a real Borell density representative.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Construction.lean#L23-L383 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Construction`, definition bundle `KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Moments
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Averages
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Domination_Ball
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set Topology Filter
namespace FunctionalInequalities
section Construction
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V]
namespace KLS
namespace BorellRepresentation
/-- The radii `1/(n+1)` along which ball ratios are read. -/
def radius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
/-- The radii are positive. -/
theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity
/-- The radii tend to zero from the right. -/
theorem tendsto_radius : Tendsto radius atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n ↦ Set.mem_Ioi.mpr (radius_pos n)⟩
/-- Some radius lies below any positive threshold. -/
theorem exists_radius_lt {ε : ℝ} (hε : 0 < ε) : ∃ n, radius n < ε := exists_nat_one_div_lt hε
/-- Halving a radius stays in the sequence: `radius (2n+1) = radius n / 2`. -/
theorem radius_two_mul_add_one (n : ℕ) : radius (2 * n + 1) = radius n / 2 := by
  unfold radius
  push_cast
  field_simp
  ring
variable (ν m : Measure V)
/-- Mass of the closed ball around `x` of radius `radius n` divided by the Haar mass of the
ball of the same radius. -/
def ballRatio (n : ℕ) (x : V) : ENNReal :=
  ν (Metric.closedBall x (radius n)) / m (Metric.closedBall (0 : V) (radius n))
/-- The lower density along the sequence of radii. It is log-concave and equals the
Radon--Nikodym derivative almost everywhere. -/
def lowerDensity (x : V) : ENNReal := liminf (fun n ↦ ballRatio ν m n x) atTop
/-- The upper semicontinuous envelope of the lower density. -/
def envelope (x : V) : ENNReal :=
  ⨅ n : ℕ, ⨆ y ∈ Metric.ball x (radius n), lowerDensity ν m y
/-- Positive real powers commute with suprema in `ENNReal`. -/
 theorem rpow_iSup {I : Sort*} (f : I → ENNReal) {t : ℝ} (ht : 0 < t) :
    (⨆ i, f i) ^ t = ⨆ i, f i ^ t :=
  (ENNReal.orderIsoRpow t ht).map_iSup f
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- A uniform eventual small-ball bound bounds the lower density everywhere. -/
theorem lowerDensity_le (C : ENNReal)
    (hC : ∀ x, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ C * m (Metric.closedBall (0 : V) r)) (x : V) :
    lowerDensity ν m x ≤ C := by
  refine liminf_le_of_frequently_le' ((tendsto_radius.eventually (hC x)).mono ?_).frequently
  intro n hn
  exact ENNReal.div_le_of_le_mul hn
/-- Besicovitch differentiation: the lower density is the Radon--Nikodym derivative almost
everywhere with respect to the Haar reference measure. -/
theorem lowerDensity_ae_eq [IsFiniteMeasure ν] [m.IsAddHaarMeasure] :
    lowerDensity ν m =ᵐ[m] ν.rnDeriv m := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ν m] with x hx
  have hx' : Tendsto (fun n ↦ ballRatio ν m n x) atTop (𝓝 (ν.rnDeriv m x)) := by
    refine (hx.comp tendsto_radius).congr fun n ↦ ?_
    simp only [Function.comp, ballRatio, Measure.addHaar_closedBall_center m x]
  exact hx'.liminf_eq
omit [BorelSpace V] [SecondCountableTopology V] in
/-- Equal-radius ball ratios inherit the log-concavity inequality of the law. -/
theorem ballRatio_logConcave {ν : ProbabilityMeasure V} (hlc : LogConcave ν) [m.IsAddHaarMeasure]
    (n : ℕ) (x y : V) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ballRatio ν m n x ^ t * ballRatio ν m n y ^ (1 - t) ≤
      ballRatio ν m n (t • x + (1 - t) • y) := by
  set D := m (Metric.closedBall (0 : V) (radius n)) with hD_def
  have hD0 : D ≠ 0 := (Metric.measure_closedBall_pos m _ (radius_pos n)).ne'
  have hDt : D ≠ ⊤ := measure_closedBall_lt_top.ne
  have ht1' : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
  have key := hlc.closedBall_mul_le x y (radius n) t ht ht1
  have hDt0 : D ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hD0) hDt).ne'
  have hDt1 : D ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hD0) hDt).ne'
  have hDtt : D ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht.le hDt
  have hDtt1 : D ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht1' hDt
  have hD : D ^ t * D ^ (1 - t) = D := by
    rw [← ENNReal.rpow_add _ _ hD0 hDt]; simp
  unfold ballRatio
  rw [ENNReal.div_rpow_of_nonneg _ _ ht.le, ENNReal.div_rpow_of_nonneg _ _ ht1']
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  calc (ν : Measure V) (Metric.closedBall x (radius n)) ^ t * (D ^ t)⁻¹ *
        ((ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t) * (D ^ (1 - t))⁻¹)
      = ((ν : Measure V) (Metric.closedBall x (radius n)) ^ t *
          (ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t)) *
          ((D ^ t)⁻¹ * (D ^ (1 - t))⁻¹) := by ring
    _ = ((ν : Measure V) (Metric.closedBall x (radius n)) ^ t *
          (ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t)) *
          (D ^ t * D ^ (1 - t))⁻¹ := by
        rw [ENNReal.mul_inv (Or.inl hDt0) (Or.inl hDtt)]
    _ = ((ν : Measure V) (Metric.closedBall x (radius n)) ^ t *
          (ν : Measure V) (Metric.closedBall y (radius n)) ^ (1 - t)) * D⁻¹ := by rw [hD]
    _ ≤ (ν : Measure V) (Metric.closedBall (t • x + (1 - t) • y) (radius n)) * D⁻¹ :=
        mul_le_mul' key le_rfl
omit [BorelSpace V] [SecondCountableTopology V] in
/-- The lower density of a log-concave law is log-concave. -/
theorem lowerDensity_logConcave {ν : ProbabilityMeasure V} (hlc : LogConcave ν)
    [m.IsAddHaarMeasure] (x y : V) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    lowerDensity ν m x ^ t * lowerDensity ν m y ^ (1 - t) ≤
      lowerDensity ν m (t • x + (1 - t) • y) := by
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  unfold lowerDensity
  simp only [liminf_eq_iSup_iInf_of_nat]
  rw [FunctionalInequalities.KLS.BorellRepresentation.rpow_iSup _ ht, FunctionalInequalities.KLS.BorellRepresentation.rpow_iSup _ ht1', ENNReal.iSup_mul]
  refine iSup_le fun i ↦ ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j ↦ ?_
  refine le_iSup_of_le (max i j) ?_
  refine le_iInf₂ fun k hk ↦ ?_
  calc (⨅ l ≥ i, ballRatio ν m l x) ^ t * (⨅ l ≥ j, ballRatio ν m l y) ^ (1 - t)
      ≤ ballRatio ν m k x ^ t * ballRatio ν m k y ^ (1 - t) :=
        mul_le_mul'
          (ENNReal.rpow_le_rpow (iInf₂_le k (le_trans (le_max_left i j) hk)) ht.le)
          (ENNReal.rpow_le_rpow (iInf₂_le k (le_trans (le_max_right i j) hk)) ht1'.le)
    _ ≤ _ := ballRatio_logConcave m hlc k x y ht ht1
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- The envelope dominates the lower density. -/
theorem le_envelope (x : V) : lowerDensity ν m x ≤ envelope ν m x :=
  le_iInf fun n ↦ le_iSup₂ (f := fun y (_ : y ∈ Metric.ball x (radius n)) ↦ lowerDensity ν m y)
    x (Metric.mem_ball_self (radius_pos n))
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- A uniform bound on the lower density bounds the envelope. -/
theorem envelope_le {C : ENNReal} (h : ∀ y, lowerDensity ν m y ≤ C) (x : V) :
    envelope ν m x ≤ C :=
  (iInf_le _ 0).trans (iSup₂_le fun y _ ↦ h y)
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- The envelope is upper semicontinuous. -/
theorem upperSemicontinuous_envelope : UpperSemicontinuous (envelope ν m) := by
  intro x c hc
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hc
  have hball : Metric.ball x (radius n / 2) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (by have := radius_pos n; positivity)
  filter_upwards [hball] with x' hx'
  calc envelope ν m x' ≤ ⨆ y ∈ Metric.ball x' (radius (2 * n + 1)), lowerDensity ν m y :=
        iInf_le _ _
    _ ≤ ⨆ y ∈ Metric.ball x (radius n), lowerDensity ν m y := by
        refine iSup₂_le fun y hy ↦ le_iSup₂_of_le y ?_ le_rfl
        rw [radius_two_mul_add_one] at hy
        rw [Metric.mem_ball] at hy hx' ⊢
        calc dist y x ≤ dist y x' + dist x' x := dist_triangle _ _ _
          _ < radius n / 2 + radius n / 2 := add_lt_add hy hx'
          _ = radius n := by ring
    _ < c := hn
omit [FiniteDimensional ℝ V] [BorelSpace V] [SecondCountableTopology V] in
/-- The envelope of a log-concave lower density is log-concave. -/
theorem envelope_logConcave
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      lowerDensity ν m x ^ t * lowerDensity ν m y ^ (1 - t) ≤
        lowerDensity ν m (t • x + (1 - t) • y))
    (x y : V) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    envelope ν m x ^ t * envelope ν m y ^ (1 - t) ≤ envelope ν m (t • x + (1 - t) • y) := by
  have ht1' : 0 < 1 - t := sub_pos.mpr ht1
  refine le_iInf fun n ↦ ?_
  calc envelope ν m x ^ t * envelope ν m y ^ (1 - t)
      ≤ (⨆ x' ∈ Metric.ball x (radius n), lowerDensity ν m x') ^ t *
          (⨆ y' ∈ Metric.ball y (radius n), lowerDensity ν m y') ^ (1 - t) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (iInf_le _ n) ht.le)
          (ENNReal.rpow_le_rpow (iInf_le _ n) ht1'.le)
    _ ≤ ⨆ z ∈ Metric.ball (t • x + (1 - t) • y) (radius n), lowerDensity ν m z := by
        rw [FunctionalInequalities.KLS.BorellRepresentation.rpow_iSup _ ht, FunctionalInequalities.KLS.BorellRepresentation.rpow_iSup _ ht1']
        simp only [FunctionalInequalities.KLS.BorellRepresentation.rpow_iSup _ ht, FunctionalInequalities.KLS.BorellRepresentation.rpow_iSup _ ht1', ENNReal.iSup_mul, ENNReal.mul_iSup]
        refine iSup₂_le fun y' hy' ↦ iSup₂_le fun x' hx' ↦ ?_
        refine le_iSup₂_of_le (t • x' + (1 - t) • y') ?_ (hψ x' y' t ht ht1)
        rw [Metric.mem_ball, dist_eq_norm] at hx' hy' ⊢
        have heq : t • x' + (1 - t) • y' - (t • x + (1 - t) • y) =
            t • (x' - x) + (1 - t) • (y' - y) := by simp only [smul_sub]; abel
        rw [heq]
        calc ‖t • (x' - x) + (1 - t) • (y' - y)‖
            ≤ ‖t • (x' - x)‖ + ‖(1 - t) • (y' - y)‖ := norm_add_le _ _
          _ = t * ‖x' - x‖ + (1 - t) * ‖y' - y‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht,
                abs_of_pos ht1']
          _ < t * radius n + (1 - t) * radius n :=
              add_lt_add (mul_lt_mul_of_pos_left hx' ht) (mul_lt_mul_of_pos_left hy' ht1')
          _ = radius n := by ring
omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The positivity set of a finite log-concave `ENNReal` function is convex. -/
theorem convex_pos_of_logConcave {ψ : V → ENNReal} (hfin : ∀ x, ψ x ≠ ⊤)
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 → ψ x ^ t * ψ y ^ (1 - t) ≤ ψ (t • x + (1 - t) • y)) :
    Convex ℝ {x | 0 < ψ x} := by
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < ψ a := ha
  have hb' : 0 < ψ b := hb
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simpa using hb'
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simpa using ha'
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := hψ a b s hs' hs1
  rw [← hu_eq] at key
  show 0 < ψ (s • a + u • b)
  exact lt_of_lt_of_le
    (ENNReal.mul_pos (ENNReal.rpow_pos ha' (hfin a)).ne' (ENNReal.rpow_pos hb' (hfin b)).ne') key
omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- On the positivity set, the logarithm of the real part of a finite log-concave `ENNReal`
function is concave. -/
theorem concaveOn_log_toReal_of_logConcave {ψ : V → ENNReal} (hfin : ∀ x, ψ x ≠ ⊤)
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 → ψ x ^ t * ψ y ^ (1 - t) ≤ ψ (t • x + (1 - t) • y)) :
    ConcaveOn ℝ {x | 0 < ψ x} fun x ↦ Real.log (ψ x).toReal := by
  refine ⟨convex_pos_of_logConcave hfin hψ, ?_⟩
  intro a ha b hb s u hs hu hsu
  have ha' : 0 < (ψ a).toReal := ENNReal.toReal_pos (ne_of_gt ha) (hfin a)
  have hb' : 0 < (ψ b).toReal := ENNReal.toReal_pos (ne_of_gt hb) (hfin b)
  rcases hs.eq_or_lt with rfl | hs'
  · have hu1 : u = 1 := by linarith
    subst hu1
    simp
  rcases hu.eq_or_lt with rfl | hu'
  · have hs1 : s = 1 := by linarith
    subst hs1
    simp
  have hu_eq : u = 1 - s := by linarith
  have hs1 : s < 1 := by linarith
  have key := hψ a b s hs' hs1
  rw [← hu_eq] at key
  have key' : (ψ a).toReal ^ s * (ψ b).toReal ^ u ≤ (ψ (s • a + u • b)).toReal := by
    have := ENNReal.toReal_mono (hfin _) key
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
  simp only [smul_eq_mul]
  calc s * Real.log (ψ a).toReal + u * Real.log (ψ b).toReal
      = Real.log ((ψ a).toReal ^ s * (ψ b).toReal ^ u) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos ha' s).ne' (Real.rpow_pos_of_pos hb' u).ne',
          Real.log_rpow ha', Real.log_rpow hb']
    _ ≤ Real.log (ψ (s • a + u • b)).toReal :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos ha' s) (Real.rpow_pos_of_pos hb' u)) key'
omit [SecondCountableTopology V] in
/-- The envelope agrees with a bounded log-concave lower density off the Haar-null frontier of
the positivity set, hence almost everywhere. -/
theorem envelope_ae_eq [m.IsAddHaarMeasure] {C : ENNReal} (hC : C ≠ ⊤)
    (hle : ∀ x, lowerDensity ν m x ≤ C)
    (hψ : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      lowerDensity ν m x ^ t * lowerDensity ν m y ^ (1 - t) ≤
        lowerDensity ν m (t • x + (1 - t) • y)) :
    envelope ν m =ᵐ[m] lowerDensity ν m := by
  set ψ := lowerDensity ν m with hψ_def
  have hfin : ∀ x, ψ x ≠ ⊤ := fun x ↦ ((hle x).trans_lt hC.lt_top).ne
  set P : Set V := {x | 0 < ψ x} with hP_def
  have hPconv : Convex ℝ P := convex_pos_of_logConcave hfin hψ
  have hfront : m (frontier P) = 0 := hPconv.addHaar_frontier m
  -- continuity of the real part on the interior of `P`
  have hcont : ContinuousOn (fun x ↦ (ψ x).toReal) (interior P) := by
    have hlog := (concaveOn_log_toReal_of_logConcave hfin hψ).continuousOn_interior
    refine (Real.continuous_exp.comp_continuousOn hlog).congr ?_
    intro y hy
    have hyP : y ∈ P := interior_subset hy
    have hy' : 0 < ψ y := hyP
    simp [Function.comp, Real.exp_log (ENNReal.toReal_pos hy'.ne' (hfin y))]
  refine measure_mono_null ?_ hfront
  intro x hx
  by_contra hxf
  apply hx
  show envelope ν m x = ψ x
  by_cases hxc : x ∈ closure P
  · have hxi : x ∈ interior P := by
      by_contra hxi
      exact hxf ⟨hxc, hxi⟩
    refine le_antisymm ?_ (le_envelope ν m x)
    by_contra hlt
    push Not at hlt
    obtain ⟨c, hc1, hc2⟩ := exists_between hlt
    have hcC : c < C := lt_of_lt_of_le hc2 (envelope_le ν m hle x)
    have hcfin : c ≠ ⊤ := (lt_of_lt_of_le hcC le_top).ne
    have hxcont : ContinuousAt (fun x ↦ (ψ x).toReal) x :=
      hcont.continuousAt (isOpen_interior.mem_nhds hxi)
    have hlt' : (ψ x).toReal < c.toReal := (ENNReal.toReal_lt_toReal (hfin x) hcfin).mpr hc1
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hxcont.eventually (gt_mem_nhds hlt'))
    obtain ⟨n, hn⟩ := exists_radius_lt hε
    have hS : (⨆ y ∈ Metric.ball x (radius n), ψ y) ≤ c := by
      refine iSup₂_le fun y hy ↦ ?_
      have hy' : dist y x < ε := lt_trans (Metric.mem_ball.mp hy) hn
      exact ((ENNReal.toReal_lt_toReal (hfin y) hcfin).mp (hball hy')).le
    exact absurd ((iInf_le _ n).trans hS) (not_le.mpr hc2)
  · have hopen : IsOpen (closure P)ᶜ := isClosed_closure.isOpen_compl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hxc
    obtain ⟨n, hn⟩ := exists_radius_lt hε
    have hS : (⨆ y ∈ Metric.ball x (radius n), ψ y) = 0 := by
      refine le_antisymm (iSup₂_le fun y hy ↦ ?_) bot_le
      have hyc : y ∈ (closure P)ᶜ := hball (Metric.ball_subset_ball hn.le hy)
      have hyP : y ∉ P := fun h ↦ hyc (subset_closure h)
      exact not_lt.mp hyP
    have hx0 : ψ x = 0 :=
      le_antisymm (not_lt.mp fun h ↦ hxc (subset_closure h)) bot_le
    refine le_antisymm ?_ (le_envelope ν m x)
    rw [hx0]
    exact (iInf_le _ n).trans hS.le
end BorellRepresentation
end KLS
namespace KLS
namespace LogConcave
open BorellRepresentation in

/-- Existence of a Borell density representative for a compact-set log-concave probability law
with full-dimensional support, relative to any additive Haar measure. -/
theorem exists_isBorellDensity_of_interior_support_nonempty {ν : ProbabilityMeasure V}
    (hlc : LogConcave ν) (m : Measure V) [m.IsAddHaarMeasure]
    (hint : (interior (ν : Measure V).support).Nonempty) (hac : (ν : Measure V) ≪ m) :
    ∃ ρ : V → ℝ, IsBorellDensity (ν : Measure V) m ρ := by
  obtain ⟨C, hC⟩ := hlc.exists_eventually_closedBall_le m hint
  have hψC : ∀ x, lowerDensity (ν : Measure V) m x ≤ C := lowerDensity_le _ m C hC
  have hψlc : ∀ x y : V, ∀ t : ℝ, 0 < t → t < 1 →
      lowerDensity (ν : Measure V) m x ^ t * lowerDensity (ν : Measure V) m y ^ (1 - t) ≤
        lowerDensity (ν : Measure V) m (t • x + (1 - t) • y) :=
    fun x y t ht ht1 ↦ lowerDensity_logConcave m hlc x y ht ht1
  have hEC : ∀ x, envelope (ν : Measure V) m x ≤ C := envelope_le _ m hψC
  have hEfin : ∀ x, envelope (ν : Measure V) m x ≠ ⊤ :=
    fun x ↦ ((hEC x).trans_lt ENNReal.coe_lt_top).ne
  have hEusc : UpperSemicontinuous (envelope (ν : Measure V) m) := upperSemicontinuous_envelope _ m
  have hElc := envelope_logConcave (ν : Measure V) m hψlc
  have hEae : envelope (ν : Measure V) m =ᵐ[m] lowerDensity (ν : Measure V) m :=
    envelope_ae_eq _ m ENNReal.coe_ne_top hψC hψlc
  have hψae : lowerDensity (ν : Measure V) m =ᵐ[m] (ν : Measure V).rnDeriv m :=
    lowerDensity_ae_eq _ m
  refine ⟨fun x ↦ (envelope (ν : Measure V) m x).toReal, hEusc.measurable.ennreal_toReal,
    fun x ↦ ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · intro x c hc
    have hlt : envelope (ν : Measure V) m x < ENNReal.ofReal c :=
      (ENNReal.lt_ofReal_iff_toReal_lt (hEfin x)).mpr hc
    filter_upwards [hEusc x _ hlt] with y hy
    exact ENNReal.toReal_lt_of_lt_ofReal hy
  · intro x y t ht ht1
    have h := hElc x y ht ht1
    have := ENNReal.toReal_mono (hEfin _) h
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at this
  · calc m.withDensity (fun x ↦ ENNReal.ofReal (envelope (ν : Measure V) m x).toReal)
        = m.withDensity (envelope (ν : Measure V) m) := by
          congr 1; ext x; exact ENNReal.ofReal_toReal (hEfin x)
      _ = m.withDensity (lowerDensity (ν : Measure V) m) := withDensity_congr_ae hEae
      _ = m.withDensity ((ν : Measure V).rnDeriv m) := withDensity_congr_ae hψae
      _ = ν := Measure.withDensity_rnDeriv_eq _ _ hac
end LogConcave
end KLS
end Construction
end FunctionalInequalities


